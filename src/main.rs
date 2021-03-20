use structopt::StructOpt;

mod parsing;
mod tests;

mod maybebool;
use maybebool::*;

mod var;
use var::*;

mod clause;
use clause::*;

mod heuristics;
use heuristics::*;

use itertools::Itertools;
pub use parsing::{dimacs_to_clausules, str_to_clause, str_to_clauses};

#[derive(Debug, PartialEq, Eq)]
pub enum ProblemType {
    Unweighted(Vec<Clause>),
    Weighted(Vec<Clause>, Vec<usize>),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum VarSource {
    Undef,
    //           v- level at what variable was fixed, zero means it must be assigned to value
    Fixed(bool, usize),
    // source clause -v      v- level at what variable was deducted, at worst it implied on this level
    Deducted(bool, usize, usize),
}

impl VarSource {
    fn into_maybe_bool(&self) -> MaybeBool {
        match self {
            VarSource::Fixed(state, _) | VarSource::Deducted(state, _, _) => (*state).into(),
            VarSource::Undef => MaybeBool::undef(),
        }
    }

    fn into_bool(&self) -> bool {
        match self {
            VarSource::Fixed(state, _) | VarSource::Deducted(state, _, _) => *state,
            VarSource::Undef => panic!(),
        }
    }

    fn into_conflict_level(&self) -> Option<usize> {
        match self {
            VarSource::Fixed(_, level) | VarSource::Deducted(_, _, level) => Some(*level),
            VarSource::Undef => None,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TrailChoice {
    FirstChoice,
    SecondChoice,
}

#[derive(Debug, Clone, Copy)]
pub enum ReasonLock {
    Fixed(TrailChoice),
    //         v- source clause
    Deducted(usize),
}

#[derive(Debug, Clone, Copy)]
struct TrailState {
    var: Var,
    reason: ReasonLock,
}

#[derive(Debug)]
struct Trail(Vec<TrailState>);

impl std::fmt::Display for Trail {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "-- Decision tree ------------------------")?;
        for decision in &self.0 {
            match decision {
                TrailState {
                    reason: ReasonLock::Fixed(choice),
                    var,
                } => {
                    write!(
                        f,
                        "\nchoose x{} = {}   {}.",
                        var.index,
                        match var.sign {
                            true => "T",
                            false => "F",
                        },
                        match choice {
                            TrailChoice::FirstChoice => "1",
                            TrailChoice::SecondChoice => "2",
                        }
                    )?;
                }
                TrailState {
                    reason: ReasonLock::Deducted(source),
                    var,
                } => {
                    write!(
                        f,
                        "   -> x{} = {} ({})",
                        var.index,
                        match var.sign {
                            true => "T",
                            false => "F",
                        },
                        source
                    )?;
                }
            }
            writeln!(f, "")?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
struct Watcher {
    for_true: Vec<usize>,
    for_false: Vec<usize>,
}

#[derive(Debug)]
pub struct Solver<SH>
where
    SH: SelectionHeuristics,
{
    clauses: Vec<Clause>,
    given_len: usize, //clauses with index > are learnt clauses
    locked: Vec<bool>,
    trail: Trail,
    watchers: Vec<Watcher>,
    assigments: Vec<VarSource>,
    level: usize,
    sel_heuristics: SH,
}

impl<SH> Solver<SH>
where
    SH: SelectionHeuristics,
{
    fn init(clauses: Vec<Clause>, sel_heuristics: SH) -> Result<Solver<SH>, ()> {
        let mut sel_heuristics = sel_heuristics;
        let nvars = clauses
            .iter()
            .map(|clause| {
                clause
                    .literals
                    .iter()
                    .map(|lit| lit.index)
                    .max()
                    .unwrap_or(0)
            })
            .max()
            .unwrap_or(0)
            + 1;
        let mut watchers = vec![
            Watcher {
                for_true: Vec::new(),
                for_false: Vec::new()
            };
            nvars
        ];
        let mut trail = Trail(Vec::new());
        let mut assigments = vec![VarSource::Undef; nvars];
        for (clause_id, clause) in (0..).zip(clauses.iter()) {
            match clause.literals[..] {
                [var] => {
                    //fix var
                    let reason = ReasonLock::Fixed(TrailChoice::SecondChoice);
                    trail.0.push(TrailState { var: var, reason });
                    assigments[var.index] = VarSource::Fixed(var.sign, trail.0.len());
                    sel_heuristics.assign(var, reason);
                }
                [] => (), //{return Err(())}, // empty-clause -> unsatisfable
                ref vars => {
                    //add watchers
                    for var in vars {
                        match var.sign {
                            true => watchers[var.index].for_false.push(clause_id),
                            false => watchers[var.index].for_true.push(clause_id),
                        }
                    }
                }
            }
        }
        let given_len = clauses.len();
        let mut solver = Solver::<SH> {
            level: trail.0.len(),
            clauses,
            given_len,
            locked: vec![false; given_len],
            trail,
            assigments,
            watchers,
            sel_heuristics,
        };

        // try to propagate if something was fixed (free propagations)
        let mut to_propagate = solver.trail.0.len();
        while to_propagate < solver.trail.0.len() {
            solver.propagate(to_propagate).map_err(|_| ())?;
            to_propagate += 1;
        }
        Ok(solver)
    }

    /// check for tests
    fn test_satisfied(&self, assigns: &[bool]) -> bool {
        self.clauses
            .iter()
            .take(self.given_len) //skip learned
            .map(|clause| {
                clause
                    .literals
                    .iter()
                    .map(|lit| assigns[lit.index] ^ !lit.sign)
                    .fold(false, |acc, x| acc | x)
            })
            .fold(true, |acc, x| acc & x)
    }

    /// unit propagation, Err is conflict (not propagated, just raw)
    /// Ok(true) -> success and continue
    /// Ok(false) -> success, but heuristics returned abort
    fn propagate(&mut self, to_propagate: usize) -> Result<bool, Vec<usize>> {
        //println!("propagate: {}", to_propagate);
        match self.trail.0[to_propagate] {
            TrailState {
                var: Var { index, sign },
                ..
            } => {
                let watches = match sign {
                    true => &self.watchers[index].for_true,
                    false => &self.watchers[index].for_false,
                };
                let mut conflicts = Vec::new();
                for w in watches {
                    if self.locked[*w] {
                        continue;
                    }
                    match self.clauses[*w].assingable(&self.assigments[..]) {
                        VarAssingable::Assingable(var) => {
                            let reason = ReasonLock::Deducted(*w);
                            self.trail.0.push(TrailState { var, reason });
                            self.assigments[var.index] =
                                VarSource::Deducted(var.sign, *w, self.level - 1);
                            self.locked[*w] = true;
                            if !self.sel_heuristics.assign(var, reason) {
                                return Ok(false);
                            }
                        }
                        VarAssingable::Conflict => conflicts.push(*w),
                        VarAssingable::Nothing => (),
                    }
                }
                if !conflicts.is_empty() {
                    return Err(conflicts);
                }
            }
        }
        Ok(true)
    }

    fn solve(&mut self) -> Result<Vec<bool>, ()> {
        /*for (i, clause) in self.clauses.iter().enumerate(){
            println!("{}: {}", i, clause);
        }*/
        let mut to_propagate = self.trail.0.len(); //assumptions that vars are assigned in their other
        self.level = self.level;
        let mut found_solution = false;
        loop {
            //satisfiable and assigned
            if self.trail.0.len() == self.assigments.len() {
                if self.sel_heuristics.final_solution(&self.assigments) {
                    return Ok(SH::solution(self));
                } else {
                    found_solution = true;
                    match self.switch_at_least_level(/*std::usize::MAX - 1*/) {
                        Err(()) => {
                            if found_solution {
                                return Ok(SH::solution(self));
                            } else {
                                return Err(());
                            }
                        }
                        Ok(()) => to_propagate = self.trail.0.len() - 1,
                    }
                }
            }
            //fixing variable
            if to_propagate == self.trail.0.len() {
                let var_to_fix = SH::select_variable(self);
                let reason = ReasonLock::Fixed(TrailChoice::FirstChoice);
                self.trail.0.push(TrailState {
                    reason,
                    var: var_to_fix,
                });
                self.assigments[var_to_fix.index] = VarSource::Fixed(var_to_fix.sign, self.level);
                self.level += 1;
                if !self.sel_heuristics.assign(var_to_fix, reason) {
                    match self.switch_at_least_level(/*std::usize::MAX - 1*/) {
                        Err(()) => {
                            if found_solution {
                                return Ok(SH::solution(self));
                            } else {
                                return Err(());
                            }
                        }
                        Ok(()) => to_propagate = self.trail.0.len() - 1,
                    }
                }
            }
            //propagate
            while to_propagate < self.trail.0.len() {
                match self.propagate(to_propagate) {
                    Ok(true) => to_propagate += 1,
                    Ok(false) => {
                        match self.switch_at_least_level(/*std::usize::MAX - 1*/) {
                            Err(()) => {
                                if found_solution {
                                    return Ok(SH::solution(self));
                                } else {
                                    return Err(());
                                }
                            }
                            _ => (),
                        }
                        to_propagate = self.trail.0.len() - 1
                    }
                    Err(conflicts) => {
                        match self.resolve_conflicts(conflicts) {
                            Err(()) => {
                                if found_solution {
                                    return Ok(SH::solution(self));
                                } else {
                                    return Err(());
                                }
                            }
                            _ => (),
                        };
                        to_propagate = self.trail.0.len() - 1
                    }
                }
            }
        }
    }

    fn append_new_clause(&mut self, clause: Clause) {
        let clause_id = self.clauses.len();
        match clause.literals[..] {
            //[_] => panic!(), -- asi bych měl nějak ošetřit ...
            [] => panic!(), // empty-clause -> unsatisfable
            ref vars => {
                //add watchers
                for var in vars {
                    match var.sign {
                        true => self.watchers[var.index].for_false.push(clause_id),
                        false => self.watchers[var.index].for_true.push(clause_id),
                    }
                }
            }
        }
        self.clauses.push(clause);
        self.locked.push(false);
    }

    fn resolve_conflicts(&mut self, conflicts: Vec<usize>) -> Result<(), ()> {
        // learns new clausule from conflict

        // for each conflict find decision level and try to divide new clause

        let conflict_level = self.level - 1; //assumes full propagate resolution
                                             // select higest implication level -> at least this need to be flipped (if not second choice)

        // not as needed as I think it is (maybe cleanup?) and name is misleading
        let implication_level = conflicts
            .iter()
            .map(|&conflict_id| &self.clauses[conflict_id])
            .map(|clause| {
                let mut skipped_conflict_level = false;
                clause
                    .literals
                    .iter()
                    .filter_map(|lit| {
                        let c_conflict_level =
                            self.assigments[lit.index].into_conflict_level().unwrap();
                        if skipped_conflict_level {
                            Some(c_conflict_level)
                        } else if conflict_level == c_conflict_level {
                            skipped_conflict_level = true;
                            None
                        } else {
                            Some(c_conflict_level)
                        }
                    })
                    .max()
                    .unwrap_or(0)
            })
            .min()
            .unwrap();

        //println!("==================\nconflicts {}:\n==================", conflicts.len());
        // on too much conflicts do not try even learn
        if conflicts.len() < 4 {
            for conflict_id in conflicts {
                let clause = &self.clauses[conflict_id];
                let mut new_clause = clause.clone();
                new_clause
                    .literals
                    .iter()
                    .for_each(|lit| self.sel_heuristics.appears_in_conflict(*lit));

                /*
                println!("{:?}", self.assigments);
                println!("{} {}", clause, conflict_id >= self.given_len);
                println!("impl_lvl: {}, conflict_lvl: {}", implication_level, conflict_level);
                println!("level: {}", self.level);
                */

                // (!x1 ^ !x2 ) = > x3
                // change x3 to x1 v x2
                // if x3 is having level >= implication_level
                let mut raised = 0;
                let mut i = 0;
                let mut above_level_or_fixed = 0;
                while i < new_clause.literals.len() && new_clause.literals.len() < 16 {
                    let index = new_clause.literals[i].index;
                    let assign = &self.assigments[index];
                    //println!("new_clause: {}, trying to rise: x{}", new_clause, index);
                    match assign {
                        VarSource::Deducted(_, source, level) if *level <= implication_level => {
                            self.clauses[*source]
                                .literals
                                .iter()
                                .filter(|lit| lit.index != index)
                                .for_each(|lit| new_clause.literals.push(*lit));
                            // replace resolved literal with last literal
                            new_clause.literals[i] = new_clause.literals.pop().unwrap();
                            raised += 1;
                            //println!("raising using {}", source);
                        }
                        VarSource::Fixed(_, _) => {
                            above_level_or_fixed += 1;
                            i += 1
                        }
                        VarSource::Deducted(_, _, _) => {
                            above_level_or_fixed += 1;
                            i += 1
                        }
                        _ => i += 1,
                    }
                }

                // deduplication in clause
                new_clause.literals.sort_by(|a, b| a.index.cmp(&b.index));
                new_clause.literals = new_clause.literals.into_iter().dedup().collect();

                //println!("to learn: {}", new_clause);

                // how to decide if clause is good?
                if new_clause.literals.len() > 0
                    && (new_clause.literals.len() > 5
                        || raised < 1
                        || above_level_or_fixed + 2 < new_clause.literals.len())
                {
                    continue;
                }

                if new_clause.literals.len() == 1 {
                    let var = new_clause.literals[0];
                    self.trail.0.insert(
                        0,
                        TrailState {
                            var,
                            reason: ReasonLock::Fixed(TrailChoice::SecondChoice),
                        },
                    );
                    self.assigments[var.index] = VarSource::Fixed(var.sign, 0);
                } else {
                    //println!("learning: {}", new_clause);
                    self.append_new_clause(new_clause)
                }
            }
        }

        //println!("before: {}", self.trail);
        //undo trail and switch most recent choice, which is possible
        let rtn = self.switch_at_least_level(/*std::usize::MAX - 1*/);
        //println!("after: {}", self.trail);
        rtn
    }

    // TODO: level is probably useless for this implementation
    fn switch_at_least_level(&mut self /*, level: usize*/) -> Result<(), ()> {
        while match self.trail.0.last().cloned() {
            // undo trail
            /*Some(TrailState {
                var,
                reason: ReasonLock::Deducted(source),
            }) if self.level > level + 1 => {
                self.sel_heuristics.deassign(var);
                self.trail.0.pop();
                self.assigments[var.index] = VarSource::Undef;
                self.locked[source] = false;
                true
            }
            Some(TrailState {
                var,
                reason: ReasonLock::Fixed(_),
            }) if self.level > level + 1 => {
                //println!("undo: {}", var);
                self.sel_heuristics.deassign(var);
                self.trail.0.pop();
                self.assigments[var.index] = VarSource::Undef;
                self.level -= 1;
                true
            }*/
            Some(TrailState {
                var,
                reason: ReasonLock::Deducted(source),
            }) => {
                self.sel_heuristics.deassign(var);
                self.trail.0.pop();
                self.assigments[var.index] = VarSource::Undef;
                self.locked[source] = false;
                true
            }

            //switch
            Some(TrailState {
                var,
                reason: ReasonLock::Fixed(TrailChoice::FirstChoice),
            }) => {
                //println!("switch: {}", !var);
                self.sel_heuristics.deassign(var);
                let var = !var;
                self.trail.0.pop();
                self.assigments[var.index] = VarSource::Fixed(var.sign, self.level - 1);
                let reason = ReasonLock::Fixed(TrailChoice::SecondChoice);
                self.trail.0.push(TrailState { var: var, reason });
                // beaware of !
                !self.sel_heuristics.assign(var, reason)
            }

            //exhausted option
            Some(TrailState {
                var,
                reason: ReasonLock::Fixed(TrailChoice::SecondChoice),
            }) => {
                //println!("exhausted: {}", var);
                self.sel_heuristics.deassign(var);
                self.trail.0.pop();
                self.assigments[var.index] = VarSource::Undef;
                self.level -= 1;
                true
            }
            None => return Err(()), // exhausted choices
        } { /*empty body*/ }
        Ok(())
    }

    fn string_analyze_conflicts(&self) -> String {
        let mut st = "Conflicts:".to_string();
        for clause in &self.clauses {
            match clause.assingable(&self.assigments[..]) {
                VarAssingable::Conflict => st = format!("{}\n{}", st, clause),
                _ => (),
            }
        }
        st
    }
}

use std::time::Instant;

fn main() {
    let opts = Opts::from_args();
    let problem = dimacs_to_clausules(std::fs::read_to_string(opts.input_task).unwrap().as_str());
    let start = Instant::now();
    match problem {
        ProblemType::Unweighted(clauses) => {
            let heur = PrioritySelectionHeuristics::new(&clauses);
            let mut solver = Solver::init(clauses, heur).unwrap();
            let assigns = solver.solve().unwrap();
            assert!(
                solver.test_satisfied(&assigns[..]) == true,
                format!(
                    "{:#?}\n{}\n{}\n{:?}",
                    solver,
                    solver.trail,
                    solver.string_analyze_conflicts(),
                    solver.test_satisfied(&assigns[..])
                )
            );
            for (i, val) in assigns.iter().enumerate() {
                print!(
                    " {}",
                    if *val {
                        (i as isize) + 1
                    } else {
                        -(i as isize) - 1
                    }
                );
            }
            println!(" 0");
        }
        ProblemType::Weighted(mut clauses, weights) => {
            // reordering in such way, that negatives with high weights are concluded sooner
            clauses.sort_by(|a, b| {
                b.literals
                    .iter()
                    .map(|x| if !x.sign { weights[x.index] } else { 0 })
                    .sum::<usize>()
                    .cmp(
                        &a.literals
                            .iter()
                            .map(|x| if !x.sign { weights[x.index] } else { 0 })
                            .sum::<usize>(),
                    )
            });

            let heur = GreedyWeightSelectionHeuristics::new(weights, &clauses);
            let mut solver = Solver::init(clauses, heur).unwrap();
            let assigns = solver.solve().unwrap();
            // not free test, but have almost zero impact ...
            assert!(
                solver.test_satisfied(&assigns[..]) == true,
                format!(
                    "{:#?}\n{}\n{}\n{:?}",
                    solver,
                    solver.trail,
                    solver.string_analyze_conflicts(),
                    solver.test_satisfied(&assigns[..])
                )
            );
            print!("{}", solver.sel_heuristics.best_weight());
            for (i, val) in assigns.iter().enumerate() {
                print!(
                    " {}",
                    if *val {
                        (i as isize) + 1
                    } else {
                        -(i as isize) - 1
                    }
                );
            }
            println!(" 0");
        }
    }
    let duration = start.elapsed();
    println!("time: {:?}", duration);
    println!("{}", duration.as_secs_f64())
}

#[derive(StructOpt, Debug)]
#[structopt(name = "sat-solver", author = "Martin Quarda <martin@quarda.cz>")]
pub struct Opts {
    input_task: String,
}
