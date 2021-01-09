use structopt::StructOpt;

mod parsing;
mod tests;

mod maybebool;
use maybebool::*;

mod var;
use var::*;

use itertools::Itertools;
pub use parsing::{
    str_to_clause,
    str_to_clauses,
    dimacs_to_clausules,
};

enum ProblemType {
    Unweighted(Vec<Clause>),
    Weighted(Vec<Clause>, Vec<usize>),
}

/// Clause can't aliasing ... x0 v x0 need to be minimized to x0
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Clause {
    literals: Vec<Var>,
}

#[derive(Debug, Clone)]
enum VarAssingable {
    Assingable(Var),
    Conflict,
    Nothing,
}

impl std::fmt::Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(")?;
        for lit in self.literals.iter().take(1) {
            write!(f, "{}", lit)?;
        }
        for lit in self.literals.iter().skip(1) {
            write!(f, " v {}", lit)?;
        }
        write!(f, ")")?;
        Ok(())
    }
}

impl Clause {
    fn new() -> Clause {
        Clause {
            literals: Vec::new(),
        }
    }
    fn assingable(&self, assigments: &[VarSource]) -> VarAssingable {
        let mut to_assign = None;
        let mut satisfied = false;
        //println!("{:?}", assigments);
        for var in &self.literals {
            //println!("{:?} {:?} {:?}", to_assign, var.sign, assigments[var.index].into_maybe_bool());
            match (to_assign, var.sign, assigments[var.index].into_maybe_bool()) {
                (_, true, MaybeBool(Some(true))) | (_, false, MaybeBool(Some(false))) => {
                    satisfied = true
                } // it is already satisfied
                (None, _, MaybeBool(None)) => to_assign = Some(var),
                (Some(_), _, MaybeBool(None)) => return VarAssingable::Nothing, // at least 2 vars are undefined
                (_, true, MaybeBool(Some(false))) | (_, false, MaybeBool(Some(true))) => (),
            }
        }
        /* //basic debug
        println!("assingable:");
        println!("{}", self);
        println!("{} {:?}", satisfied, to_assign);
        */
        match (satisfied, to_assign) {
            (false, Some(&to_assign)) => {
                VarAssingable::Assingable(to_assign)
            }
            (true, _) => VarAssingable::Nothing,
            (false, None) => VarAssingable::Conflict,
        }
    }

    fn empty() -> Clause {
        Clause {
            literals: Vec::new(),
        }
    }

    fn insert(&mut self, var: Var) {
        self.literals.push(var)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum VarSource {
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
enum TrailChoice {
    FirstChoice,
    SecondChoice,
}

#[derive(Debug, Clone, Copy)]
enum ReasonLock {
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
                    var
                } => {
                    write!(f, "\nchoose x{} = {}   {}.", var.index,
                        match var.sign {
                            true => "T",
                            false => "F",
                        },
                        match choice{
                            TrailChoice::FirstChoice => "1",
                            TrailChoice::SecondChoice => "2",
                        }
                    )?;
                },
                TrailState{
                    reason: ReasonLock::Deducted(source),
                    var
                } => {
                    write!(f, "   -> x{} = {} ({})",
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

#[derive(Debug)]
struct LearntClause{
    clause: usize,
    activity: f32,
}

#[derive(Debug, Clone)]
struct Watcher{
    for_true: Vec<usize>,
    for_false: Vec<usize>,
}

// this is where weighted SAT is implemented
trait SelectionHeuristics
    where Self: Sized,
          Self: std::fmt::Debug,
{
    fn new(nvars: usize) -> Self;
    fn select_variable(solver: &mut Solver<Self>) -> Var;
    // assigns and asks if continue
    fn assign(&mut self, var: Var, reason: ReasonLock) -> bool;
    fn deassign(&mut self, var: Var);
    // found solution and asks if final solution
    fn final_solution(&mut self, assigments: &[VarSource]) -> bool;
    fn solution(solver: &Solver<Self>) -> Vec<bool>;
}

#[derive(Debug)]
struct NaiveSelectionHeuristics{
    index: usize
}

impl SelectionHeuristics for NaiveSelectionHeuristics {
    fn new(_: usize) -> Self{
        NaiveSelectionHeuristics{
            index: 0,
        }
    }
    fn select_variable(solver: &mut Solver<Self>) -> Var{
        let mut index = solver.sel_heuristics.index;
        //fix first unassigned var
        while solver.assigments[index] != VarSource::Undef {
            index = (index + 1) % solver.assigments.len()
        }
        let assign = solver.watchers[index].for_true.len() <= solver.watchers[index].for_false.len();
        solver.sel_heuristics.index = index;
        Var{
            sign: assign,
            index: index,
        }
    }
    // assigns and asks if continue
    fn assign(&mut self, _: Var, _: ReasonLock) -> bool {
        true
    }
    fn deassign(&mut self, _: Var) {

    }
    // found solution and asks if final solution
    fn final_solution(&mut self, _: &[VarSource]) -> bool{
        true
    }
    fn solution(solver: &Solver<Self>) -> Vec<bool>{
        solver.assigments.iter().map(|x| x.into_bool()).collect()
    }
}

#[derive(Debug)]
struct Solver<SH>
    where SH : SelectionHeuristics,
          SH : std::fmt::Debug,
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
    where SH : SelectionHeuristics,
{
    fn init(clauses: Vec<Clause>) -> Result<Solver<SH>, ()> {
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
        let mut watchers = vec![Watcher{for_true:Vec::new(), for_false:Vec::new()}; nvars];
        let mut trail = Trail(Vec::new());
        let mut assigments = vec![VarSource::Undef; nvars];
        for (clause_id, clause) in (0..).zip(clauses.iter()) {
            match clause.literals[..] {
                [var] => {
                    //fix var
                    trail.0.push(TrailState{
                        var: var,
                        reason: ReasonLock::Fixed(TrailChoice::SecondChoice),
                    });
                    assigments[var.index] = VarSource::Fixed(var.sign, trail.0.len());
                },
                [] => (), //{return Err(())}, // empty-clause -> unsatisfable
                ref vars => {
                    //add watchers
                    for var in vars{
                        match var.sign{
                            true => watchers[var.index].for_false.push(clause_id),
                            false => watchers[var.index].for_true.push(clause_id),
                        }
                    }
                },
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
            sel_heuristics: SH::new(nvars),
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
            .take(self.given_len)
            .map(|clause| {
                clause
                    .literals
                    .iter()
                    .map(|lit| {
                        assigns[lit.index] ^ !lit.sign
                    })
                    .fold(false, |acc, x| acc | x)
            })
            .fold(true, |acc, x| acc & x)
    }

    /// unit propagation, Err is conflict (not propagated, just raw)
    fn propagate(&mut self, to_propagate: usize) -> Result<usize, Vec<usize>> {
        //println!("propagate: {}", to_propagate);
        let mut deducted = 0;
        match self.trail.0[to_propagate] {
            TrailState{
                var: Var{
                    index,
                    sign,
                },
                ..
            } => {
                let watches = match sign {
                    true => &self.watchers[index].for_true,
                    false => &self.watchers[index].for_false,
                };
                let mut conflicts = Vec::new();
                for w in watches {
                    if self.locked[*w] {continue}
                    match self.clauses[*w].assingable(&self.assigments[..]) {
                        VarAssingable::Assingable(var) => {
                            let reason = ReasonLock::Deducted(*w);
                            self.trail.0.push(TrailState{var, reason});
                            self.assigments[var.index] = VarSource::Deducted(var.sign, *w, self.level - 1);
                            self.locked[*w] = true;
                            self.sel_heuristics.assign(var, reason);
                            deducted += 1
                        },
                        VarAssingable::Conflict => conflicts.push(*w),
                        VarAssingable::Nothing => (),
                    }
                }
                if !conflicts.is_empty() {
                    return Err(conflicts)
                }
            }
        }
        Ok(deducted)
    }

    fn solve(&mut self) -> Result<Vec<bool>, ()> {
        let mut to_propagate = self.trail.0.len(); //assumptions that vars are assigned in their other
        self.level = self.level;
        let mut found_solution = false;
        loop {
            //satisfiable and assigned
            if self.trail.0.len() == self.assigments.len(){
                if self.sel_heuristics.final_solution(&self.assigments){
                    return Ok(SH::solution(self))
                } else {
                    found_solution = true;
                }
            }
            let var_to_fix = SH::select_variable(self);
            let reason = ReasonLock::Fixed(TrailChoice::FirstChoice);
            self.trail.0.push(TrailState{reason, var: var_to_fix});
            self.assigments[var_to_fix.index] = VarSource::Fixed(var_to_fix.sign, self.level);
            self.level += 1;
            self.sel_heuristics.assign(var_to_fix, reason);
            //propagate
            while to_propagate < self.trail.0.len() {
                match self.propagate(to_propagate) {
                    Ok(_) => to_propagate += 1,
                    Err(conflicts) => {
                        match self.resolve_conflicts(conflicts){
                            Err(()) => if found_solution {
                                return Ok(SH::solution(self))
                            } else {
                                return Err(())
                            }
                            _ => (),
                        };
                        to_propagate = self.trail.0.len()-1
                    }
                }
            }
        }
    }

    fn append_new_clause(&mut self, clause: Clause){
        let clause_id = self.clauses.len();
        match clause.literals[..] {
            [_] => panic!(),
            [] => panic!(), // empty-clause -> unsatisfable
            ref vars => {
                //add watchers
                for var in vars{
                    match var.sign{
                        true => self.watchers[var.index].for_false.push(clause_id),
                        false => self.watchers[var.index].for_true.push(clause_id),
                    }
                }
            },
        }
        self.clauses.push(clause);
        self.locked.push(false);
    }

    fn resolve_conflicts(&mut self, conflicts: Vec<usize>) -> Result<(), ()>{
        // learns new clausule from conflict

        // for each conflict find decision level and try to divide new clause

        let conflict_level = self.level-1; //assumes full propagate resolution
        // select higest implication level -> at least this need to be flipped (if not second choice)
        let implication_level = conflicts
            .iter()
            .map(|&conflict_id| &self.clauses[conflict_id])
            .map(|clause| {
                let mut skipped_conflict_level = false;
                clause.literals.iter().filter_map(|lit|{
                    let c_conflict_level = self.assigments[lit.index].into_conflict_level().unwrap();
                    if skipped_conflict_level {
                        Some(c_conflict_level)
                    } else if conflict_level == c_conflict_level{
                        skipped_conflict_level = true;
                        None
                    } else {
                        Some(c_conflict_level)
                    }
                }).max().unwrap_or(0)
            }
            ).min()
            .unwrap();

        //println!("==================\nconflicts {}:\n==================", conflicts.len());
        // on too much conflicts do not try even learn
        if conflicts.len() < 10 {
            for conflict_id in conflicts{
                let clause = &self.clauses[conflict_id];
                let mut new_clause = clause.clone();

                /*
                println!("{:?}", self.assigments);
                println!("{}", clause);
                println!("impl_lvl: {}, conflict_lvl: {}", implication_level, conflict_level);
                println!("level: {}", self.level);
                */


                if implication_level == 0 && match self.trail.0[0] {
                    TrailState{
                        reason: ReasonLock::Fixed(TrailChoice::SecondChoice),
                        ..
                    } => true,
                    _ => false,
                } {
                    return Err(());
                }

                // (!x1 ^ !x2 ) = > x3
                // change x3 to x1 v x2
                // if x3 is having level >= implication_level
                let mut raised = 0;
                let mut i = 0;
                let mut above_level = 0;
                while i < new_clause.literals.len(){
                    let index = new_clause.literals[i].index;
                    let assign = &self.assigments[index];
                    match assign {
                        VarSource::Deducted(_, source, level) if *level <= implication_level => {
                            self.clauses[*source].literals.iter().filter(|lit| lit.index != index).for_each(|lit| new_clause.literals.push(*lit));
                            new_clause.literals[i] = new_clause.literals.pop().unwrap();
                            raised += 1;
                        },
                        VarSource::Fixed(_, level) => {
                            if *level > implication_level {
                                above_level += 1;
                            }
                            i+=1
                        },
                        VarSource::Deducted(_, _, _) => {
                            above_level += 1;
                            i+=1
                        }
                        _ => i += 1,
                    }
                }

                // deduplication in clause
                new_clause.literals.sort_by(|a, b| a.index.cmp(&b.index));
                new_clause.literals = new_clause.literals.into_iter().dedup().collect();


                // how to decide if clause is good?
                if new_clause.literals.len() > 5 || raised < 2 || above_level < new_clause.literals.len()-3{
                    continue
                }

                self.append_new_clause(new_clause);
            }
        }

        //println!("{}", self.trail);
        //undo trail and switch most recent choice, which is possible
        while match self.trail.0.last().cloned() {
            // undo trail
            Some(TrailState{
                var,
                reason: ReasonLock::Deducted(source)
            }) if self.level > implication_level+1 => {
                self.sel_heuristics.deassign(var);
                self.trail.0.pop();
                self.assigments[var.index] = VarSource::Undef;
                self.locked[source] = false;
                true
            },
            Some(TrailState{
                var,
                reason: ReasonLock::Fixed(_)
            }) if self.level > implication_level+1 => {
                //println!("undo: {}", var);
                self.sel_heuristics.deassign(var);
                self.trail.0.pop();
                self.assigments[var.index] = VarSource::Undef;
                self.level -= 1;
                true
            },
            Some(TrailState{
                var,
                reason: ReasonLock::Deducted(source),
            }) => {
                self.sel_heuristics.deassign(var);
                self.trail.0.pop();
                self.assigments[var.index] = VarSource::Undef;
                self.locked[source] = false;
                true
            },

            //switch
            Some(TrailState{
                var,
                reason: ReasonLock::Fixed(TrailChoice::FirstChoice),
            }) => {
                //println!("switch: {}", !var);
                self.sel_heuristics.deassign(var);
                self.trail.0.pop();
                self.assigments[var.index] = VarSource::Fixed(!var.sign, self.level-1);
                let reason = ReasonLock::Fixed(TrailChoice::SecondChoice);
                self.trail.0.push(TrailState{var: !var, reason});
                self.sel_heuristics.assign(!var, reason);
                false
            }
            //exhausted option
            Some(TrailState{
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
        } {/*empty body*/}
        Ok(())
    }

    fn string_analyze_conflicts(&self) -> String {
        let mut st = "Conflicts:".to_string();
        for clause in &self.clauses{
            match clause.assingable(&self.assigments[..]) {
                VarAssingable::Conflict => {
                    st = format!("{}\n{}", st, clause)
                },
                _ => (),
            }
        }
        st
    }
}

fn main() {
    let opts = Opts::from_args();
    let clauses = dimacs_to_clausules(std::fs::read_to_string(opts.input_task).unwrap().as_str());
    let mut solver = Solver::<NaiveSelectionHeuristics>::init(clauses).unwrap();
    let assigns = solver.solve().unwrap();
    assert!(
        solver.test_satisfied(&assigns[..]) == true,
        format!("{:#?}\n{}\n{}\n{:?}", solver, solver.trail, solver.string_analyze_conflicts(), solver.test_satisfied(&assigns[..]))
    );
    //println!("{:#?}", solver);
}

#[derive(StructOpt, Debug)]
#[structopt(name = "sat-solver", author = "Martin Quarda <martin@quarda.cz>")]
pub struct Opts {
    input_task: String,
}