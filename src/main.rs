use structopt::StructOpt;

mod parsing;
mod tests;

use itertools::Itertools;
pub use parsing::{
    str_to_clause,
    str_to_clauses,
    dimacs_to_clausules,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Var {
    index: usize,
    sign: bool,
}

impl Var {
    fn new(index: usize, state: bool) -> Var {
        Var { index, sign: state }
    }
}

impl std::ops::Not for Var {
    type Output = Self;

    fn not(self) -> Self::Output {
        Var {
            index: self.index,
            sign: !self.sign,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MaybeBool(Option<bool>);

impl MaybeBool {
    fn undef() -> Self {
        MaybeBool(None)
    }

    fn truee() -> Self {
        MaybeBool(Some(true))
    }

    fn falsee() -> Self {
        MaybeBool(Some(false))
    }
}

impl std::convert::From<bool> for MaybeBool {
    fn from(b: bool) -> Self {
        MaybeBool(Some(b))
    }
}

/*impl Var {
    fn into_maybe_bool(self) -> MaybeBool {
        MaybeBool(Some(self.sign))
    }
    fn into_bool(self) -> bool {
        self.sign
    }
}*/

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.sign {
            write!(f, "~")?;
        }
        write!(f, "x{}", self.index)
    }
}

impl std::ops::BitAnd for MaybeBool {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self::Output {
        MaybeBool(match (self.0, rhs.0) {
            (Some(true), Some(true)) => Some(true),
            (Some(false), _) | (_, Some(false)) => Some(false),
            _ => None,
        })
    }
}

impl std::ops::BitOr for MaybeBool {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self::Output {
        MaybeBool(match (self.0, rhs.0) {
            (Some(false), Some(false)) => Some(false),
            (Some(true), _) | (_, Some(true)) => Some(true),
            _ => None,
        })
    }
}

impl std::ops::BitXor for MaybeBool {
    type Output = Self;
    fn bitxor(self, rhs: Self) -> Self::Output {
        MaybeBool(match (self.0, rhs.0) {
            (Some(true), Some(false)) | (Some(false), Some(true)) => Some(true),
            (Some(true), Some(true)) | (Some(false), Some(false)) => Some(false),
            (None, _) | (_, None) => None,
        })
    }
}

impl std::ops::Not for MaybeBool {
    type Output = Self;
    fn not(self) -> Self::Output {
        MaybeBool(match self.0 {
            Some(x) => Some(!x),
            None => None,
        })
    }
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

#[derive(Debug)]
struct Solver
{
    clauses: Vec<Clause>,
    given_len: usize, //clauses with index > are learnt clauses
    locked: Vec<bool>,
    trail: Trail,
    watchers: Vec<Watcher>,
    assigments: Vec<VarSource>,
    level: usize,
}

impl Solver
{
    fn init(clauses: Vec<Clause>) -> Result<Solver, ()> {
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
        let mut solver = Solver {
            level: trail.0.len(),
            clauses,
            given_len,
            locked: vec![false; given_len],
            trail,
            assigments,
            watchers,
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
    fn test_satisfied(&self) -> MaybeBool {
        self.clauses
            .iter()
            .take(self.given_len)
            .map(|clause| {
                clause
                    .literals
                    .iter()
                    .map(|lit| {
                        self.assigments[lit.index].into_maybe_bool()
                            ^ !MaybeBool(Some(lit.sign))
                    })
                    .fold(MaybeBool::falsee(), |acc, x| acc | x)
            })
            .fold(MaybeBool::truee(), |acc, x| acc & x)
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
                            self.trail.0.push(TrailState{
                                var: var,
                                reason: ReasonLock::Deducted(*w),
                            });
                            self.assigments[var.index] = VarSource::Deducted(var.sign, *w, self.level - 1);
                            self.locked[*w] = true;
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

    fn solve(&mut self) -> Result<(), ()> {
        let mut i = 0; //to be fixed
        let mut to_propagate = self.trail.0.len(); //assumptions that vars are assigned in their other
        self.level = self.level;
        loop {
            if self.trail.0.len() == self.assigments.len(){
                return Ok(())
            }
            //fix first unassigned var
            while self.assigments[i] != VarSource::Undef {
                i = (i + 1) % self.assigments.len()
            }
            let assign = self.watchers[i].for_true.len() <= self.watchers[i].for_false.len();
            self.trail.0.push(
                TrailState{
                    reason: ReasonLock::Fixed(TrailChoice::FirstChoice),
                    var: Var{
                        index: i,
                        // prefer choice with less watchers
                        sign: assign,
                    }
                }
            );
            self.assigments[i] = VarSource::Fixed(assign, self.level);
            self.level += 1;
            //propagate
            while to_propagate < self.trail.0.len() {
                match self.propagate(to_propagate) {
                    Ok(_) => to_propagate += 1,
                    Err(conflicts) => {
                        self.resolve_conflicts(conflicts)?;
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
        if conflicts.len() < 3 {
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
                self.trail.0.pop();
                self.assigments[var.index] = VarSource::Undef;
                self.level -= 1;
                true
            },
            Some(TrailState{
                var,
                reason: ReasonLock::Deducted(source),
            }) => {
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
                self.trail.0.pop();
                self.assigments[var.index] = VarSource::Fixed(!var.sign, self.level-1);
                self.trail.0.push(TrailState{
                    var: !var,
                    reason: ReasonLock::Fixed(TrailChoice::SecondChoice),
                });
                false
            }
            //exhausted option
            Some(TrailState{
                var,
                reason: ReasonLock::Fixed(TrailChoice::SecondChoice),
            }) => {
                //println!("exhausted: {}", var);
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
    let mut solver = Solver::init(clauses).unwrap();
    solver.solve().unwrap();
    assert!(
        solver.test_satisfied() == MaybeBool::truee(),
        format!("{:#?}\n{}\n{}\n{:?}", solver, solver.trail, solver.string_analyze_conflicts(), solver.test_satisfied())
    );
    //println!("{:#?}", solver);
}

#[derive(StructOpt, Debug)]
#[structopt(name = "sat-solver", author = "Martin Quarda <martin@quarda.cz>")]
pub struct Opts {
    input_task: String,
}