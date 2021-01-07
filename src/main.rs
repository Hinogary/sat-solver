mod parsing;
mod tests;

use itertools::Itertools;
use parsing::{str_to_clause, str_to_clauses, dimacs_to_clausules};

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
            sign: self.sign,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct MaybeBool(Option<bool>);

impl MaybeBool {
    fn into_inner(self) -> Option<bool> {
        self.0
    }

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

impl Var {
    fn into_maybe_bool(self) -> MaybeBool {
        MaybeBool(Some(self.sign))
    }
    fn into_bool(self) -> bool {
        self.sign
    }
}

impl std::fmt::Display for Var {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if !self.sign {
            write!(f, "~");
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

struct Conflicts(Vec<usize>);

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
    fn assingable(&self, assigments: &[MaybeBool]) -> VarAssingable {
        let mut to_assign = None;
        let mut satisfied = false;
        //println!("{:?}", assigments);
        for var in &self.literals {
            //println!("{:?} {:?} {:?}", to_assign, var.sign, assigments[var.index].into_maybe_bool());
            match (to_assign, var.sign, assigments[var.index]) {
                (_, true, MaybeBool(Some(true))) | (_, false, MaybeBool(Some(false))) => {
                    satisfied = true
                } // it is already satisfied
                (None, _, MaybeBool(None)) => to_assign = Some(var),
                (Some(_), _, MaybeBool(None)) => return VarAssingable::Nothing, // at least 2 vars are undefined
                (_, true, MaybeBool(Some(false))) | (_, false, MaybeBool(Some(true))) => (),
            }
        }
        //println!("{}", satisfied);
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

    fn is_empty(&self) -> bool {
        self.literals.is_empty()
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

use TrailChoice::*;

#[derive(Debug, Clone, Copy)]
struct TrailState {
    var: Var,
    reason: ReasonLock,
}

#[derive(Debug)]
struct Trail(Vec<TrailState>);

impl std::fmt::Display for Trail {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "-- Decision tree ------------------------");
        for decision in self.0 {
            match decision {
                TrailState {
                    reason: ReasonLock::Fixed(choice),
                    var
                } => {
                    write!(f, "\nx{} = {}   {}.  -->", var.index,
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
                    write!(f, "  x{} = {}", var.index,
                    match var.sign {
                        true => "T",
                        false => "F",
                    });
                }
            }
            writeln!(f, "");
        }
        Ok(())
    }
}

#[derive(Debug)]
struct LearntClause{
    clause: usize,
    activity: f32,
}

#[derive(Debug)]
enum ClauseType{
    Original(usize),
    Learnt(LearntClause),
}

impl ClauseType{
    fn into_innder(&self) -> usize {
        use ClauseType::*;
        match self {
            Original(index) => *index,
            Learnt(LearntClause{clause: clause, ..}) => *clause,
        }
    }
}

use std::collections::HashMap as HMap;

#[derive(Debug, Clone)]
struct Watcher{
    for_true: Vec<usize>,
    for_false: Vec<usize>,
}

#[derive(Debug)]
struct Solver
{
    clauses: Vec<Clause>,
    given_len: usize, //clauses with index >
    locked: Vec<bool>,
    trail: Trail,
    trail_lim: Vec<usize>,
    watchers: Vec<Watcher>,
    assigments: Vec<MaybeBool>,
    fixing_level: Vec<usize>,
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
        for (clause_id, clause) in (0..).zip(clauses) {
            match &clause.literals[..] {
                &[var] => {
                    //fix var
                    trail.0.push(TrailState{
                        var: var,
                        reason: ReasonLock::Fixed(TrailChoice::SecondChoice),
                    })
                },
                &[] => {return Err(())}, // empty-clause -> unsatisfable
                vars => {
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
        // TODO: simplify???
        Ok(Solver {
            clauses,
            given_len: clauses.len(),
            locked: vec![false; clauses.len()],
            trail,
            trail_lim: vec![0],
            assigments: vec![MaybeBool::undef(); nvars],
            watchers,
            fixing_level: vec![0, nvars],
        })
    }

    /// check for tests
    fn test_satisfied(&self) -> MaybeBool {
        self.clauses
            .iter()
            .map(|clause| {
                clause
                    .literals
                    .iter()
                    .map(|lit| {
                        self.assigments[lit.index]
                            ^ !MaybeBool(Some(lit.sign))
                    })
                    .fold(MaybeBool::falsee(), |acc, x| acc | x)
            })
            .fold(MaybeBool::truee(), |acc, x| acc & x)
    }

    /// unit propagation, Err is conflict (not propagated, just raw)
    fn propagate(&mut self, to_propagate: usize) -> Result<usize, Vec<usize>> {
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
                    true => self.watchers[index].for_true,
                    false => self.watchers[index].for_false,
                };
                let mut conflicts = Vec::new();
                for w in watches {
                    if self.locked[w] {continue}
                    match self.clauses[w].assingable(&self.assigments[..]) {
                        VarAssingable::Assingable(var) => {
                            self.trail.0.push(TrailState{
                                var: var,
                                reason: ReasonLock::Deducted(w),
                            });
                            deducted += 1
                        },
                        VarAssingable::Conflict => conflicts.push(w),
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
        let mut to_propagate = 0;
        loop {
            //fix something
            while self.assigments[i] != MaybeBool::undef() {
                i+=1;
            }
            self.trail.0.push(
                TrailState{
                    reason: ReasonLock::Fixed(TrailChoice::FirstChoice),
                    var: Var{
                        index: i,
                        sign: true,
                    }
                }
            );
            i+=1;
            //propagate
            while to_propagate < self.trail.0.len() {
                match self.propagate(to_propagate) {
                    Ok(x) => to_propagate += 1,
                    Err(conflicts) => {
                        self.resolve_conflicts(conflicts);
                        to_propagate = self.trail.0.len()
                    }
                }
            }
        }
    }

    fn resolve_conflicts(&mut self, conflicts: Vec<usize>){
        // probably learning should occur hear

        // for each conflict find decision level and try to divide new clause
        for conflict_id in conflicts{
            let clause = &self.clauses[conflict_id];
            let mut conflict_sources = Vec::new(); //probably just one
            let mut iterator = self.trail.0.iter().rev();
            // resolving conflict level
            for trailstate in iterator {
                match trailstate {
                    TrailState{
                        var,
                        ..
                    } => {
                        if clause.literals.iter().find(|&&x| x == !*var).is_some() {
                            conflict_sources.push(var)
                        }
                    }
                }
                match trailstate {
                    TrailState{
                        reason: ReasonLock::Fixed(_),
                        ..
                    } => break,
                }
            }
            let mut implied_sources = Vec::new();
            for trailstate in iterator {
                match trailstate {
                    TrailState{
                        var,
                        ..
                    } => {
                        if clause.literals.iter().find(|&&x| x == !*var).is_some() {
                            implied_sources.push(var)
                        }
                    }
                }
                match trailstate {
                    TrailState{
                        reason: ReasonLock::Fixed(_),
                        ..
                    } => if !implied_sources.is_empty() {
                        break
                    },
                }
            }




        }



    }

    /// Conflict is clause, where all Variables are assigned, but Clause forms Contradiction
    fn solve_conflict(&mut self, conflict: Conflict) -> Result<Option<Clause>, ()> {
        use std::cell::UnsafeCell;
        use std::collections::HashMap as Map;
        use std::collections::HashSet as Set;
        #[cfg(debug_assertions)]
        println!("conflicting {}", conflict.clause);

        debug_assert!(!conflict.clause.literals.is_empty());

        // Creating initial conflict plane and calculating risky levels conflict plane

        let mut conflict_plane = Map::new(); // var, is_on_edge?
        let mut last_level: Option<(usize, Var)> = None; // this is conflict level, that needs to be reverted
                                                         //                  v- implied_level (lowest level, which causes conflict)
                                                         // (x1 ^ x2 ^ x3 ^ x4) => x5
                                                         //                         ^ last_level
        let mut implied_level = None;
        for var in conflict.clause.literals {
            conflict_plane.insert(var, true);
            let level = self
                .searchstate
                .assigment(var.index)
                .into_conflict_level()
                .unwrap_or_else(|| panic!("{:?}", self.searchstate.assigment(var.index)));
            if level >= last_level.map(|x| x.0).unwrap_or(0) {
                implied_level = last_level;
                last_level = Some((level, var));
            }
        }

        let last_level = last_level.map(|(x, _)| x).unwrap();
        let implied_level = implied_level.map(|(x, _)| x).unwrap_or(0);

        // Move conflict plane upwards -> generate better clauses (not yet implemented)

        let conflict_plane: UnsafeCell<_> = conflict_plane.into();

        let mut new_clause_from_conflict = Clause::empty();
        let mut waiting_to_insert_into_cf = Set::new();
        let mut x = 0;
        loop {
            for (&k, v) in unsafe { &mut *conflict_plane.get() }
                .iter_mut()
                .filter(|(_, v)| **v)
            {
                *v = false;
                match &self.searchstate.assigment(k.index) {
                    VarSource::Undef => unreachable!(),
                    VarSource::Deducted(_, source, _) => {
                        for var in source {
                            // Keys can't alias, it will cause cyclic Clause
                            if unsafe { &*conflict_plane.get() }.get(&var) == None {
                                waiting_to_insert_into_cf.insert(k);
                            }
                        }
                    }
                    VarSource::Fixed(_, level) => {
                        new_clause_from_conflict.insert(if *level == last_level { k } else { !k })
                    }
                }
            }
            if waiting_to_insert_into_cf.is_empty() {
                break;
            }
            waiting_to_insert_into_cf.retain(|&key| {
                unsafe { &mut *conflict_plane.get() }.insert(key, true);
                false
            });
        }
        // TODO: generate clause from conflict plane and insert it

        // Undoes work up to implied_level, then change mind on var selection
        // last level -> delete
        // implication level -> change mind

        (implied_level..=self.searchstate.trail_len() - 2)
            .map(|_| self.searchstate.raise_level(&mut self.heuristics))
            .last();

        loop {
            match (self.searchstate.raise_level(&mut self.heuristics), self.searchstate.trail_len()) {
                (
                    TrailState {
                        choice: TrailChoice::SecondChoice,
                        ..
                    },
                    0,
                ) => return Err(()),
                (
                    TrailState {
                        choice: TrailChoice::FirstChoice,
                        var: Var { index, sign },
                    },
                    _,
                ) => {
                    self.searchstate.fix_level(TrailState{var: Var{index, sign: !(bool::from(sign))}, choice: SecondChoice});
                    break;
                }
                (
                    TrailState {
                        choice: TrailChoice::SecondChoice,
                        ..
                    },
                    _,
                ) => (),
            }
        }
        Ok(None)
    }
}

fn main() {
    let clauses = dimacs_to_clausules(std::fs::read_to_string("./tests/satisfable/uf20-01.cnf").unwrap().as_str());
    let mut solver = Solver::<NaiveHeuristics>::init(clauses).unwrap();
    assert!(Ok(()) == solver.solve());
    assert!(
        solver.test_satisfied() == MaybeBool::truee(),
        format!("{:?}, {:#?}", solver.test_satisfied(), solver)
    );
}
