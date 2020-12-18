mod parsing;
mod tests;

use itertools::Itertools;
use parsing::{str_to_clause, str_to_clauses};

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
    Assingable(Var, Vec<Var>),
    Conflict(Conflict), // new Clause to add
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
        //println!("{}", satisfied);
        match (satisfied, to_assign) {
            (false, Some(&to_assign)) => {
                VarAssingable::Assingable(to_assign, self.literals.iter().cloned().collect())
            }
            (true, _) => VarAssingable::Nothing,
            (false, None) => VarAssingable::Conflict(Conflict {
                clause: self.clone(),
            }),
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
    //                        v- level at what variable was deducted, at worst it implied on this level
    Deducted(bool, Vec<Var>, usize),
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

use TrailChoice::*;

#[derive(Debug, Clone, Copy)]
struct TrailState {
    var: Var,
    choice: TrailChoice,
}

trait Heuristics {
    fn select_variable(&mut self, searchstate: &SearchState) -> Var;
    fn deselect_variable(&mut self, var: Var);
}

#[derive(Debug, Default)]
struct NaiveHeuristics {
    last_selected: u32,
}

impl Heuristics for NaiveHeuristics {
    fn select_variable(&mut self, searchstate: &SearchState) -> Var {
        for (index, var) in (0..).zip(searchstate.assigments.iter()) {
            if *var == VarSource::Undef {
                return Var{index: index, sign: true};
            }
        }
        panic!()
    }
    fn deselect_variable(&mut self, var: Var) {}
}

impl std::fmt::Display for SearchState {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "-- Decision tree ------------------------");
        for (i, decision) in (0..).zip(self.trail.iter()) {
            match decision {
                TrailState {
                    choice: TrailChoice::FirstChoice,
                    ..
                } => write!(f, "   1.")?,
                TrailState {
                    choice: TrailChoice::SecondChoice,
                    ..
                } => write!(f, "   2.")?,
            }
            let decision = decision.var;
            write!(
                f,
                "  x{} = {}",
                decision.index,
                match decision.sign {
                    true => 'T',
                    false => 'F',
                }
            )?;
            if !self.deductions.is_empty() {
                write!(f, "  -->  ");
            }
            writeln!(
                f,
                "{}",
                self.deductions
                    .iter()
                    .filter(|(_, level)| *level == i)
                    .map(|(var, _)| {
                        format!(
                            "x{} = {}",
                            var.index,
                            match var.sign {
                                true => 'T',
                                false => 'F',
                            }
                        )
                    })
                    .join(", ")
            )?;
        }
        Ok(())
    }
}

#[derive(Debug)]
struct SearchState {
    trail: Vec<TrailState>,
    deductions: Vec<(Var, usize)>,
    assigments: Vec<VarSource>,
}

impl SearchState {
    fn new(nvars: usize) -> SearchState {
        SearchState {
            assigments: vec![VarSource::Undef; nvars],
            trail: vec![],
            deductions: vec![],
        }
    }

    fn trail_len(&self) -> usize {
        self.trail.len()
    }

    fn assigment(&self, index: usize) -> &VarSource {
        &self.assigments[index]
    }

    fn raiseLevel(&mut self) -> TrailState {
        match self.trail.pop() {
            Some(x) => {
                self.assigments[x.var.index] = VarSource::Undef;
                self.strip_deductions();
                x
            }
            _ => panic!(),
        }
    }

    fn fixLevel(&mut self, state: TrailState) {
        self.assigments[state.var.index] = VarSource::Fixed(state.var.into_bool(), state.var.index);
        self.trail.push(state);
    }

    fn missing_assigments(&self) -> usize {
        self.assigments.len() - self.trail.len() - self.deductions.len()
    }

    /// Strips deductions up to trails.len()
    fn strip_deductions(&mut self) {
        loop {
            match self.last_deduct_level() {
                Some(level) if level >= self.trail_len() => self.pop_deduct(),
                _ => break,
            }
        }
    }

    fn pop_deduct(&mut self) {
        self.assigments[self.deductions.pop().unwrap().0.index] =
            VarSource::Undef;
    }

    fn last_deduct_level(&mut self) -> Option<usize> {
        self.deductions.last().map(|(_, level)| *level)
    }
}

#[derive(Debug)]
struct Solver<H>
where
    H: Heuristics,
    H: std::fmt::Debug,
{
    clauses: Vec<Clause>,
    //assigments: Vec<VarSource>,
    //deducted: usize,
    //trail: Vec<TrailState>,
    /// Var levels
    //deductions: Vec<(Var, usize)>,
    searchstate: SearchState,
    cursor: Cursor,
    heuristics: H,
}

#[derive(Debug)]
struct Cursor {
    position: usize,
}

fn debug() -> () {
    ()
}

#[derive(Debug, Clone)]
struct Conflict {
    clause: Clause,
}

impl<H> Solver<H>
where
    H: Heuristics,
    H: Default,
    H: std::fmt::Debug,
{
    fn init(clauses: Vec<Clause>) -> Result<Solver<H>, ()> {
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
        Ok(Solver {
            clauses,
            searchstate: SearchState::new(nvars),
            heuristics: H::default(),
            cursor: Cursor { position: 0 },
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
                        self.searchstate.assigment(lit.index).into_maybe_bool()
                            ^ !MaybeBool(Some(lit.sign))
                    })
                    .fold(MaybeBool::falsee(), |acc, x| acc | x)
            })
            .fold(MaybeBool::truee(), |acc, x| acc & x)
    }

    /// unit propagation, Err is conflict (not propagated, just raw)
    fn propagate(&mut self) -> Result<bool, Conflict> {
        let mut deductions = false;
        let position = self.cursor.position;
        let mut advance = 0;
        match self.clauses[position..]
            .iter()
            .chain(self.clauses[..position].iter())
            .map(|clause| {
                advance += 1;
                clause.assingable(&self.searchstate.assigments)
            })
            .find(|res| match res {
                VarAssingable::Nothing => false,
                _ => true,
            }) {
            Some(VarAssingable::Assingable(var, sources)) => {
                deductions = true;
                let conflict_level = sources
                    .iter()
                    .map(|s| self.searchstate.assigments[s.index].into_conflict_level())
                    .max()
                    .unwrap()
                    .unwrap();
                self.save_deduct(
                    var.index,
                    var.into_bool(),
                    sources.iter().filter(|&&x| x != var).cloned().collect(),
                    conflict_level,
                );
            }
            Some(VarAssingable::Conflict(conflict)) => {
                self.cursor.position = (self.cursor.position + advance) % self.clauses.len();
                return Err(conflict);
            }
            Some(VarAssingable::Nothing) => (),
            None => (),
        }
        self.cursor.position = (self.cursor.position + advance) % self.clauses.len();
        Ok(deductions)
    }

    fn save_deduct(&mut self, index: usize, assign: bool, vars: Vec<Var>, level: usize) {
        debug_assert!(
            self.searchstate.assigments[index] == VarSource::Undef,
            debug()
        );
        self.searchstate.assigments[index] = VarSource::Deducted(assign, vars, level);
        self.searchstate
            .deductions
            .push((Var::new(index, assign), level));
    }

    fn solve(&mut self) -> Result<(), ()> {
        loop {
            let propagate = self.propagate();
            #[cfg(debug_assertions)]
            println!("{}", self.searchstate);
            match propagate {
                Ok(new_deductions) if new_deductions == false => {
                    // are all variables fixed?
                    if self.searchstate.missing_assigments() == 0 {
                        return Ok(());
                    } else {
                        self.fix_some_var()
                    }
                }
                Ok(_) => (),
                Err(conflict) => {
                    if let Some(learnt_clause) = self.solve_conflict(conflict)? {
                        self.clauses.push(learnt_clause);
                    }
                }
            }
        }
    }

    fn fix_some_var(&mut self) {
        self.searchstate.fixLevel(TrailState{var: self.heuristics.select_variable(&self.searchstate), choice: FirstChoice});
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

        let mut conflict_plane: UnsafeCell<_> = conflict_plane.into();

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
            x += 1;
            if x > 10 {
                panic!()
            }
        }
        // TODO: generate clause from conflict plane and insert it

        // Undoes work up to implied_level, then change mind on var selection
        // last level -> delete
        // implication level -> change mind

        (implied_level..=self.searchstate.trail_len() - 2)
            .map(|_| self.searchstate.raiseLevel())
            .last();

        loop {
            match (self.searchstate.raiseLevel(), self.searchstate.trail_len()) {
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
                    self.searchstate.fixLevel(TrailState{var: Var{index, sign: !(bool::from(sign))}, choice: SecondChoice});
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
    let clauses = str_to_clauses("(x0 v x1) ^ (x1 v x2 v x3) ^ (~x0 v ~x3)");
    let mut solver = Solver::<NaiveHeuristics>::init(clauses).unwrap();
    assert!(Ok(()) == solver.solve());
    assert!(
        solver.test_satisfied() == MaybeBool::truee(),
        format!("{:?}, {:#?}", solver.test_satisfied(), solver)
    );
}
