#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct Var {
    index: usize,
    sign: Sign,
}

impl Var {
    fn new(index: usize, state: bool) -> Var {
        Var{
            index,
            sign: Sign::new_bool(state)
        }
    }
}

impl std::ops::Not for Var {
    type Output = Self;

    fn not(self) -> Self::Output {
        match self.sign {
            Sign::Positive => Var {
                sign: Sign::Negative,
                index: self.index,
            },
            Sign::Negative => Var {
                sign: Sign::Positive,
                index: self.index,
            },
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum Sign {
    Positive,
    Negative,
}

impl Sign {
    fn into_maybe_bool(self) -> MaybeBool {
        MaybeBool(Some(match self {
            Sign::Positive => true,
            Sign::Negative => false,
        }))
    }

    fn new_bool(b: bool) -> Sign {
        match b {
            true => Sign::Positive,
            false => Sign::Negative,
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
    fn to_maybe_bool(self) -> MaybeBool {
        match self.sign {
            Sign::Positive => MaybeBool(Some(true)),
            Sign::Negative => MaybeBool(Some(false)),
        }
    }
    fn into_bool(self) -> bool {
        self.sign == Sign::Positive
    }
}

impl std::fmt::Display for Var{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.sign == Sign::Negative {
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
    Conflict(Clause), // new Clause to add
    Nothing,
}


impl std::fmt::Display for Clause {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "(");
        self.literals.iter().take(1).for_each(|lit| {write!(f, "{}", lit);});
        self.literals.iter().skip(1).for_each(|lit| {write!(f, " v {}", lit);});
        write!(f, ")")
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

        for var in &self.literals {
            match (to_assign, var.sign, assigments[var.index].into_maybe_bool()) {
                (_, Sign::Positive, MaybeBool(Some(true)))
                | (_, Sign::Negative, MaybeBool(Some(false))) => return VarAssingable::Nothing, // it is already satisfied
                (None, _, MaybeBool(None)) => to_assign = Some(var),
                (Some(_), _, MaybeBool(None)) => return VarAssingable::Nothing, // at least 2 vars are undefined
                (_, Sign::Positive, MaybeBool(Some(false)))
                | (_, Sign::Negative, MaybeBool(Some(true))) => (),
            }
        }

        if let Some(to_assign) = to_assign {
            VarAssingable::Assingable(
                *to_assign,
                self.literals
                    .iter()
                    .filter(|&&var| var != *to_assign)
                    .cloned()
                    .collect(),
            )
        } else {
            VarAssingable::Conflict(self.clone())
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
            Undef => MaybeBool::undef(),
        }
    }

    fn into_conflict_level(&self) -> Option<usize> {
        match self {
            VarSource::Fixed(_, level) | VarSource::Deducted(_, _, level) => Some(*level),
            VarSource::Undef => None,
        }
    }
}

#[derive(Debug)]
enum TrailState {
    FirstChoice(bool, usize),
    SecondChoice(bool, usize),
}

impl TrailState{
    fn into_inner(self) -> (bool, usize) {
        match self {
            TrailState::FirstChoice(state, index) | TrailState::SecondChoice(state, index) => (state, index)
        }
    }
}

#[derive(Debug)]
struct CDCLSolver {
    clauses: Vec<Clause>,
    assigments: Vec<VarSource>,
    deducted: usize,
    /// Number of levels, first one with index zero is empty
    current_level: usize,
    trail: Vec<TrailState>,
    /// Var levels
    deductions: Vec<(Var, usize)>,
}

mod parsing;
use parsing::str_to_clauses;

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_parser() {
        use Sign::*;
        let clauses = str_to_clauses("(x0 v x1) ^ (x1 v x2 v x3) ^ (~x0 v ~x3)");
        assert!(
            clauses
                == vec![
                    Clause {
                        literals: vec![
                            Var {
                                index: 0,
                                sign: Positive
                            },
                            Var {
                                index: 1,
                                sign: Positive
                            }
                        ]
                    },
                    Clause {
                        literals: vec![
                            Var {
                                index: 1,
                                sign: Positive
                            },
                            Var {
                                index: 2,
                                sign: Positive
                            },
                            Var {
                                index: 3,
                                sign: Positive
                            }
                        ]
                    },
                    Clause {
                        literals: vec![
                            Var {
                                index: 0,
                                sign: Negative
                            },
                            Var {
                                index: 3,
                                sign: Negative
                            }
                        ]
                    }
                ]
        );
    }

    fn test_satisfability(expr: &str) {
        println!("------------------------------------------------");
        println!("{}", expr);
        let clauses = str_to_clauses(expr);
        let mut solver = CDCLSolver::init(clauses).unwrap();
        assert!(Ok(()) == solver.solve());
        assert!(
            solver.test_satisfied() == MaybeBool::truee(),
            format!("{:?}, {:#?}", solver.test_satisfied(), solver)
        );
    }

    #[test]
    fn test_solver() {
        test_satisfability("(x0 v x1) ^ (x1 v ~x2 v x3) ^ (~x0 v ~x3)");
        test_satisfability("(x0 v x1 v x2) ^ (~x0 v ~x1 v x2) ^ (~x0 v x1 v x2) ^ (x0 v ~x1 v x2)");
        test_satisfability("(x0 v x1 v x2) ^ (~x0 v x1 v ~x2) ^ (~x0 v x1 v x2) ^ (x0 v x1 v ~x2)");
        test_satisfability(
            "(x0 v x1 v ~x2) ^ (~x0 v ~x1 v ~x2) ^ (~x0 v x1 v ~x2) ^ (x0 v ~x1 v ~x2)",
        );
        test_satisfability(
            "(x0 v ~x1 v x2) ^ (~x0 v ~x1 v ~x2) ^ (~x0 v ~x1 v x2) ^ (x0 v ~x1 v ~x2)",
        );
        test_satisfability("(x0 v x1 v x2) ^ (x0 v ~x1 v x2) ^ (x0 v x1 v ~x2) ^ (x0 v ~x1 v ~x2)");
        test_satisfability(
            "(~x0 v x1 v x2) ^ (~x0 v ~x1 v x2) ^ (~x0 v x1 v ~x2) ^ (~x0 v ~x1 v ~x2)",
        );
    }
}

fn debug() ->() {
    ()
}

impl CDCLSolver {
    fn init(clauses: Vec<Clause>) -> Result<CDCLSolver, ()> {
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
        Ok(CDCLSolver {
            clauses,
            current_level: 0,
            deducted: 0,
            assigments: vec![VarSource::Undef; nvars],
            trail: vec![],
            deductions: vec![],
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
                        self.assigments[lit.index].into_maybe_bool() ^ !lit.sign.into_maybe_bool()
                    })
                    .fold(MaybeBool::falsee(), |acc, x| acc | x)
            })
            .fold(MaybeBool::truee(), |acc, x| acc & x)
    }

    /// unit propagation, Err is conflict (not propagated, just raw)
    fn propagate(&mut self) -> Result<bool, Clause> {
        let mut deductions = false;
        match self
            .clauses
            .iter()
            .map(|clause| clause.assingable(&self.assigments))
            .find(|res| match res {
                VarAssingable::Nothing => false,
                _ => true,
            }) {
            Some(VarAssingable::Assingable(var, sources)) => {
                deductions = true;
                let conflict_level = sources
                    .iter()
                    .map(|s| self.assigments[s.index].into_conflict_level())
                    .max()
                    .unwrap()
                    .unwrap();
                self.save_deduct(var.index, var.into_bool(), sources, conflict_level);
            }
            Some(VarAssingable::Conflict(clause)) => {
                return Err(clause);
            }
            Some(VarAssingable::Nothing) => unreachable!(),
            None => (),
        }
        Ok(deductions)
    }


    fn save_deduct(&mut self, index: usize, assign: bool, vars: Vec<Var>, level: usize){
        debug_assert!(
            self.assigments[index] == VarSource::Undef, debug()
        );
        self.assigments[index] = VarSource::Deducted(assign, vars, level);
        self.deductions.push(Var::new(index, assign), level);
        self.deducted += 1;
    }

    fn pop_deduct(&mut self){
        self.deducted -= 1;
        self.assigments[self.deductions.pop().unwrap().index] = VarSource::Undef;
    }

    fn last_deduct_level(&mut self) -> Option<usize> {

    }

    fn solve(&mut self) -> Result<(), ()> {
        loop {
            match self.propagate() {
                Ok(new_deductions) if new_deductions == false => {
                    // are all variables fixed?
                    if self.deducted + self.trail.len() == self.assigments.len() {
                        return Ok(());
                    } else {
                        self.fix_some_var()
                    }
                }
                Ok(_) => (),
                Err(conflict) => {
                    self.solve_conflict(conflict)?;
                }
            }
        }
    }

    fn fix_some_var(&mut self) {
        debug_assert!(
            self.deducted + self.trail.len() < self.assigments.len(),
            format!("{:#?}", self)
        );
        for (index, var) in (0..).zip(&mut self.assigments) {
            if *var == VarSource::Undef {
                *var = VarSource::Fixed(false, self.current_level);
                self.trail.push(TrailState::FirstChoice(true, index));
                break;
            }
        }
    }

    /// Conflict is clause, where all Variables are assigned, but Clause forms Contradiction
    fn solve_conflict(&mut self, conflict: Clause) -> Result<Clause, ()> {
        use std::cell::UnsafeCell;
        use std::collections::HashMap as Map;
        use std::collections::HashSet as Set;
        println!("conflict: {}", conflict);

        if conflict.literals.is_empty() {
            return Err(());
        }

        // Trying to get conflict plane

        let mut conflict_plane = Map::new(); // var, is_on_edge?
        let mut last_level: Option<(usize, Var)> = None; // this is conflict level, that needs to be reverted
        let mut implied_level = None; // this is on which can be variable implied
        for var in conflict.literals {
            conflict_plane.insert(var, true);
            let level = self.assigments[var.index].into_conflict_level().unwrap();
            if level >= last_level.map(|x| x.0).unwrap_or(0) {
                implied_level = last_level;
                last_level = Some((level, var));
            }
        }

        // last level -> delete
        // implication level -> change mind

        let last_level = last_level.unwrap();
        println!("");

        // TODO: What if I missed some propagation and two levels collide? Then I probably need be more aggresive with cutting. Probably not problem ...

        // TODO: heuristics for stoping resolution
        let mut new_clause_from_conflict = Clause::empty();
        let mut waiting_to_insert_into_cf = Set::new();
        let mut conflict_plane: UnsafeCell<_> = conflict_plane.into();
        let mut fixed_last_level = None;
        loop {
            for (&k, v) in unsafe { &mut *conflict_plane.get() }
                .iter_mut()
                .filter(|(_, v)| **v)
            {
                match &self.assigments[k.index] {
                    VarSource::Undef => unreachable!(),
                    VarSource::Deducted(_, source, _) => {
                        *v = false;
                        for var in source {
                            // Keys can't aliasing, it will cause cyclic Clause
                            if unsafe { &*conflict_plane.get() }.get(&k) == None {
                                waiting_to_insert_into_cf.insert(k);
                            }
                        }
                    }
                    VarSource::Fixed(_, level) => {
                        if *level == last_level.0 {
                            fixed_last_level = Some(k)
                        }
                        new_clause_from_conflict.insert(if *level == last_level.0 { k } else { !k })
                    }
                }
                *v = false;
            }
            if waiting_to_insert_into_cf.is_empty() {
                break;
            }
            waiting_to_insert_into_cf.retain(|&key| {
                unsafe { &mut *conflict_plane.get() }.insert(key, true);
                false
            });
        }
        if new_clause_from_conflict.is_empty() {
            Err(()) // tautology
        } else {
            while self.trail.len() > last_level.0 {
                let (b, i) = self.trail.pop().unwrap().into_inner();
                match self.assigments[i] {
                    VarSource::Deducted(_, _, _) => self.deducted -= 1,
                    _ => (),
                }
                self.assigments[i] = VarSource::Undef;
            }
            let implied_level = implied_level.map(|x| x.0).unwrap_or(0);
            assert!(last_level.1.into_bool() == false);
            if let Some(fixed_last_level) = fixed_last_level {
                self.save_deduct(
                    last_level.1.index,
                    last_level.1.into_bool(),
                    new_clause_from_conflict
                        .literals
                        .iter()
                        .cloned()
                        .filter(|&lit| lit != fixed_last_level)
                        .collect(),
                    implied_level
                )
            } else {
                panic!()
            }
            Ok(new_clause_from_conflict)
        }
    }
}

fn main() {
    let clauses = str_to_clauses("(x0 v x1) ^ (x1 v x2 v x3) ^ (~x0 v ~x3)");
    let mut solver = CDCLSolver::init(clauses).unwrap();
    assert!(Ok(()) == solver.solve());
    assert!(
        solver.test_satisfied() == MaybeBool::truee(),
        format!("{:?}, {:#?}", solver.test_satisfied(), solver)
    );
}
