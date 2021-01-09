use super::{MaybeBool, Var, VarSource};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Clause {
    pub literals: Vec<Var>,
}

#[derive(Debug, Clone)]
pub enum VarAssingable {
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
    pub fn new() -> Clause {
        Clause {
            literals: Vec::new(),
        }
    }
    pub fn assingable(&self, assigments: &[VarSource]) -> VarAssingable {
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
            (false, Some(&to_assign)) => VarAssingable::Assingable(to_assign),
            (true, _) => VarAssingable::Nothing,
            (false, None) => VarAssingable::Conflict,
        }
    }

    pub fn insert(&mut self, var: Var) {
        self.literals.push(var)
    }
}
