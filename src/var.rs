#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Var {
    pub index: usize,
    pub sign: bool,
}

impl Var {
    pub fn new(index: usize, state: bool) -> Var {
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