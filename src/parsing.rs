use logos::Logos;

#[derive(Logos, Debug, PartialEq)]
enum Token {
    #[token("(")]
    OpenBracket,

    #[token(")")]
    CloseBracket,

    #[regex("x[0-9]+")]
    PosVar,

    #[regex("[~!]x[0-9]+")]
    NegVar,

    #[regex("v")]
    Or,

    #[regex(r"\^")]
    And,

    #[error]
    #[regex(r"[ \t\n\f]+", logos::skip)]
    Error,
}

use super::{Clause, ProblemType, Var};

pub fn str_to_clauses(clauses: &str) -> Vec<Clause> {
    use Token::*;
    let mut lex = Token::lexer(clauses);
    let mut clauses = Vec::new();
    loop {
        let mut clause = Clause::new();
        match lex.next() {
            Some(OpenBracket) => (),
            None => break,
            _ => panic!("Expected '(' or end found: '{}'", lex.slice()),
        }
        loop {
            match lex.next() {
                Some(PosVar) => clause.literals.push(Var {
                    index: lex.slice()[1..].parse().unwrap(),
                    sign: true,
                }),
                Some(NegVar) => clause.literals.push(Var {
                    index: lex.slice()[2..].parse().unwrap(),
                    sign: false,
                }),
                _ => panic!("Expected variable, found: '{}'", lex.slice()),
            }
            match lex.next() {
                Some(CloseBracket) => break,
                Some(Or) => (),
                _ => panic!("Expected 'v' or ')', found: '{}'", lex.slice()),
            }
        }
        clauses.push(clause);
        match lex.next() {
            None => break,
            Some(And) => (),
            _ => panic!("Expected '^' or end, found: '{}'", lex.slice()),
        }
    }
    clauses
}

pub fn str_to_clause(clause: &str) -> Clause {
    use Token::*;
    let mut lex = Token::lexer(clause);
    let mut clause = Clause::new();
    match lex.next() {
        Some(OpenBracket) => (),
        _ => panic!("Expected '(' or end found: '{}'", lex.slice()),
    }
    loop {
        match lex.next() {
            Some(PosVar) => clause.literals.push(Var {
                index: lex.slice()[1..].parse().unwrap(),
                sign: true,
            }),
            Some(NegVar) => clause.literals.push(Var {
                index: lex.slice()[2..].parse().unwrap(),
                sign: false,
            }),
            _ => panic!("Expected variable, found: '{}'", lex.slice()),
        }
        match lex.next() {
            Some(CloseBracket) => break,
            Some(Or) => (),
            _ => panic!("Expected 'v' or ')', found: '{}'", lex.slice()),
        }
    }
    assert!(lex.next() == None);
    clause
}

#[derive(Logos, Debug, PartialEq)]
enum DimacsToken {
    #[token(r"p")]
    Problem,

    #[regex(r"cnf")]
    CNF,

    #[regex(r"mwcnf")]
    MWCNF,

    #[regex("w")]
    Weights,

    #[regex(r"-?[0-9]+")]
    Number,

    #[error]
    #[regex(r"[ \n\t\f%]+|c [a-zA-Z0-9 '\(\),?=\t%\.\-/]*|c", logos::skip)]
    Error,
}

pub fn dimacs_to_clausules(dimacs: &str) -> ProblemType {
    use DimacsToken::*;
    let mut lex = DimacsToken::lexer(dimacs);
    let mut weighted = false;
    match lex.next() {
        Some(Problem) => (),
        _ => panic!("Expected 'p', found: '{}'", lex.slice()),
    }
    match lex.next() {
        Some(CNF) => (),
        Some(MWCNF) => {
            weighted = true;
        }
        _ => (),
    }
    match lex.next() {
        Some(Number) => (), //clauses
        _ => panic!("Expected Number, found: '{}'", lex.slice()),
    }
    match lex.next() {
        Some(Number) => (), //variables
        _ => panic!("Expected Number, found: '{}'", lex.slice()),
    }
    let weights = if weighted {
        match lex.next() {
            Some(Weights) => (),
            _ => panic!("Expected w, found: '{}'", lex.slice()),
        }
        let mut weights = Vec::new();
        loop {
            match lex.next() {
                Some(Number) => {
                    let num = lex.slice().parse::<usize>().unwrap();
                    if num == 0 {
                        break;
                    }
                    weights.push(num)
                }
                _ => panic!("Expected Number, found: '{}'", lex.slice()),
            }
        }
        Some(weights)
    } else {
        None
    };
    let mut clauses: Vec<Clause> = vec![];
    let mut current_clause = Clause::new();
    loop {
        match lex.next() {
            Some(Number) => {
                let num = lex.slice().parse::<isize>().unwrap();
                if num == 0 {
                    if !current_clause.literals.is_empty() {
                        clauses.push(current_clause);
                    }
                    current_clause = Clause::new();
                } else {
                    current_clause.insert(Var::new(num.abs() as usize - 1, num > 0))
                }
            }
            None => break,
            _ => panic!("Expected Number, found: '{}'", lex.slice()),
        }
    }
    if weighted {
        ProblemType::Weighted(clauses, weights.unwrap())
    } else {
        ProblemType::Unweighted(clauses)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_parser() {
        let clauses = str_to_clauses("(x0 v x1) ^ (x1 v x2 v x3) ^ (~x0 v ~x3)");
        assert!(
            clauses
                == vec![
                    Clause {
                        literals: vec![
                            Var {
                                index: 0,
                                sign: true
                            },
                            Var {
                                index: 1,
                                sign: true
                            }
                        ]
                    },
                    Clause {
                        literals: vec![
                            Var {
                                index: 1,
                                sign: true
                            },
                            Var {
                                index: 2,
                                sign: true
                            },
                            Var {
                                index: 3,
                                sign: true
                            }
                        ]
                    },
                    Clause {
                        literals: vec![
                            Var {
                                index: 0,
                                sign: false
                            },
                            Var {
                                index: 3,
                                sign: false
                            }
                        ]
                    }
                ]
        )
    }

    #[test]
    fn test_dimacs_cnf_parser() {
        let input = "
            c CNF Example
            c 4 variabwles, 6 clauses
            c each clausse is termiwnated by '0' (not by the end of line)
            p cnf 4 6
            1 -3 4 0
            -1 2 -3 0
            3 4 0
            1 2 -3 -4 0
            -2 3 0
            -3 -4 0
            %
            0
        ";
        assert!(
            dimacs_to_clausules(input)
                == ProblemType::Unweighted(vec![
                    Clause {
                        literals: vec![
                            Var {
                                index: 0,
                                sign: true,
                            },
                            Var {
                                index: 2,
                                sign: false,
                            },
                            Var {
                                index: 3,
                                sign: true,
                            },
                        ],
                    },
                    Clause {
                        literals: vec![
                            Var {
                                index: 0,
                                sign: false,
                            },
                            Var {
                                index: 1,
                                sign: true,
                            },
                            Var {
                                index: 2,
                                sign: false,
                            },
                        ],
                    },
                    Clause {
                        literals: vec![
                            Var {
                                index: 2,
                                sign: true,
                            },
                            Var {
                                index: 3,
                                sign: true,
                            },
                        ],
                    },
                    Clause {
                        literals: vec![
                            Var {
                                index: 0,
                                sign: true,
                            },
                            Var {
                                index: 1,
                                sign: true,
                            },
                            Var {
                                index: 2,
                                sign: false,
                            },
                            Var {
                                index: 3,
                                sign: false,
                            },
                        ],
                    },
                    Clause {
                        literals: vec![
                            Var {
                                index: 1,
                                sign: false,
                            },
                            Var {
                                index: 2,
                                sign: true,
                            },
                        ],
                    },
                    Clause {
                        literals: vec![
                            Var {
                                index: 2,
                                sign: false,
                            },
                            Var {
                                index: 3,
                                sign: false,
                            },
                        ],
                    }
                ]),
            format!("{:#?}", dimacs_to_clausules(input))
        );
    }

    #[test]
    fn test_dimacs_mwcnf_parser() {
        let input = "
            c MWCNF Example
            c 4 variables, 6 clauses
            c each clause is terminated by '0' (not by the end of line)
            p mwcnf 4 6
            c zero-terminated as the clauses
            w 2 4 1 6 0
            1 -3 4 0
            -1 2 -3 0
            3 4 0
            1 2 -3 -4 0
            -2 3 0
            -3 -4 0
        ";
        assert!(
            dimacs_to_clausules(input)
                == ProblemType::Weighted(
                    vec![
                        Clause {
                            literals: vec![
                                Var {
                                    index: 0,
                                    sign: true,
                                },
                                Var {
                                    index: 2,
                                    sign: false,
                                },
                                Var {
                                    index: 3,
                                    sign: true,
                                },
                            ],
                        },
                        Clause {
                            literals: vec![
                                Var {
                                    index: 0,
                                    sign: false,
                                },
                                Var {
                                    index: 1,
                                    sign: true,
                                },
                                Var {
                                    index: 2,
                                    sign: false,
                                },
                            ],
                        },
                        Clause {
                            literals: vec![
                                Var {
                                    index: 2,
                                    sign: true,
                                },
                                Var {
                                    index: 3,
                                    sign: true,
                                },
                            ],
                        },
                        Clause {
                            literals: vec![
                                Var {
                                    index: 0,
                                    sign: true,
                                },
                                Var {
                                    index: 1,
                                    sign: true,
                                },
                                Var {
                                    index: 2,
                                    sign: false,
                                },
                                Var {
                                    index: 3,
                                    sign: false,
                                },
                            ],
                        },
                        Clause {
                            literals: vec![
                                Var {
                                    index: 1,
                                    sign: false,
                                },
                                Var {
                                    index: 2,
                                    sign: true,
                                },
                            ],
                        },
                        Clause {
                            literals: vec![
                                Var {
                                    index: 2,
                                    sign: false,
                                },
                                Var {
                                    index: 3,
                                    sign: false,
                                },
                            ],
                        },
                    ],
                    vec![2, 4, 1, 6,],
                ),
            format!("{:#?}", dimacs_to_clausules(input))
        );
    }
}
