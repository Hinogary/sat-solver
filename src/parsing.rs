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

use super::{Clause, Sign, Var};
use Token::*;

pub fn str_to_clauses(clauses: &str) -> Vec<Clause> {
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
                    sign: Sign::Positive,
                }),
                Some(NegVar) => clause.literals.push(Var {
                    index: lex.slice()[2..].parse().unwrap(),
                    sign: Sign::Negative,
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
