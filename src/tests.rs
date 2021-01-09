#[cfg(test)]
mod tests {
    use super::super::*;

    fn test_assingability(clause: &str, assign: &[bool]) {
        let assignable = assingability(clause, assign);
        assert!(
            match assignable {
                VarAssingable::Assingable(_) => true,
                _ => false,
            },
            format!("{} {:?}", clause, assignable)
        );
    }

    fn test_conflit_assigability(clause: &str, assign: &[bool]) {
        let assignable = assingability(clause, assign);
        assert!(
            match assignable {
                VarAssingable::Conflict => true,
                _ => false,
            },
            format!("{} {:?}", clause, assignable)
        );
    }

    fn test_unassigability(clause: &str, assign: &[bool]) {
        let assignable = assingability(clause, assign);
        assert!(
            match assignable {
                VarAssingable::Nothing => true,
                _ => false,
            },
            format!("{} {:?}", clause, assignable)
        );
    }

    fn assingability(clause: &str, assign: &[bool]) -> VarAssingable {
        let clause = str_to_clause(clause);
        let n_assigns = clause.literals.iter().map(|x| x.index).max().unwrap() + 1;
        let mut assigns = assign
            .iter()
            .enumerate()
            .map(|(i, &x)| VarSource::Fixed(x, i))
            .collect::<Vec<_>>();
        (assigns.len()..n_assigns).for_each(|_| assigns.push(VarSource::Undef));
        clause.assingable(&assigns)
    }

    #[test]
    fn test_assingability_cases() {
        test_assingability("(x0 v x1)", &[false]);
        test_assingability("(x0 v ~x1)", &[false]);
        test_assingability("(x1 v ~x0)", &[true]);
        test_assingability("(x1 v x0)", &[false]);
        test_assingability("(~x0 v x1)", &[true]);
        test_assingability("(~x0 v ~x1)", &[true]);
        test_assingability("(~x1 v ~x0)", &[true]);
        test_assingability("(~x1 v x0)", &[false]);
        test_assingability("(~x1 v x0 v x2)", &[false, true]);
        test_assingability("(~x0 v x1 v ~x2)", &[true, false]);
        test_assingability("(~x1 v ~x2 v x0)", &[false, true]);
        test_assingability("(~x2 v x1 v ~x0)", &[true, false]);

        test_conflit_assigability("(x0 v ~x1 v x2)", &[false, true, false]);
        test_conflit_assigability("(~x1 v ~x0 v ~x2)", &[true, true, true]);
        test_conflit_assigability("(x0 v ~x1 v x2)", &[false, true, false]);
        test_conflit_assigability("(x2 v ~x1 v x0)", &[false, true, false]);
        test_conflit_assigability("(x2 v ~x0 v ~x1)", &[true, true, false]);

        test_unassigability("(x0 v x1)", &[]);
        test_unassigability("(x1 v x0)", &[]);
        test_unassigability("(x0 v x2 v x1)", &[true]);

        test_conflit_assigability("(x0 v x1)", &[false, false]);
        test_conflit_assigability("(~x0 v x1)", &[true, false]);
        test_conflit_assigability("(x0 v ~x1)", &[false, true]);
        test_conflit_assigability("(~x0 v ~x1)", &[true, true]);

        test_conflit_assigability("(x1 v x0)", &[false, false]);
        test_conflit_assigability("(x1 v ~x0)", &[true, false]);
        test_conflit_assigability("(~x1 v x0)", &[false, true]);
        test_conflit_assigability("(~x1 v ~x0)", &[true, true]);
    }

    fn test_satisfability<H: SelectionHeuristics>(expr: &str) {
        println!("------------------------------------------------");
        println!("{}", expr);
        let clauses = str_to_clauses(expr);
        let mut solver = Solver::<H>::init(clauses).unwrap();
        let assigns = solver.solve().unwrap();
        assert!(
            solver.test_satisfied(&assigns) == true,
            format!("{:?}, {:#?}", solver.test_satisfied(&assigns), solver)
        );
    }

    fn test_solver_satisfability<H: SelectionHeuristics>() {
        test_satisfability::<H>("(x0 v x1) ^ (x1 v ~x2 v x3) ^ (~x0 v ~x3)");

        test_satisfability::<H>(
            "(x0 v x1 v x2) ^ (~x0 v ~x1 v x2) ^ (~x0 v x1 v x2) ^ (x0 v ~x1 v x2)",
        );
        test_satisfability::<H>(
            "(x0 v x1 v x2) ^ (~x0 v x1 v ~x2) ^ (~x0 v x1 v x2) ^ (x0 v x1 v ~x2)",
        );
        test_satisfability::<H>(
            "(x0 v x1 v ~x2) ^ (~x0 v ~x1 v ~x2) ^ (~x0 v x1 v ~x2) ^ (x0 v ~x1 v ~x2)",
        );
        test_satisfability::<H>(
            "(x0 v ~x1 v x2) ^ (~x0 v ~x1 v ~x2) ^ (~x0 v ~x1 v x2) ^ (x0 v ~x1 v ~x2)",
        );
        test_satisfability::<H>(
            "(x0 v x1 v x2) ^ (x0 v ~x1 v x2) ^ (x0 v x1 v ~x2) ^ (x0 v ~x1 v ~x2)",
        );
        test_satisfability::<H>(
            "(~x0 v x1 v x2) ^ (~x0 v ~x1 v x2) ^ (~x0 v x1 v ~x2) ^ (~x0 v ~x1 v ~x2)",
        );
    }

    #[test]
    fn test_solver() {
        test_solver_satisfability::<NaiveSelectionHeuristics>();
    }
}
