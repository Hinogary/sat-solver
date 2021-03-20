use super::{Var, ReasonLock, VarSource, Solver, Clause};

// this is where weighted SAT is implemented
pub trait SelectionHeuristics
where
    Self: Sized + std::fmt::Debug,
{
    fn select_variable(solver: &mut Solver<Self>) -> Var;
    // assigns and asks if continue (possible cut)
    fn assign(&mut self, var: Var, reason: ReasonLock) -> bool;
    fn deassign(&mut self, var: Var);
    // found solution and asks if final solution
    fn final_solution(&mut self, assigments: &[VarSource]) -> bool;
    fn solution(solver: &Solver<Self>) -> Vec<bool>;
    fn appears_in_conflict(&mut self, var: Var);
}

#[derive(Debug, Clone, Copy)]
pub struct NaiveSelectionHeuristics {
    index: usize,
}

impl NaiveSelectionHeuristics {
    pub fn new() -> Self {
        NaiveSelectionHeuristics { index: 0 }
    }
}

impl SelectionHeuristics for NaiveSelectionHeuristics {
    fn select_variable(solver: &mut Solver<Self>) -> Var {
        let mut index = solver.sel_heuristics.index;
        //fix first unassigned var
        while solver.assigments[index] != VarSource::Undef {
            index = (index + 1) % solver.assigments.len()
        }
        let assign =
            solver.watchers[index].for_true.len() <= solver.watchers[index].for_false.len();
        solver.sel_heuristics.index = index;
        Var {
            sign: assign,
            index: index,
        }
    }
    // assigns and asks if continue
    // on false conclude it was assigned anyways ... it will call to deassign
    fn assign(&mut self, _: Var, _: ReasonLock) -> bool {
        true
    }
    fn deassign(&mut self, _: Var) {}
    // found solution and asks if final solution
    fn final_solution(&mut self, _: &[VarSource]) -> bool {
        true
    }
    fn solution(solver: &Solver<Self>) -> Vec<bool> {
        solver.assigments.iter().map(|x| x.into_bool()).collect()
    }
    fn appears_in_conflict(&mut self, _: Var) {}
}

use priority_queue::PriorityQueue;

#[derive(Debug)]
pub struct PrioritySelectionHeuristics {
    queue: PriorityQueue<Var, usize>,
    priorities: Vec<usize>,
}

impl PrioritySelectionHeuristics {
    pub fn new(clauses: &Vec<Clause>) -> Self {
        let nvars = clauses
            .iter()
            .map(|c| c.literals.iter().map(|l| l.index).max().unwrap())
            .max()
            .unwrap()
            + 1;
        let mut queue = PriorityQueue::new();
        for i in 0..nvars {
            queue.push(
                Var {
                    index: i,
                    sign: true,
                },
                0,
            );
        }

        PrioritySelectionHeuristics {
            priorities: vec![0; nvars],
            queue,
        }
    }
}

impl SelectionHeuristics for PrioritySelectionHeuristics {
    fn select_variable(solver: &mut Solver<Self>) -> Var {
        *solver.sel_heuristics.queue.peek().unwrap().0
    }
    // assigns and asks if continue
    fn assign(&mut self, var: Var, _: ReasonLock) -> bool {
        self.priorities[var.index] += 1;
        if var.sign {
            self.queue.remove(&var);
        } else {
            self.queue.remove(&!var);
        }
        // if attainable weight is higher than best_weight -> continue
        true
    }
    fn deassign(&mut self, var: Var) {
        if var.sign {
            self.queue.push(var, self.priorities[var.index]);
        } else {
            self.queue.push(!var, self.priorities[var.index]);
        }
    }
    // found solution and asks if final solution
    fn final_solution(&mut self, _: &[VarSource]) -> bool {
        true
    }
    fn solution(solver: &Solver<Self>) -> Vec<bool> {
        solver.assigments.iter().map(|x| x.into_bool()).collect()
    }
    fn appears_in_conflict(&mut self, var: Var) {
        self.priorities[var.index] += 3
    }
}

#[derive(Debug)]
pub struct GreedyWeightSelectionHeuristics {
    best_weight: usize,
    best_solution: Vec<bool>,
    weights: Vec<usize>,
    queue: PriorityQueue<Var, (usize, usize)>,
    free_weight: usize,
    current_weight: usize,
    priorities: Vec<usize>,
}

impl GreedyWeightSelectionHeuristics {
    pub fn new(weights: Vec<usize>, _clauses: &Vec<Clause>) -> GreedyWeightSelectionHeuristics {
        let mut queue = PriorityQueue::new();
        for (i, w) in weights.iter().enumerate() {
            queue.push(
                Var {
                    index: i,
                    sign: true,
                },
                (0, *w),
            );
        }

        let free_weight = weights.iter().sum();

        GreedyWeightSelectionHeuristics {
            best_solution: vec![false; weights.len()],
            priorities: vec![0; weights.len()],
            current_weight: 0,
            best_weight: 0,
            queue,
            free_weight,
            weights,
        }
    }
    pub fn best_weight(&self) -> usize{
        self.best_weight
    }
}

impl SelectionHeuristics for GreedyWeightSelectionHeuristics {
    fn select_variable(solver: &mut Solver<Self>) -> Var {
        *solver.sel_heuristics.queue.peek().unwrap().0
    }
    // assigns and asks if continue
    fn assign(&mut self, var: Var, _: ReasonLock) -> bool {
        let weight = self.weights[var.index];
        self.priorities[var.index] += 1;
        self.free_weight -= weight;
        if var.sign {
            self.current_weight += weight;
            self.queue.remove(&var);
        } else {
            self.queue.remove(&!var);
        }
        // if attainable weight is higher than best_weight -> continue
        self.best_weight <= self.current_weight + self.free_weight
    }
    fn deassign(&mut self, var: Var) {
        let weight = self.weights[var.index];
        self.free_weight += weight;
        if var.sign {
            self.current_weight -= weight;
            self.queue.push(var, (self.priorities[var.index], weight));
        } else {
            self.queue.push(!var, (self.priorities[var.index], weight));
        }
    }
    // found solution and asks if final solution
    fn final_solution(&mut self, assigments: &[VarSource]) -> bool {
        if self.current_weight > self.best_weight {
            self.best_solution
                .iter_mut()
                .zip(assigments.iter())
                .for_each(|(s, a)| *s = a.into_bool());
            self.best_weight = self.current_weight;
        }
        false // force for full search space
    }
    fn solution(solver: &Solver<Self>) -> Vec<bool> {
        solver.sel_heuristics.best_solution.clone()
    }
    fn appears_in_conflict(&mut self, var: Var) {
        self.priorities[var.index] += 3
    }
}
