use crate::compiler::taint_analysis::{Judgement, Taint, TaintAnalysis, TaintType, TypeVariable};
use crate::compiler::union_find::UnionFind;
use petgraph::algo::tarjan_scc;
use petgraph::graph::{DiGraph, NodeIndex};
use std::collections::HashMap;

/// Constraint solver for taint analysis
#[derive(Clone)]
pub struct ConstraintSolver {
    unification: UnionFind,
    judgements: Vec<Judgement>,
    // TODO: Add fields for subtyping and instantiation constraints
}

impl ConstraintSolver {
    pub fn new(taint_analysis: &TaintAnalysis) -> Self {
        ConstraintSolver {
            unification: UnionFind::new(),
            judgements: taint_analysis.get_judgements_data().to_vec(),
        }
    }

    /// Main entry point for constraint solving
    pub fn solve(&mut self) {
        // TODO: Implement constraint solving logic
        self.inline_equalities();
        // println!("\n\n=== Inlined equalities ===");
        // println!("{}", self.judgements_string());
        // println!("Number of judgements: {}", self.num_judgements());
        self.blow_up_le_of_meet();
        // println!("\n\n=== Blow up le of meet ===");
        // println!("{}", self.judgements_string());
        // println!("Number of judgements: {}", self.num_judgements());
        self.simplify_le_pure();
        // println!("\n\n=== Simplified le of pure ===");
        // println!("{}", self.judgements_string());
        // println!("Number of judgements: {}", self.num_judgements());
        self.unify_cycles();
        // println!("\n\n=== Unified cycles ===");
        // println!("{}", self.judgements_string());
        // println!("Number of judgements: {}", self.num_judgements());
        self.cleanup_judgements();
        // println!("\n\n=== Cleaned up judgements ===");
        // println!("{}", self.judgements_string());
        // println!("Number of judgements: {}", self.num_judgements());
    }

    pub fn judgements_string(&self) -> String {
        self.judgements
            .iter()
            .map(|j| match j {
                Judgement::Eq(l, r) => {
                    let l_substituted = self.unification.substitute_variables(l);
                    let r_substituted = self.unification.substitute_variables(r);
                    format!(
                        "{} = {}",
                        l_substituted.to_string(),
                        r_substituted.to_string()
                    )
                }
                Judgement::Le(l, r) => {
                    let l_substituted = self.unification.substitute_variables(l);
                    let r_substituted = self.unification.substitute_variables(r);
                    format!(
                        "{} ≤ {}",
                        l_substituted.to_string(),
                        r_substituted.to_string()
                    )
                }
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    pub fn num_judgements(&self) -> usize {
        self.judgements.len()
    }

    fn inline_equalities(&mut self) {
        let mut new_judgements = Vec::new();
        for judgement in &self.judgements {
            match judgement {
                Judgement::Eq(Taint::Variable(l), Taint::Variable(r)) => {
                    self.unification.union(*l, *r);
                }
                Judgement::Eq(Taint::Variable(l), t) => {
                    // TODO: Occurs check
                    self.unification.set_taint(*l, t.clone());
                }
                Judgement::Eq(l, r) => {
                    panic!(
                        "Don't know how to handle this equality yet: {:?} = {:?}",
                        l, r
                    );
                }
                _ => new_judgements.push(judgement.clone()),
            }
        }
        self.judgements = new_judgements;
    }

    fn flatten_meets(&self, taint: &Taint) -> Vec<Taint> {
        match taint {
            Taint::Meet(l, r) => {
                let mut result = Vec::new();
                result.extend(self.flatten_meets(l));
                result.extend(self.flatten_meets(r));
                result
            }
            _ => vec![taint.clone()],
        }
    }

    fn blow_up_le_of_meet(&mut self) {
        let mut new_judgements = Vec::new();
        for judgement in &self.judgements {
            match judgement {
                Judgement::Le(l, r) => {
                    let flattened_meets = self.flatten_meets(r);
                    for meet in flattened_meets {
                        new_judgements.push(Judgement::Le(l.clone(), meet));
                    }
                }
                _ => new_judgements.push(judgement.clone()),
            }
        }
        self.judgements = new_judgements;
    }

    fn simplify_le_pure(&mut self) {
        let mut new_judgements = Vec::new();
        for judgement in &self.judgements {
            match judgement {
                Judgement::Le(Taint::Pure, r) => {
                    new_judgements.push(Judgement::Eq(Taint::Pure, r.clone()));
                }
                Judgement::Le(l, Taint::Pure) => {}
                _ => new_judgements.push(judgement.clone()),
            }
        }
        self.judgements = new_judgements;
    }

    /// Generate a Graphviz DOT representation of variable inequalities
    pub fn generate_inequality_graph(&self) -> String {
        let mut dot = String::new();
        dot.push_str("digraph InequalityGraph {\n");
        dot.push_str("  rankdir=TB;\n");
        dot.push_str("  node [shape=box];\n\n");

        // Collect all variable inequalities
        for judgement in &self.judgements {
            match judgement {
                Judgement::Le(l, r) => {
                    let l_substituted = self.unification.substitute_variables(l);
                    let r_substituted = self.unification.substitute_variables(r);

                    // Only include variable-to-variable inequalities
                    if let (Taint::Variable(left_var), Taint::Variable(right_var)) =
                        (&l_substituted, &r_substituted)
                    {
                        dot.push_str(&format!(
                            "  V{} -> V{} [label=\"\"];\n",
                            left_var.0, right_var.0
                        ));
                    }
                }
                _ => {}
            }
        }

        dot.push_str("}\n");
        dot
    }

    /// Detect cycles in the inequality graph and unify variables in cycles
    pub fn unify_cycles(&mut self) {
        let mut graph = DiGraph::new();
        let mut var_to_node = HashMap::new();
        let mut node_to_var = HashMap::new();

        // Build the graph from inequalities
        for judgement in &self.judgements {
            match judgement {
                Judgement::Le(l, r) => {
                    let l_substituted = self.unification.substitute_variables(l);
                    let r_substituted = self.unification.substitute_variables(r);

                    if let (Taint::Variable(left_var), Taint::Variable(right_var)) =
                        (&l_substituted, &r_substituted)
                    {
                        // Add nodes if they don't exist
                        let left_node = *var_to_node.entry(*left_var).or_insert_with(|| {
                            let node = graph.add_node(*left_var);
                            node_to_var.insert(node, *left_var);
                            node
                        });

                        let right_node = *var_to_node.entry(*right_var).or_insert_with(|| {
                            let node = graph.add_node(*right_var);
                            node_to_var.insert(node, *right_var);
                            node
                        });

                        // Add edge
                        graph.add_edge(left_node, right_node, ());
                    }
                }
                _ => {}
            }
        }

        // Find strongly connected components using petgraph's tarjan_scc
        let sccs = tarjan_scc(&graph);

        // Unify variables in each cycle
        for scc in sccs {
            if scc.len() > 1 {
                let cycle_vars: Vec<TypeVariable> =
                    scc.iter().map(|&node| node_to_var[&node]).collect();
                println!("Found cycle: {:?}", cycle_vars);
                // Unify all variables in the cycle with the first one
                let representative = cycle_vars[0];
                for &var in &cycle_vars[1..] {
                    self.unification.union(representative, var);
                }
            }
        }
    }

    /// Clean up judgements by removing reflexive inequalities and duplicates
    fn cleanup_judgements(&mut self) {
        let mut new_judgements = Vec::new();
        let mut seen = std::collections::HashSet::new();

        for judgement in &self.judgements {
            match judgement {
                Judgement::Le(l, r) => {
                    let l_substituted = self.unification.substitute_variables(l);
                    let r_substituted = self.unification.substitute_variables(r);

                    // Skip reflexive inequalities (X ≤ X)
                    if l_substituted == r_substituted {
                        continue;
                    }

                    // Create a canonical form for deduplication
                    let canonical = format!(
                        "{} ≤ {}",
                        l_substituted.to_string(),
                        r_substituted.to_string()
                    );
                    if seen.insert(canonical) {
                        new_judgements.push(judgement.clone());
                    }
                }
                Judgement::Eq(l, r) => {
                    let l_substituted = self.unification.substitute_variables(l);
                    let r_substituted = self.unification.substitute_variables(r);

                    // Skip reflexive equalities (X = X)
                    if l_substituted == r_substituted {
                        continue;
                    }

                    // Create a canonical form for deduplication
                    let canonical = format!(
                        "{} = {}",
                        l_substituted.to_string(),
                        r_substituted.to_string()
                    );
                    if seen.insert(canonical) {
                        new_judgements.push(judgement.clone());
                    }
                }
            }
        }

        self.judgements = new_judgements;
    }

    fn solve_under_instantiations(
        &mut self,
        insts: Vec<(TypeVariable, Taint)>,
        constraints: Vec<(TypeVariable, Taint)>,
        other_judgements: &Vec<Judgement>,
    ) {
        let cloned = self.with_judgements(
            other_judgements.iter().cloned().chain(
                constraints
                    .iter()
                    .cloned()
                    .map(|(l, r)| Judgement::Le(Taint::Variable(l), r)),
            )
            .chain(
                insts.iter()
                    .cloned()
                    .map(|(l, r)| Judgement::Eq(Taint::Variable(l), r)),
            )
            .collect(),
        );
    }

    fn with_judgements(&mut self, judgements: Vec<Judgement>) -> Self {
        let mut cloned = self.clone();
        cloned.judgements = judgements;
        cloned
    }

    fn solve_instantiation_constraints(&mut self) {
        let mut judgements_with_instantiation_constraints: HashMap<
            Vec<(TypeVariable, Taint)>,
            Vec<(TypeVariable, Taint)>,
        > = HashMap::new();
        let mut other_judgements: Vec<Judgement> = Vec::new();

        for judgement in &self.judgements {
            match judgement {
                Judgement::Le(Taint::Variable(l), Taint::Instantiate(r, insts)) => {
                    judgements_with_instantiation_constraints
                        .entry(insts.clone())
                        .or_insert(Vec::new())
                        .push((*l, *r.clone()));
                }
                _ => {
                    other_judgements.push(judgement.clone());
                }
            }
        }

        for (insts, constraints) in judgements_with_instantiation_constraints {
            self.solve_under_instantiations(insts, constraints, &other_judgements);
        }
    }
}
