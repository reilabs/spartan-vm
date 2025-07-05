use std::collections::HashMap;
use crate::compiler::taint_analysis::{TypeVariable, Taint, TaintType, Judgement, TaintAnalysis};
use crate::compiler::union_find::UnionFind;

/// Constraint solver for taint analysis
pub struct ConstraintSolver {
    definite_assignments: HashMap<TypeVariable, Taint>,
    unification: UnionFind,
    judgements: Vec<Judgement>,
    // TODO: Add fields for subtyping and instantiation constraints
}

impl ConstraintSolver {
    pub fn new(taint_analysis: &TaintAnalysis) -> Self {
        ConstraintSolver {
            definite_assignments: HashMap::new(),
            unification: UnionFind::new(),
            judgements: taint_analysis.get_judgements_data().to_vec(),
        }
    }

    /// Main entry point for constraint solving
    pub fn solve(&mut self) {
        // TODO: Implement constraint solving logic
        self.inline_equalities();
        println!("\n\n=== Inlined equalities ===");
        println!("{}", self.judgements_string());
        println!("Number of judgements: {}", self.num_judgements());

    }

    pub fn judgements_string(&self) -> String {
        self.judgements.iter()
            .map(|j| match j {
                Judgement::Eq(l, r) => {
                    let l_substituted = self.substitute_variables(l);
                    let r_substituted = self.substitute_variables(r);
                    format!("{} = {}", l_substituted.to_string(), r_substituted.to_string())
                },
                Judgement::Le(l, r) => {
                    let l_substituted = self.substitute_variables(l);
                    let r_substituted = self.substitute_variables(r);
                    format!("{} ≤ {}", l_substituted.to_string(), r_substituted.to_string())
                },
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    /// Recursively substitute variables with their representatives in a taint
    fn substitute_variables(&self, taint: &Taint) -> Taint {
        match taint {
            Taint::Variable(var) => {
                let representative = self.unification.find(*var);
                // Check if the representative has a concrete taint value
                if let Some(concrete_taint) = self.unification.get_taint(representative) {
                    self.substitute_variables(&concrete_taint)
                } else {
                    Taint::Variable(representative)
                }
            },
            Taint::Pure => Taint::Pure,
            Taint::Witness => Taint::Witness,
            Taint::Meet(left, right) => {
                let left_substituted = self.substitute_variables(left);
                let right_substituted = self.substitute_variables(right);
                Taint::Meet(Box::new(left_substituted), Box::new(right_substituted))
            },
            Taint::Instantiate(var, substitutions) => {
                let representative = self.unification.find(*var);
                let substituted_subs = substitutions
                    .iter()
                    .map(|(from, to)| {
                        let from_representative = self.unification.find(*from);
                        let to_substituted = self.substitute_variables(to);
                        (from_representative, to_substituted)
                    })
                    .collect::<Vec<_>>();
                Taint::Instantiate(representative, substituted_subs)
            },
        }
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
                _ => new_judgements.push(judgement.clone()),
            }
        }
        self.judgements = new_judgements;
    }
}