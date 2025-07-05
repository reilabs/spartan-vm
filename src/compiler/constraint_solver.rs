use crate::compiler::taint_analysis::{Judgement, Taint, TaintAnalysis, TaintType, TypeVariable};
use crate::compiler::union_find::UnionFind;
use std::collections::HashMap;

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
        self.blow_up_le_of_meet();
        println!("\n\n=== Blow up le of meet ===");
        println!("{}", self.judgements_string());
        println!("Number of judgements: {}", self.num_judgements());
        self.simplify_le_pure();
        println!("\n\n=== Simplified le of pure ===");
        println!("{}", self.judgements_string());
        println!("Number of judgements: {}", self.num_judgements());
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
}
