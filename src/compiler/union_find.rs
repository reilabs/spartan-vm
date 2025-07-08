use crate::compiler::taint_analysis::{Judgement, Taint, TaintType, TypeVariable};
use std::cell::RefCell;
use std::collections::HashMap;

/// Union-Find data structure for type variables with taint mapping
#[derive(Debug, Clone)]
pub struct UnionFind {
    parent: RefCell<HashMap<TypeVariable, TypeVariable>>,
    rank: RefCell<HashMap<TypeVariable, usize>>,
    taint_mapping: RefCell<HashMap<TypeVariable, Taint>>,
}

impl UnionFind {
    pub fn new() -> Self {
        UnionFind {
            parent: RefCell::new(HashMap::new()),
            rank: RefCell::new(HashMap::new()),
            taint_mapping: RefCell::new(HashMap::new()),
        }
    }

    /// Find the representative (root) of the equivalence class containing x
    pub fn find(&self, x: TypeVariable) -> TypeVariable {
        let mut parent = self.parent.borrow_mut();
        let mut rank = self.rank.borrow_mut();

        if !parent.contains_key(&x) {
            parent.insert(x, x);
            rank.insert(x, 0);
            return x;
        }

        // Find the root iteratively (no recursion)
        let mut current = x;
        let mut path = Vec::new();

        while parent[&current] != current {
            path.push(current);
            current = parent[&current];
        }

        // Path compression: update all nodes on the path to point directly to root
        for node in path {
            parent.insert(node, current);
        }

        current
    }

    /// Union two equivalence classes
    pub fn union(&mut self, x: TypeVariable, y: TypeVariable) {
        let root_x = self.find(x);
        let root_y = self.find(y);

        if root_x == root_y {
            return;
        }

        // Union by rank first
        let mut parent = self.parent.borrow_mut();
        let mut rank = self.rank.borrow_mut();
        let rank_x = rank[&root_x];
        let rank_y = rank[&root_y];

        let new_root;
        if rank_x < rank_y {
            parent.insert(root_x, root_y);
            new_root = root_y;
        } else if rank_x > rank_y {
            parent.insert(root_y, root_x);
            new_root = root_x;
        } else {
            parent.insert(root_y, root_x);
            rank.insert(root_x, rank_x + 1);
            new_root = root_x;
        }

        // Now handle taint merging
        let taint_x = self.taint_mapping.borrow().get(&root_x).cloned();
        let taint_y = self.taint_mapping.borrow().get(&root_y).cloned();

        // Merge taints if both representatives had taint values
        let mut mapping = self.taint_mapping.borrow_mut();
        match (taint_x, taint_y) {
            (Some(taint_x), Some(taint_y)) => {
                let merged_taint = taint_x.union(&taint_y);
                mapping.insert(new_root, merged_taint);
            }
            (Some(taint_x), None) => {
                mapping.insert(new_root, taint_x);
            }
            (None, Some(taint_y)) => {
                mapping.insert(new_root, taint_y);
            }
            (None, None) => {
                // If neither had taint, no mapping is created
            }
        }
    }

    /// Check if two variables are in the same equivalence class
    pub fn same_class(&self, x: TypeVariable, y: TypeVariable) -> bool {
        self.find(x) == self.find(y)
    }

    /// Get all variables in the same equivalence class as x
    pub fn get_class(&self, x: TypeVariable) -> Vec<TypeVariable> {
        let parent = self.parent.borrow();
        let mut result = Vec::new();
        for (var, _) in parent.iter() {
            if parent[var] == parent[&x] {
                result.push(*var);
            }
        }
        result
    }

    /// Set the taint value for a representative
    #[must_use]
    pub fn set_taint(&mut self, representative: TypeVariable, taint: Taint) -> Option<Taint> {
        let mut mapping = self.taint_mapping.borrow_mut();
        let old_taint = mapping.get(&representative).cloned();
        mapping.insert(representative, taint);
        old_taint
    }

    /// Get the taint value for a representative, if it exists
    pub fn get_taint(&self, representative: TypeVariable) -> Option<Taint> {
        let mapping = self.taint_mapping.borrow();
        mapping.get(&representative).cloned()
    }

    /// Get the taint value for any variable by finding its representative first
    pub fn get_taint_for_variable(&self, variable: TypeVariable) -> Option<Taint> {
        let representative = self.find(variable);
        self.get_taint(representative)
    }

    /// Recursively substitute variables with their representatives in a taint
    pub fn substitute_variables(&self, taint: &Taint) -> Taint {
        match taint {
            Taint::Variable(var) => {
                let representative = self.find(*var);
                // Check if the representative has a concrete taint value
                if let Some(concrete_taint) = self.get_taint(representative) {
                    self.substitute_variables(&concrete_taint)
                } else {
                    Taint::Variable(representative)
                }
            }
            Taint::Pure => Taint::Pure,
            Taint::Witness => Taint::Witness,
            Taint::Union(left, right) => {
                let left_substituted = self.substitute_variables(left);
                let right_substituted = self.substitute_variables(right);
                Taint::Union(Box::new(left_substituted), Box::new(right_substituted))
            }
        }
    }

    pub fn substitute_taint_type(&self, taint_type: &TaintType) -> TaintType {
        match taint_type {
            TaintType::Primitive(taint) => TaintType::Primitive(self.substitute_variables(taint)),
            TaintType::NestedImmutable(taint, inner) => TaintType::NestedImmutable(
                self.substitute_variables(taint),
                Box::new(self.substitute_taint_type(inner)),
            ),
            TaintType::NestedMutable(taint, inner) => TaintType::NestedMutable(
                self.substitute_variables(taint),
                Box::new(self.substitute_taint_type(inner)),
            ),
        }
    }

    pub fn substitute_judgement(&self, judgement: &Judgement) -> Judgement {
        match judgement {
            Judgement::Le(l, r) => {
                let l_substituted = self.substitute_variables(l);
                let r_substituted = self.substitute_variables(r);
                Judgement::Le(l_substituted, r_substituted)
            }
            Judgement::Eq(l, r) => {
                let l_substituted = self.substitute_variables(l);
                let r_substituted = self.substitute_variables(r);
                Judgement::Eq(l_substituted, r_substituted)
            }
        }
    }
}
