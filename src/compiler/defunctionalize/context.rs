//! Defunctionalization context tracking variants and apply functions.

use std::collections::{HashMap, HashSet};

use noirc_frontend::monomorphization::ast::{FuncId, LocalId};

use super::signature::LambdaSignature;

/// Tracks all information needed during defunctionalization.
///
/// Constrained and unconstrained versions are tracked separately.
/// IDs are local to each (signature, runtime) pair for compact dispatch tables.
pub struct DefunctionalizationContext {
    /// Maps each lambda signature to its list of constrained function variants.
    /// The index in the Vec IS the local u32 ID for that variant.
    pub constrained_variants: HashMap<LambdaSignature, Vec<FuncId>>,

    /// Maps each lambda signature to its list of unconstrained function variants.
    /// The index in the Vec IS the local u32 ID for that variant.
    pub unconstrained_variants: HashMap<LambdaSignature, Vec<FuncId>>,

    /// Maps each lambda signature to its generated constrained apply function
    pub constrained_apply_functions: HashMap<LambdaSignature, FuncId>,

    /// Maps each lambda signature to its generated unconstrained apply function
    pub unconstrained_apply_functions: HashMap<LambdaSignature, FuncId>,

    /// Counter for generating new FuncIds
    next_func_id: u32,

    /// Counter for generating new LocalIds
    next_local_id: u32,
}

impl DefunctionalizationContext {
    /// Create a new defunctionalization context.
    ///
    /// The `max_func_id` should be one greater than the highest existing FuncId
    /// in the program to avoid collisions when generating new functions.
    pub fn new(max_func_id: u32) -> Self {
        Self {
            constrained_variants: HashMap::new(),
            unconstrained_variants: HashMap::new(),
            constrained_apply_functions: HashMap::new(),
            unconstrained_apply_functions: HashMap::new(),
            next_func_id: max_func_id,
            next_local_id: 0,
        }
    }

    /// Register a function as a variant for a given signature and runtime.
    pub fn register_variant(&mut self, func_id: FuncId, sig: LambdaSignature, unconstrained: bool) {
        let variants = if unconstrained {
            &mut self.unconstrained_variants
        } else {
            &mut self.constrained_variants
        };
        variants.entry(sig).or_default().push(func_id);
    }

    /// Deduplicate variants within each (signature, runtime) pair.
    /// Called after discovery to ensure each FuncId appears at most once per list.
    /// The final index becomes the local ID.
    pub fn finalize_variants(&mut self) {
        for variants in self.constrained_variants.values_mut() {
            Self::deduplicate(variants);
        }
        for variants in self.unconstrained_variants.values_mut() {
            Self::deduplicate(variants);
        }
    }

    fn deduplicate(variants: &mut Vec<FuncId>) {
        let mut seen = HashSet::new();
        variants.retain(|id| seen.insert(*id));
    }

    /// Get the local ID for a function within a specific signature and runtime.
    /// Returns None if the function is not a variant of this signature/runtime.
    pub fn get_local_id(
        &self,
        func_id: FuncId,
        sig: &LambdaSignature,
        unconstrained: bool,
    ) -> Option<u32> {
        let variants = if unconstrained {
            self.unconstrained_variants.get(sig)?
        } else {
            self.constrained_variants.get(sig)?
        };
        variants
            .iter()
            .position(|&id| id == func_id)
            .map(|idx| idx as u32)
    }

    /// Get all signatures that have variants (either constrained or unconstrained)
    pub fn all_signatures(&self) -> HashSet<LambdaSignature> {
        self.constrained_variants
            .keys()
            .chain(self.unconstrained_variants.keys())
            .cloned()
            .collect()
    }

    /// Get the constrained variants for a signature
    pub fn get_constrained_variants(&self, sig: &LambdaSignature) -> Option<&[FuncId]> {
        self.constrained_variants.get(sig).map(|v| v.as_slice())
    }

    /// Get the unconstrained variants for a signature
    pub fn get_unconstrained_variants(&self, sig: &LambdaSignature) -> Option<&[FuncId]> {
        self.unconstrained_variants.get(sig).map(|v| v.as_slice())
    }

    /// Allocate a fresh FuncId for a new apply function
    pub fn fresh_func_id(&mut self) -> FuncId {
        let id = FuncId(self.next_func_id);
        self.next_func_id += 1;
        id
    }

    /// Allocate a fresh LocalId for a new local variable
    pub fn fresh_local_id(&mut self) -> LocalId {
        let id = LocalId(self.next_local_id);
        self.next_local_id += 1;
        id
    }

    /// Register a generated apply function for a signature
    pub fn register_apply_function(
        &mut self,
        sig: LambdaSignature,
        func_id: FuncId,
        unconstrained: bool,
    ) {
        if unconstrained {
            self.unconstrained_apply_functions.insert(sig, func_id);
        } else {
            self.constrained_apply_functions.insert(sig, func_id);
        }
    }

    /// Get the apply function for a signature and runtime
    pub fn get_apply_function(
        &self,
        sig: &LambdaSignature,
        unconstrained: bool,
    ) -> Option<FuncId> {
        if unconstrained {
            self.unconstrained_apply_functions.get(sig).copied()
        } else {
            self.constrained_apply_functions.get(sig).copied()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use noirc_frontend::monomorphization::ast::Type;

    fn make_signature() -> LambdaSignature {
        LambdaSignature {
            param_types: vec![Type::Field],
            return_type: Type::Field,
            env_type: Type::Unit,
        }
    }

    #[test]
    fn test_register_and_get_local_id() {
        let mut ctx = DefunctionalizationContext::new(100);
        let sig = make_signature();

        ctx.register_variant(FuncId(1), sig.clone(), false);
        ctx.register_variant(FuncId(2), sig.clone(), false);
        ctx.register_variant(FuncId(3), sig.clone(), false);
        ctx.finalize_variants();

        assert_eq!(ctx.get_local_id(FuncId(1), &sig, false), Some(0));
        assert_eq!(ctx.get_local_id(FuncId(2), &sig, false), Some(1));
        assert_eq!(ctx.get_local_id(FuncId(3), &sig, false), Some(2));
        assert_eq!(ctx.get_local_id(FuncId(4), &sig, false), None);
    }

    #[test]
    fn test_separate_constrained_unconstrained() {
        let mut ctx = DefunctionalizationContext::new(100);
        let sig = make_signature();

        ctx.register_variant(FuncId(1), sig.clone(), false); // constrained
        ctx.register_variant(FuncId(2), sig.clone(), true); // unconstrained
        ctx.finalize_variants();

        assert_eq!(ctx.get_local_id(FuncId(1), &sig, false), Some(0));
        assert_eq!(ctx.get_local_id(FuncId(1), &sig, true), None);
        assert_eq!(ctx.get_local_id(FuncId(2), &sig, true), Some(0));
        assert_eq!(ctx.get_local_id(FuncId(2), &sig, false), None);
    }

    #[test]
    fn test_deduplication() {
        let mut ctx = DefunctionalizationContext::new(100);
        let sig = make_signature();

        ctx.register_variant(FuncId(1), sig.clone(), false);
        ctx.register_variant(FuncId(1), sig.clone(), false); // duplicate
        ctx.register_variant(FuncId(2), sig.clone(), false);
        ctx.finalize_variants();

        let variants = ctx.get_constrained_variants(&sig).unwrap();
        assert_eq!(variants.len(), 2);
        assert_eq!(ctx.get_local_id(FuncId(1), &sig, false), Some(0));
        assert_eq!(ctx.get_local_id(FuncId(2), &sig, false), Some(1));
    }
}
