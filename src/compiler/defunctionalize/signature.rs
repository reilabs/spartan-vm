//! Lambda signature for grouping apply functions.
//!
//! A `LambdaSignature` represents the type signature of a function value,
//! excluding the `unconstrained` flag since we generate separate apply
//! functions for constrained and unconstrained calls.

use std::hash::{Hash, Hasher};

use noirc_frontend::monomorphization::ast::Type;

/// Represents the signature of a lambda type for grouping apply functions.
///
/// The `unconstrained` flag is intentionally excluded because we generate
/// separate apply functions for constrained and unconstrained variants.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LambdaSignature {
    /// Parameter types (excluding environment)
    pub param_types: Vec<Type>,
    /// Return type
    pub return_type: Type,
    /// Environment type (Unit for non-closures)
    pub env_type: Type,
}

impl LambdaSignature {
    /// Extract signature from a Type::Function (ignoring unconstrained flag)
    pub fn from_function_type(typ: &Type) -> Option<Self> {
        match typ {
            Type::Function(params, ret, env, _unconstrained) => Some(LambdaSignature {
                param_types: params.clone(),
                return_type: (**ret).clone(),
                env_type: (**env).clone(),
            }),
            _ => None,
        }
    }

    /// Check if this signature has a non-trivial environment (i.e., is a closure)
    pub fn has_environment(&self) -> bool {
        self.env_type != Type::Unit
    }

    /// Generate a unique hash string for naming apply functions
    pub fn hash_string(&self) -> String {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        self.hash(&mut hasher);
        format!("{:016x}", hasher.finish())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_signature_from_function_type() {
        let func_type = Type::Function(
            vec![Type::Field, Type::Bool],
            Box::new(Type::Field),
            Box::new(Type::Unit),
            false,
        );

        let sig = LambdaSignature::from_function_type(&func_type).unwrap();
        assert_eq!(sig.param_types, vec![Type::Field, Type::Bool]);
        assert_eq!(sig.return_type, Type::Field);
        assert_eq!(sig.env_type, Type::Unit);
        assert!(!sig.has_environment());
    }

    #[test]
    fn test_signature_with_environment() {
        let env_type = Type::Tuple(vec![Type::Field, Type::Bool]);
        let func_type = Type::Function(
            vec![Type::Field],
            Box::new(Type::Bool),
            Box::new(env_type.clone()),
            true,
        );

        let sig = LambdaSignature::from_function_type(&func_type).unwrap();
        assert!(sig.has_environment());
        assert_eq!(sig.env_type, env_type);
    }

    #[test]
    fn test_unconstrained_flag_ignored() {
        let constrained = Type::Function(
            vec![Type::Field],
            Box::new(Type::Field),
            Box::new(Type::Unit),
            false,
        );
        let unconstrained = Type::Function(
            vec![Type::Field],
            Box::new(Type::Field),
            Box::new(Type::Unit),
            true,
        );

        let sig1 = LambdaSignature::from_function_type(&constrained).unwrap();
        let sig2 = LambdaSignature::from_function_type(&unconstrained).unwrap();

        // Signatures should be equal despite different unconstrained flags
        assert_eq!(sig1, sig2);
    }
}
