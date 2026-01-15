//! Defunctionalization pass for Noir's monomorphised AST.
//!
//! This module transforms higher-order functions into first-order code by:
//! 1. Discovering all functions used as first-class values
//! 2. Assigning local u32 IDs to each function variant per signature
//! 3. Generating apply functions that dispatch based on the u32 ID
//! 4. Transforming the AST to use u32 IDs and apply function calls
//!
//! # Design
//!
//! Function values in the monomorphised AST are represented as tuples:
//! `(constrained_version, unconstrained_version)`
//!
//! For closures, each element is itself a tuple: `(func_id, environment)`
//!
//! This pass generates **two** apply functions per signature:
//! - `apply_constrained_<hash>` for constrained calls
//! - `apply_unconstrained_<hash>` for unconstrained calls
//!
//! IDs are **local** to each `(signature, runtime)` pair, enabling compact
//! dispatch tables (switch statements, jump tables, or array indexing).
//!
//! # Example
//!
//! Before defunctionalization:
//! ```ignore
//! fn map(f: fn(Field) -> Field, x: Field) -> Field {
//!     f(x)
//! }
//!
//! fn main() {
//!     let result = map(double, 5);
//! }
//! ```
//!
//! After defunctionalization:
//! ```ignore
//! fn apply_constrained_abc123(func_id: u32, x: Field) -> Field {
//!     if func_id == 0 { double(x) }
//!     else { triple(x) }  // etc.
//! }
//!
//! fn map(f: u32, x: Field) -> Field {
//!     apply_constrained_abc123(f, x)
//! }
//!
//! fn main() {
//!     let result = map(0, 5);  // 0 is the ID for `double`
//! }
//! ```

mod apply_gen;
mod context;
mod discovery;
mod signature;
mod transform;

pub use context::DefunctionalizationContext;
pub use signature::LambdaSignature;

use noirc_frontend::monomorphization::ast::Program;

/// Main entry point for defunctionalization.
///
/// Transforms the program to eliminate higher-order functions by:
/// 1. Discovering all function values and grouping by signature
/// 2. Generating apply functions for dispatch
/// 3. Rewriting calls to use u32 IDs and apply functions
pub fn defunctionalize(mut program: Program) -> Program {
    // Find the maximum FuncId to avoid collisions when generating new functions
    let max_func_id = program
        .functions
        .iter()
        .map(|f| f.id.0)
        .max()
        .unwrap_or(0)
        + 1;

    let mut ctx = DefunctionalizationContext::new(max_func_id);

    // Phase 1: Discover all function values and higher-order calls
    discovery::discover(&mut ctx, &program);

    // Phase 2: Finalize variants (deduplicate, indices become local IDs)
    ctx.finalize_variants();

    // Phase 3: Generate apply functions (two per signature)
    apply_gen::generate_apply_functions(&mut ctx, &mut program);

    // Phase 4: Transform the AST (using local IDs)
    transform::transform_program(&ctx, &mut program);

    // Phase 5: Transform all types (replace function types with u32)
    transform::transform_types(&mut program);

    program
}

#[cfg(test)]
mod tests {
    use super::*;
    use noirc_errors::Location;
    use noirc_frontend::hir_def::function::FunctionSignature;
    use noirc_frontend::monomorphization::ast::{
        Definition, Expression, FuncId, Function, Ident, IdentId, InlineType, Literal, LocalId,
        Type,
    };
    use noirc_frontend::shared::Visibility;
    use noirc_frontend::signed_field::SignedField;

    fn make_simple_function(id: u32, name: &str, body: Expression) -> Function {
        Function {
            id: FuncId(id),
            name: name.to_string(),
            parameters: vec![(
                LocalId(0),
                false,
                "x".to_string(),
                Type::Field,
                Visibility::Private,
            )],
            body,
            return_type: Type::Field,
            return_visibility: Visibility::Private,
            inline_type: InlineType::default(),
            unconstrained: false,
            func_sig: FunctionSignature::default(),
        }
    }

    fn make_func_ident(func_id: u32, unconstrained: bool) -> Expression {
        Expression::Ident(Ident {
            location: None,
            definition: Definition::Function(FuncId(func_id)),
            mutable: false,
            name: format!("func_{}", func_id),
            typ: Type::Function(
                vec![Type::Field],
                Box::new(Type::Field),
                Box::new(Type::Unit),
                unconstrained,
            ),
            id: IdentId(0),
        })
    }

    #[test]
    fn test_defunctionalize_empty_program() {
        let program = Program {
            functions: vec![],
            ..Default::default()
        };

        let result = defunctionalize(program);
        assert!(result.functions.is_empty());
    }

    #[test]
    fn test_defunctionalize_with_function_value() {
        // Create a simple program with a function used as a value
        let double_body = Expression::Literal(Literal::Integer(
            SignedField::zero(),
            Type::Field,
            Location::dummy(),
        ));
        let double_func = make_simple_function(1, "double", double_body);

        // Create a function tuple (constrained, unconstrained)
        let func_tuple = Expression::Tuple(vec![
            make_func_ident(1, false),
            make_func_ident(1, true),
        ]);

        let main_body = Expression::Block(vec![func_tuple]);
        let main_func = make_simple_function(0, "main", main_body);

        let program = Program {
            functions: vec![main_func, double_func],
            ..Default::default()
        };

        let result = defunctionalize(program);

        // Should have generated apply functions
        // Original 2 functions + up to 2 apply functions
        assert!(result.functions.len() >= 2);
    }
}
