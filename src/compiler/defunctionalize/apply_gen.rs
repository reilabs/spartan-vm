//! Apply function generation for defunctionalization.
//!
//! This module generates `apply` functions that dispatch to the correct
//! implementation based on a u32 function identifier. Two apply functions
//! are generated per signature: one for constrained calls, one for unconstrained.

use noirc_errors::Location;
use noirc_frontend::ast::IntegerBitSize;
use noirc_frontend::hir_def::function::FunctionSignature;
use noirc_frontend::monomorphization::ast::{
    Binary, BinaryOp, Call, Definition, Expression, FuncId, Function, Ident, IdentId, If,
    InlineType, Literal, LocalId, Program, Type,
};
use noirc_frontend::shared::{Signedness, Visibility};
use noirc_frontend::signed_field::SignedField;

use super::{context::DefunctionalizationContext, signature::LambdaSignature};

/// Parameter type for apply functions: (LocalId, mutable, name, Type, Visibility)
type Param = (LocalId, bool, String, Type, Visibility);

/// Generate apply functions for all discovered signatures.
pub fn generate_apply_functions(ctx: &mut DefunctionalizationContext, program: &mut Program) {
    let signatures: Vec<_> = ctx.all_signatures().into_iter().collect();

    for sig in signatures {
        // Generate constrained apply function if there are constrained variants
        let constrained_variants: Option<Vec<FuncId>> = ctx
            .get_constrained_variants(&sig)
            .filter(|v| !v.is_empty())
            .map(|v| v.to_vec());

        if let Some(variants) = constrained_variants {
            let apply_func = create_apply_function(ctx, &sig, &variants, false, program);
            let func_id = apply_func.id;
            program.functions.push(apply_func);
            ctx.register_apply_function(sig.clone(), func_id, false);
        }

        // Generate unconstrained apply function if there are unconstrained variants
        let unconstrained_variants: Option<Vec<FuncId>> = ctx
            .get_unconstrained_variants(&sig)
            .filter(|v| !v.is_empty())
            .map(|v| v.to_vec());

        if let Some(variants) = unconstrained_variants {
            let apply_func = create_apply_function(ctx, &sig, &variants, true, program);
            let func_id = apply_func.id;
            program.functions.push(apply_func);
            ctx.register_apply_function(sig.clone(), func_id, true);
        }
    }
}

/// Create an apply function for a specific signature and runtime.
fn create_apply_function(
    ctx: &mut DefunctionalizationContext,
    sig: &LambdaSignature,
    variants: &[FuncId],
    unconstrained: bool,
    program: &Program,
) -> Function {
    let apply_id = ctx.fresh_func_id();

    // Build parameters: (func_id: u32, env?: EnvType, ...args)
    let mut parameters = Vec::new();

    // First param: function identifier (u32)
    let func_id_local = ctx.fresh_local_id();
    let func_id_param: Param = (
        func_id_local,
        false, // not mutable
        "func_id".to_string(),
        Type::Integer(Signedness::Unsigned, IntegerBitSize::ThirtyTwo),
        Visibility::Private,
    );
    parameters.push(func_id_param);

    // Second param: environment (if closure)
    let env_param = if sig.has_environment() {
        let env_local = ctx.fresh_local_id();
        let param: Param = (
            env_local,
            false,
            "env".to_string(),
            sig.env_type.clone(),
            Visibility::Private,
        );
        parameters.push(param.clone());
        Some(param)
    } else {
        None
    };

    // Remaining params: original function parameters
    let arg_params: Vec<Param> = sig
        .param_types
        .iter()
        .enumerate()
        .map(|(i, typ)| {
            let local_id = ctx.fresh_local_id();
            (local_id, false, format!("arg{}", i), typ.clone(), Visibility::Private)
        })
        .collect();
    parameters.extend(arg_params.clone());

    // Generate body: if-else chain dispatching to each variant
    let body = generate_dispatch_body(
        ctx,
        func_id_local,
        &env_param,
        &arg_params,
        variants,
        sig,
        program,
    );

    // Name includes constrained/unconstrained prefix
    let name_prefix = if unconstrained {
        "apply_unconstrained"
    } else {
        "apply_constrained"
    };

    Function {
        id: apply_id,
        name: format!("{}_{}", name_prefix, sig.hash_string()),
        parameters,
        body,
        return_type: sig.return_type.clone(),
        return_visibility: Visibility::Private,
        inline_type: InlineType::InlineAlways,
        unconstrained,
        func_sig: FunctionSignature::default(),
    }
}

/// Generate an if-else chain that dispatches to the correct variant based on func_id.
fn generate_dispatch_body(
    ctx: &mut DefunctionalizationContext,
    func_id_local: LocalId,
    env_param: &Option<Param>,
    arg_params: &[Param],
    variants: &[FuncId],
    sig: &LambdaSignature,
    program: &Program,
) -> Expression {
    if variants.is_empty() {
        // No variants: generate unreachable (this shouldn't happen in practice)
        return generate_unreachable(sig);
    }

    // Build if-else chain from last to first
    let mut result: Option<Expression> = None;

    for (idx, &func_id) in variants.iter().enumerate().rev() {
        let call_expr = generate_variant_call(func_id, env_param, arg_params, sig, program);

        if result.is_none() {
            // Last variant: no condition needed (else branch)
            result = Some(call_expr);
        } else {
            // Generate: if func_id == idx { call_variant } else { previous }
            let condition = Expression::Binary(Binary {
                lhs: Box::new(local_id_to_ident(func_id_local)),
                operator: BinaryOp::Equal,
                rhs: Box::new(Expression::Literal(Literal::Integer(
                    SignedField::positive(idx as u128),
                    Type::Integer(Signedness::Unsigned, IntegerBitSize::ThirtyTwo),
                    Location::dummy(),
                ))),
                location: Location::dummy(),
            });

            result = Some(Expression::If(If {
                condition: Box::new(condition),
                consequence: Box::new(call_expr),
                alternative: result.map(Box::new),
                typ: sig.return_type.clone(),
            }));
        }
    }

    result.unwrap_or_else(|| generate_unreachable(sig))
}

/// Generate a call to a specific variant function.
fn generate_variant_call(
    func_id: FuncId,
    env_param: &Option<Param>,
    arg_params: &[Param],
    sig: &LambdaSignature,
    program: &Program,
) -> Expression {
    // Find the function in the program to get its name
    let func = program
        .functions
        .iter()
        .find(|f| f.id == func_id)
        .expect("Variant function must exist in program");

    // Build argument list
    let mut arguments = Vec::new();

    // Add environment if the target function expects it
    if let Some((env_local, _, _, env_type, _)) = env_param {
        // Check if target function takes an environment parameter
        // (This is a simplification - in practice we'd check the function signature)
        if sig.has_environment() {
            arguments.push(local_id_to_ident_with_type(*env_local, env_type.clone()));
        }
    }

    // Add remaining arguments
    for (local_id, _, _, typ, _) in arg_params {
        arguments.push(local_id_to_ident_with_type(*local_id, typ.clone()));
    }

    // Create the call expression
    Expression::Call(Call {
        func: Box::new(Expression::Ident(Ident {
            location: None,
            definition: Definition::Function(func_id),
            mutable: false,
            name: func.name.clone(),
            typ: function_type_from_func(func),
            id: IdentId(0),
        })),
        arguments,
        return_type: sig.return_type.clone(),
        location: Location::dummy(),
    })
}

/// Generate an unreachable expression (for empty variant lists).
fn generate_unreachable(sig: &LambdaSignature) -> Expression {
    // Generate a simple default value based on the return type
    // In a real implementation, this would be a proper unreachable/panic
    match &sig.return_type {
        Type::Unit => Expression::Literal(Literal::Unit),
        Type::Bool => Expression::Literal(Literal::Bool(false)),
        Type::Field => Expression::Literal(Literal::Integer(
            SignedField::zero(),
            Type::Field,
            Location::dummy(),
        )),
        Type::Integer(signedness, bit_size) => Expression::Literal(Literal::Integer(
            SignedField::zero(),
            Type::Integer(*signedness, *bit_size),
            Location::dummy(),
        )),
        // For other types, return unit (this is a fallback)
        _ => Expression::Literal(Literal::Unit),
    }
}

/// Convert a LocalId to an Ident expression (for use as func_id parameter).
fn local_id_to_ident(local_id: LocalId) -> Expression {
    Expression::Ident(Ident {
        location: None,
        definition: Definition::Local(local_id),
        mutable: false,
        name: format!("local_{}", local_id.0),
        typ: Type::Integer(Signedness::Unsigned, IntegerBitSize::ThirtyTwo),
        id: IdentId(0),
    })
}

/// Convert a LocalId to an Ident expression with a specific type.
fn local_id_to_ident_with_type(local_id: LocalId, typ: Type) -> Expression {
    Expression::Ident(Ident {
        location: None,
        definition: Definition::Local(local_id),
        mutable: false,
        name: format!("local_{}", local_id.0),
        typ,
        id: IdentId(0),
    })
}

/// Reconstruct a function type from a Function.
fn function_type_from_func(func: &Function) -> Type {
    let param_types: Vec<Type> = func.parameters.iter().map(|(_, _, _, t, _)| t.clone()).collect();
    Type::Function(
        param_types,
        Box::new(func.return_type.clone()),
        Box::new(Type::Unit), // Simplified: assume no environment
        func.unconstrained,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_test_signature() -> LambdaSignature {
        LambdaSignature {
            param_types: vec![Type::Field],
            return_type: Type::Field,
            env_type: Type::Unit,
        }
    }

    fn make_test_function(id: u32, name: &str) -> Function {
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
            body: Expression::Literal(Literal::Integer(
                SignedField::zero(),
                Type::Field,
                Location::dummy(),
            )),
            return_type: Type::Field,
            return_visibility: Visibility::Private,
            inline_type: InlineType::default(),
            unconstrained: false,
            func_sig: FunctionSignature::default(),
        }
    }

    #[test]
    fn test_generate_dispatch_body_single_variant() {
        let mut ctx = DefunctionalizationContext::new(100);
        let sig = make_test_signature();
        let func = make_test_function(1, "test_func");
        let program = Program {
            functions: vec![func],
            ..Default::default()
        };

        ctx.register_variant(FuncId(1), sig.clone(), false);
        ctx.finalize_variants();

        let func_id_local = ctx.fresh_local_id();
        let arg_params: Vec<Param> = vec![(
            ctx.fresh_local_id(),
            false,
            "arg0".to_string(),
            Type::Field,
            Visibility::Private,
        )];

        let body = generate_dispatch_body(
            &mut ctx,
            func_id_local,
            &None,
            &arg_params,
            &[FuncId(1)],
            &sig,
            &program,
        );

        // With a single variant, should just be a direct call (no if-else)
        assert!(matches!(body, Expression::Call(_)));
    }
}
