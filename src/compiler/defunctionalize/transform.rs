//! AST transformation for defunctionalization.
//!
//! This module transforms the AST to:
//! 1. Convert function value tuples `(constrained, unconstrained)` to `(u32, u32)`
//! 2. Replace higher-order calls with calls to the appropriate apply function
//! 3. Maintain the tuple structure so runtime selection continues to work

use noirc_errors::Location;
use noirc_frontend::ast::IntegerBitSize;
use noirc_frontend::monomorphization::ast::{
    Call, Definition, Expression, Function, Ident, IdentId, LValue, Literal, Program, Type,
};
use noirc_frontend::shared::Signedness;
use noirc_frontend::signed_field::SignedField;

use super::{context::DefunctionalizationContext, signature::LambdaSignature};

/// Transform the entire program to use apply functions and u32 IDs.
pub fn transform_program(ctx: &DefunctionalizationContext, program: &mut Program) {
    for function in &mut program.functions {
        let is_unconstrained = function.unconstrained;
        transform_function(ctx, function, is_unconstrained);
    }
}

fn transform_function(
    ctx: &DefunctionalizationContext,
    function: &mut Function,
    unconstrained: bool,
) {
    transform_expression(ctx, &mut function.body, unconstrained, None);
}

fn transform_expression(
    ctx: &DefunctionalizationContext,
    expr: &mut Expression,
    in_unconstrained_context: bool,
    target_sig: Option<&LambdaSignature>,
) {
    match expr {
        Expression::Ident(_) => {
            transform_ident(ctx, expr, in_unconstrained_context, target_sig);
        }
        Expression::Literal(lit) => {
            transform_literal(ctx, lit, in_unconstrained_context);
        }
        Expression::Block(exprs) => {
            for e in exprs {
                transform_expression(ctx, e, in_unconstrained_context, None);
            }
        }
        Expression::Unary(unary) => {
            transform_expression(ctx, &mut unary.rhs, in_unconstrained_context, None);
        }
        Expression::Binary(binary) => {
            transform_expression(ctx, &mut binary.lhs, in_unconstrained_context, None);
            transform_expression(ctx, &mut binary.rhs, in_unconstrained_context, None);
        }
        Expression::Index(index) => {
            transform_expression(ctx, &mut index.collection, in_unconstrained_context, None);
            transform_expression(ctx, &mut index.index, in_unconstrained_context, None);
        }
        Expression::Cast(cast) => {
            transform_expression(ctx, &mut cast.lhs, in_unconstrained_context, None);
        }
        Expression::For(for_expr) => {
            transform_expression(ctx, &mut for_expr.start_range, in_unconstrained_context, None);
            transform_expression(ctx, &mut for_expr.end_range, in_unconstrained_context, None);
            transform_expression(ctx, &mut for_expr.block, in_unconstrained_context, None);
        }
        Expression::Loop(loop_body) => {
            transform_expression(ctx, loop_body, in_unconstrained_context, None);
        }
        Expression::While(while_expr) => {
            transform_expression(ctx, &mut while_expr.condition, in_unconstrained_context, None);
            transform_expression(ctx, &mut while_expr.body, in_unconstrained_context, None);
        }
        Expression::If(if_expr) => {
            transform_expression(ctx, &mut if_expr.condition, in_unconstrained_context, None);
            transform_expression(ctx, &mut if_expr.consequence, in_unconstrained_context, None);
            if let Some(alt) = &mut if_expr.alternative {
                transform_expression(ctx, alt, in_unconstrained_context, None);
            }
        }
        Expression::Match(match_expr) => {
            // variable_to_match is (LocalId, String), not an expression
            for case in &mut match_expr.cases {
                transform_expression(ctx, &mut case.branch, in_unconstrained_context, None);
            }
            if let Some(default_body) = &mut match_expr.default_case {
                transform_expression(ctx, default_body, in_unconstrained_context, None);
            }
        }
        Expression::Tuple(elements) => {
            // Check if this is a function value tuple: (constrained, unconstrained)
            if is_function_value_tuple(elements) {
                // Extract signature from the first element's type
                let sig = get_expression_function_signature(&elements[0]);
                transform_function_value_tuple(ctx, elements, sig.as_ref());
            } else {
                for elem in elements {
                    transform_expression(ctx, elem, in_unconstrained_context, None);
                }
            }
        }
        Expression::ExtractTupleField(inner, _) => {
            // This is the runtime selection: index 0 = constrained, index 1 = unconstrained
            // Transform the inner expression, selection mechanism stays the same
            transform_expression(ctx, inner, in_unconstrained_context, target_sig);
        }
        Expression::Call(call) => {
            if is_higher_order_call(call) {
                transform_higher_order_call(ctx, call, in_unconstrained_context);
            } else {
                // Direct call: just recurse into arguments
                transform_expression(ctx, &mut call.func, in_unconstrained_context, None);
                for arg in &mut call.arguments {
                    transform_expression(ctx, arg, in_unconstrained_context, None);
                }
            }
        }
        Expression::Let(let_expr) => {
            transform_expression(ctx, &mut let_expr.expression, in_unconstrained_context, None);
        }
        Expression::Constrain(constrain_expr, _location, msg_opt) => {
            transform_expression(ctx, constrain_expr, in_unconstrained_context, None);
            if let Some(msg_box) = msg_opt {
                transform_expression(ctx, &mut msg_box.0, in_unconstrained_context, None);
            }
        }
        Expression::Assign(assign) => {
            transform_lvalue(ctx, &mut assign.lvalue, in_unconstrained_context);
            transform_expression(ctx, &mut assign.expression, in_unconstrained_context, None);
        }
        Expression::Semi(inner) => {
            transform_expression(ctx, inner, in_unconstrained_context, None);
        }
        Expression::Clone(inner) => {
            transform_expression(ctx, inner, in_unconstrained_context, None);
        }
        Expression::Drop(inner) => {
            transform_expression(ctx, inner, in_unconstrained_context, None);
        }
        Expression::Break | Expression::Continue => {}
    }
}

fn transform_ident(
    ctx: &DefunctionalizationContext,
    expr: &mut Expression,
    in_unconstrained_context: bool,
    target_sig: Option<&LambdaSignature>,
) {
    // Extract ident info first to avoid borrow conflicts
    let (func_id, sig, location) = match expr {
        Expression::Ident(ident) => {
            if let Definition::Function(func_id) = &ident.definition {
                let sig = target_sig
                    .cloned()
                    .or_else(|| LambdaSignature::from_function_type(&ident.typ));
                (Some(*func_id), sig, ident.location)
            } else {
                return;
            }
        }
        _ => return,
    };

    // Convert function references to local u32 IDs
    if let (Some(func_id), Some(sig)) = (func_id, sig) {
        if let Some(local_id) = ctx.get_local_id(func_id, &sig, in_unconstrained_context) {
            *expr = Expression::Literal(Literal::Integer(
                SignedField::positive(local_id as u128),
                Type::Integer(Signedness::Unsigned, IntegerBitSize::ThirtyTwo),
                location.unwrap_or_else(Location::dummy),
            ));
        }
    }
}

fn transform_literal(
    ctx: &DefunctionalizationContext,
    lit: &mut Literal,
    in_unconstrained_context: bool,
) {
    match lit {
        Literal::Array(array_lit) | Literal::Slice(array_lit) => {
            for elem in &mut array_lit.contents {
                transform_expression(ctx, elem, in_unconstrained_context, None);
            }
        }
        Literal::FmtStr(_, _, expr) => {
            transform_expression(ctx, expr, in_unconstrained_context, None);
        }
        Literal::Integer(_, _, _) | Literal::Bool(_) | Literal::Unit | Literal::Str(_) => {}
    }
}

fn transform_lvalue(
    ctx: &DefunctionalizationContext,
    lvalue: &mut LValue,
    in_unconstrained_context: bool,
) {
    match lvalue {
        LValue::Ident(_) => {}
        LValue::Index { array, index, .. } => {
            transform_lvalue(ctx, array, in_unconstrained_context);
            transform_expression(ctx, index, in_unconstrained_context, None);
        }
        LValue::MemberAccess { object, .. } => {
            transform_lvalue(ctx, object, in_unconstrained_context);
        }
        LValue::Dereference { reference, .. } => {
            transform_lvalue(ctx, reference, in_unconstrained_context);
        }
        LValue::Clone(inner) => {
            transform_lvalue(ctx, inner, in_unconstrained_context);
        }
    }
}

/// Transform a (constrained, unconstrained) function value tuple.
/// Each element is transformed with its respective runtime context and the same signature.
fn transform_function_value_tuple(
    ctx: &DefunctionalizationContext,
    elements: &mut [Expression],
    sig: Option<&LambdaSignature>,
) {
    // Transform constrained version (index 0) with constrained context
    transform_expression(ctx, &mut elements[0], false, sig);
    // Transform unconstrained version (index 1) with unconstrained context
    transform_expression(ctx, &mut elements[1], true, sig);
}

/// Transform a higher-order call to use the apply function.
fn transform_higher_order_call(
    ctx: &DefunctionalizationContext,
    call: &mut Call,
    in_unconstrained_context: bool,
) {
    // Get the signature from the callee type
    let callee_type = get_expression_type(&call.func);
    let sig = callee_type
        .as_ref()
        .and_then(LambdaSignature::from_function_type);

    let Some(sig) = sig else {
        // Not a function type, just transform normally
        transform_expression(ctx, &mut call.func, in_unconstrained_context, None);
        for arg in &mut call.arguments {
            transform_expression(ctx, arg, in_unconstrained_context, None);
        }
        return;
    };

    // Get the apply function for this signature
    let apply_func_id = ctx.get_apply_function(&sig, in_unconstrained_context);
    let Some(apply_func_id) = apply_func_id else {
        // No apply function (shouldn't happen if discovery was correct)
        transform_expression(ctx, &mut call.func, in_unconstrained_context, None);
        for arg in &mut call.arguments {
            transform_expression(ctx, arg, in_unconstrained_context, None);
        }
        return;
    };

    // Extract the function value and transform it
    let func_value_expr = std::mem::replace(
        &mut *call.func,
        Expression::Literal(Literal::Unit),
    );

    // Extract the right version from the tuple based on context
    let selected_func = extract_runtime_version(func_value_expr, in_unconstrained_context);
    let mut selected_func = selected_func;
    transform_expression(ctx, &mut selected_func, in_unconstrained_context, Some(&sig));

    // Handle closure extraction: if it's a closure, extract (func_id, env)
    let (func_id_expr, env_expr) = if sig.has_environment() {
        extract_closure_components(selected_func)
    } else {
        (selected_func, None)
    };

    // Build new argument list: (func_id, env?, ...original_args)
    let mut new_arguments = vec![func_id_expr];
    if let Some(env) = env_expr {
        new_arguments.push(env);
    }

    // Transform and add original arguments
    for arg in &mut call.arguments {
        transform_expression(ctx, arg, in_unconstrained_context, None);
    }
    new_arguments.append(&mut call.arguments);

    // Replace call target with appropriate apply function
    let name_prefix = if in_unconstrained_context {
        "apply_unconstrained"
    } else {
        "apply_constrained"
    };

    call.func = Box::new(Expression::Ident(Ident {
        location: None,
        definition: Definition::Function(apply_func_id),
        mutable: false,
        name: format!("{}_{}", name_prefix, sig.hash_string()),
        typ: build_apply_function_type(&sig, in_unconstrained_context),
        id: IdentId(0),
    }));
    call.arguments = new_arguments;
}

/// Check if a tuple represents a (constrained, unconstrained) function value pair.
fn is_function_value_tuple(elements: &[Expression]) -> bool {
    if elements.len() != 2 {
        return false;
    }
    // Both elements should have function types
    expr_has_function_type(&elements[0]) && expr_has_function_type(&elements[1])
}

/// Check if an expression has a function type.
fn expr_has_function_type(expr: &Expression) -> bool {
    matches!(get_expression_type(expr), Some(Type::Function(..)))
}

/// Get the type of an expression (simplified - only handles common cases).
fn get_expression_type(expr: &Expression) -> Option<Type> {
    match expr {
        Expression::Ident(ident) => Some(ident.typ.clone()),
        Expression::Tuple(elements) => {
            // For closure tuples, check if first element is a function
            if let Some(Expression::Ident(ident)) = elements.first() {
                if let Type::Function(..) = &ident.typ {
                    return Some(ident.typ.clone());
                }
            }
            None
        }
        Expression::Call(call) => Some(call.return_type.clone()),
        Expression::If(if_expr) => Some(if_expr.typ.clone()),
        Expression::Match(match_expr) => Some(match_expr.typ.clone()),
        _ => None,
    }
}

/// Get the function signature from an expression's type.
fn get_expression_function_signature(expr: &Expression) -> Option<LambdaSignature> {
    get_expression_type(expr)
        .as_ref()
        .and_then(LambdaSignature::from_function_type)
}

/// Check if a call is higher-order (callee is not a direct function reference).
fn is_higher_order_call(call: &Call) -> bool {
    match call.func.as_ref() {
        Expression::Ident(ident) => !matches!(ident.definition, Definition::Function(_)),
        _ => true, // Any computed expression is higher-order
    }
}

/// Extract the constrained (index 0) or unconstrained (index 1) version from a function tuple.
fn extract_runtime_version(expr: Expression, unconstrained: bool) -> Expression {
    let index = if unconstrained { 1 } else { 0 };
    match expr {
        Expression::Tuple(mut elements) if elements.len() == 2 => elements.remove(index),
        Expression::ExtractTupleField(inner, idx) if idx == index => {
            // Already extracting the right version
            Expression::ExtractTupleField(inner, idx)
        }
        other => {
            // Runtime value: generate tuple field extraction
            Expression::ExtractTupleField(Box::new(other), index)
        }
    }
}

/// Extract (func_id, env) from a closure expression.
fn extract_closure_components(expr: Expression) -> (Expression, Option<Expression>) {
    match expr {
        Expression::Tuple(mut elements) if elements.len() == 2 => {
            let env = elements.pop();
            let func_id = elements.pop().unwrap();
            (func_id, env)
        }
        other => {
            // Runtime closure value: generate tuple field extractions
            let inner = Box::new(other);
            (
                Expression::ExtractTupleField(inner.clone(), 0),
                Some(Expression::ExtractTupleField(inner, 1)),
            )
        }
    }
}

/// Build the type for an apply function.
fn build_apply_function_type(sig: &LambdaSignature, unconstrained: bool) -> Type {
    let mut param_types = vec![Type::Integer(Signedness::Unsigned, IntegerBitSize::ThirtyTwo)];

    if sig.has_environment() {
        param_types.push(sig.env_type.clone());
    }

    param_types.extend(sig.param_types.clone());

    Type::Function(
        param_types,
        Box::new(sig.return_type.clone()),
        Box::new(Type::Unit),
        unconstrained,
    )
}

/// Transform all types in the program to replace function types with u32.
pub fn transform_types(program: &mut Program) {
    for function in &mut program.functions {
        // Transform parameter types
        for (_, _, _, typ, _) in &mut function.parameters {
            transform_type(typ);
        }
        // Transform return type
        transform_type(&mut function.return_type);
        // Transform types in the body
        transform_expression_types(&mut function.body);
    }
}

fn transform_type(typ: &mut Type) {
    match typ {
        Type::Function(_, _, env, _) => {
            if **env == Type::Unit {
                // Non-closure: just u32
                *typ = Type::Integer(Signedness::Unsigned, IntegerBitSize::ThirtyTwo);
            } else {
                // Closure: (u32, env_type)
                let mut env_type = (**env).clone();
                transform_type(&mut env_type);
                *typ = Type::Tuple(vec![
                    Type::Integer(Signedness::Unsigned, IntegerBitSize::ThirtyTwo),
                    env_type,
                ]);
            }
        }
        Type::Array(_, elem) => {
            transform_type(elem);
        }
        Type::Slice(elem) => {
            transform_type(elem);
        }
        Type::Tuple(elems) => {
            for elem in elems {
                transform_type(elem);
            }
        }
        Type::Reference(inner, _) => {
            transform_type(inner);
        }
        // Primitive types: no change
        _ => {}
    }
}

fn transform_expression_types(expr: &mut Expression) {
    match expr {
        Expression::Ident(ident) => {
            transform_type(&mut ident.typ);
        }
        Expression::Block(exprs) => {
            for e in exprs {
                transform_expression_types(e);
            }
        }
        Expression::Unary(unary) => {
            transform_type(&mut unary.result_type);
            transform_expression_types(&mut unary.rhs);
        }
        Expression::Binary(binary) => {
            transform_expression_types(&mut binary.lhs);
            transform_expression_types(&mut binary.rhs);
        }
        Expression::Index(index) => {
            transform_type(&mut index.element_type);
            transform_expression_types(&mut index.collection);
            transform_expression_types(&mut index.index);
        }
        Expression::Cast(cast) => {
            transform_type(&mut cast.r#type);
            transform_expression_types(&mut cast.lhs);
        }
        Expression::For(for_expr) => {
            transform_expression_types(&mut for_expr.start_range);
            transform_expression_types(&mut for_expr.end_range);
            transform_expression_types(&mut for_expr.block);
        }
        Expression::Loop(loop_body) => {
            transform_expression_types(loop_body);
        }
        Expression::While(while_expr) => {
            transform_expression_types(&mut while_expr.condition);
            transform_expression_types(&mut while_expr.body);
        }
        Expression::If(if_expr) => {
            transform_type(&mut if_expr.typ);
            transform_expression_types(&mut if_expr.condition);
            transform_expression_types(&mut if_expr.consequence);
            if let Some(alt) = &mut if_expr.alternative {
                transform_expression_types(alt);
            }
        }
        Expression::Match(match_expr) => {
            transform_type(&mut match_expr.typ);
            // variable_to_match is (LocalId, String), not an expression
            for case in &mut match_expr.cases {
                transform_expression_types(&mut case.branch);
            }
            if let Some(default_body) = &mut match_expr.default_case {
                transform_expression_types(default_body);
            }
        }
        Expression::Tuple(elements) => {
            for elem in elements {
                transform_expression_types(elem);
            }
        }
        Expression::ExtractTupleField(inner, _) => {
            transform_expression_types(inner);
        }
        Expression::Call(call) => {
            transform_type(&mut call.return_type);
            transform_expression_types(&mut call.func);
            for arg in &mut call.arguments {
                transform_expression_types(arg);
            }
        }
        Expression::Let(let_expr) => {
            transform_expression_types(&mut let_expr.expression);
        }
        Expression::Constrain(constrain_expr, _, msg_opt) => {
            transform_expression_types(constrain_expr);
            if let Some(msg_box) = msg_opt {
                transform_expression_types(&mut msg_box.0);
            }
        }
        Expression::Assign(assign) => {
            transform_expression_types(&mut assign.expression);
        }
        Expression::Semi(inner) => {
            transform_expression_types(inner);
        }
        Expression::Clone(inner) => {
            transform_expression_types(inner);
        }
        Expression::Drop(inner) => {
            transform_expression_types(inner);
        }
        Expression::Literal(_) | Expression::Break | Expression::Continue => {}
    }
}
