//! Discovery pass for finding all function values and higher-order calls.
//!
//! This module traverses the monomorphised AST to discover:
//! 1. All functions used as first-class values (in both constrained and unconstrained positions)
//! 2. All higher-order call sites
//! 3. Groups functions by their `LambdaSignature`, separately for constrained and unconstrained

use noirc_frontend::monomorphization::ast::{
    Definition, Expression, FuncId, Function, Ident, LValue, Literal, Program, Type,
};

use super::{context::DefunctionalizationContext, signature::LambdaSignature};

/// Discover all function values and higher-order call sites in the program.
pub fn discover(ctx: &mut DefunctionalizationContext, program: &Program) {
    for function in &program.functions {
        discover_in_function(ctx, function);
    }
}

fn discover_in_function(ctx: &mut DefunctionalizationContext, function: &Function) {
    discover_in_expression(ctx, &function.body);
}

fn discover_in_expression(ctx: &mut DefunctionalizationContext, expr: &Expression) {
    match expr {
        Expression::Ident(ident) => {
            discover_in_ident(ctx, ident);
        }
        Expression::Literal(lit) => {
            discover_in_literal(ctx, lit);
        }
        Expression::Block(exprs) => {
            for e in exprs {
                discover_in_expression(ctx, e);
            }
        }
        Expression::Unary(unary) => {
            discover_in_expression(ctx, &unary.rhs);
        }
        Expression::Binary(binary) => {
            discover_in_expression(ctx, &binary.lhs);
            discover_in_expression(ctx, &binary.rhs);
        }
        Expression::Index(index) => {
            discover_in_expression(ctx, &index.collection);
            discover_in_expression(ctx, &index.index);
        }
        Expression::Cast(cast) => {
            discover_in_expression(ctx, &cast.lhs);
        }
        Expression::For(for_expr) => {
            discover_in_expression(ctx, &for_expr.start_range);
            discover_in_expression(ctx, &for_expr.end_range);
            discover_in_expression(ctx, &for_expr.block);
        }
        Expression::Loop(loop_body) => {
            discover_in_expression(ctx, loop_body);
        }
        Expression::While(while_expr) => {
            discover_in_expression(ctx, &while_expr.condition);
            discover_in_expression(ctx, &while_expr.body);
        }
        Expression::If(if_expr) => {
            discover_in_expression(ctx, &if_expr.condition);
            discover_in_expression(ctx, &if_expr.consequence);
            if let Some(alt) = &if_expr.alternative {
                discover_in_expression(ctx, alt);
            }
        }
        Expression::Match(match_expr) => {
            // variable_to_match is (LocalId, String), not an expression
            for case in &match_expr.cases {
                discover_in_expression(ctx, &case.branch);
            }
            if let Some(default_body) = &match_expr.default_case {
                discover_in_expression(ctx, default_body);
            }
        }
        Expression::Tuple(elements) => {
            // Check if this is a function value tuple: (constrained, unconstrained)
            if is_function_value_tuple(elements) {
                discover_function_value_tuple(ctx, elements);
            } else {
                for elem in elements {
                    discover_in_expression(ctx, elem);
                }
            }
        }
        Expression::ExtractTupleField(inner, _) => {
            discover_in_expression(ctx, inner);
        }
        Expression::Call(call) => {
            // Discover in the callee expression
            discover_in_expression(ctx, &call.func);
            // Discover in arguments
            for arg in &call.arguments {
                discover_in_expression(ctx, arg);
            }
        }
        Expression::Let(let_expr) => {
            discover_in_expression(ctx, &let_expr.expression);
        }
        Expression::Constrain(constrain_expr, _location, msg_opt) => {
            discover_in_expression(ctx, constrain_expr);
            if let Some(msg_box) = msg_opt {
                discover_in_expression(ctx, &msg_box.0);
            }
        }
        Expression::Assign(assign) => {
            discover_in_lvalue(ctx, &assign.lvalue);
            discover_in_expression(ctx, &assign.expression);
        }
        Expression::Semi(inner) => {
            discover_in_expression(ctx, inner);
        }
        Expression::Clone(inner) => {
            discover_in_expression(ctx, inner);
        }
        Expression::Drop(inner) => {
            discover_in_expression(ctx, inner);
        }
        Expression::Break | Expression::Continue => {}
    }
}

fn discover_in_ident(ctx: &mut DefunctionalizationContext, ident: &Ident) {
    // Check if this is a function reference used as a value
    if let Definition::Function(func_id) = &ident.definition {
        if let Some(sig) = LambdaSignature::from_function_type(&ident.typ) {
            let is_unconstrained = is_unconstrained_function_type(&ident.typ);
            ctx.register_variant(*func_id, sig, is_unconstrained);
        }
    }
}

fn discover_in_literal(ctx: &mut DefunctionalizationContext, lit: &Literal) {
    match lit {
        Literal::Array(array_lit) | Literal::Slice(array_lit) => {
            for elem in &array_lit.contents {
                discover_in_expression(ctx, elem);
            }
        }
        Literal::FmtStr(_, _, expr) => {
            discover_in_expression(ctx, expr);
        }
        Literal::Integer(_, _, _) | Literal::Bool(_) | Literal::Unit | Literal::Str(_) => {}
    }
}

fn discover_in_lvalue(ctx: &mut DefunctionalizationContext, lvalue: &LValue) {
    match lvalue {
        LValue::Ident(_) => {}
        LValue::Index { array, index, .. } => {
            discover_in_lvalue(ctx, array);
            discover_in_expression(ctx, index);
        }
        LValue::MemberAccess { object, .. } => {
            discover_in_lvalue(ctx, object);
        }
        LValue::Dereference { reference, .. } => {
            discover_in_lvalue(ctx, reference);
        }
        LValue::Clone(inner) => {
            discover_in_lvalue(ctx, inner);
        }
    }
}

/// Check if a tuple represents a (constrained, unconstrained) function value pair
fn is_function_value_tuple(elements: &[Expression]) -> bool {
    if elements.len() != 2 {
        return false;
    }
    // Both elements should have function types (or be closure tuples with function types)
    expr_has_function_type(&elements[0]) && expr_has_function_type(&elements[1])
}

/// Check if an expression has a function type
fn expr_has_function_type(expr: &Expression) -> bool {
    matches!(get_expression_type(expr), Some(Type::Function(..))) || is_closure_tuple_expr(expr)
}

/// Check if an expression is a closure tuple (func_id, env)
fn is_closure_tuple_expr(expr: &Expression) -> bool {
    if let Expression::Tuple(elements) = expr {
        if elements.len() == 2 {
            // First element should be a function reference
            if let Expression::Ident(ident) = &elements[0] {
                return matches!(ident.definition, Definition::Function(_));
            }
        }
    }
    false
}

/// Get the type of an expression (simplified - only handles common cases)
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
        _ => None,
    }
}

/// Discover function variants from a (constrained, unconstrained) tuple
fn discover_function_value_tuple(ctx: &mut DefunctionalizationContext, elements: &[Expression]) {
    // First element: constrained version
    if let Some((func_id, sig)) = extract_function_from_expr(&elements[0]) {
        ctx.register_variant(func_id, sig, false);
    }
    // Second element: unconstrained version
    if let Some((func_id, sig)) = extract_function_from_expr(&elements[1]) {
        ctx.register_variant(func_id, sig, true);
    }
    // Recurse into nested expressions for any other function values
    for elem in elements {
        discover_in_expression(ctx, elem);
    }
}

/// Extract a function ID and signature from an expression that represents a function value
fn extract_function_from_expr(expr: &Expression) -> Option<(FuncId, LambdaSignature)> {
    match expr {
        Expression::Ident(ident) => {
            if let Definition::Function(func_id) = &ident.definition {
                let sig = LambdaSignature::from_function_type(&ident.typ)?;
                Some((*func_id, sig))
            } else {
                None
            }
        }
        // For closure tuples (func_id, env), extract from first element
        Expression::Tuple(elements) if elements.len() == 2 => {
            extract_function_from_expr(&elements[0])
        }
        _ => None,
    }
}

fn is_unconstrained_function_type(typ: &Type) -> bool {
    matches!(typ, Type::Function(_, _, _, true))
}

#[cfg(test)]
mod tests {
    use super::*;
    use noirc_frontend::monomorphization::ast::IdentId;

    fn make_func_ident(func_id: u32, unconstrained: bool) -> Ident {
        Ident {
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
        }
    }

    #[test]
    fn test_discover_function_ident() {
        let mut ctx = DefunctionalizationContext::new(100);
        let ident = make_func_ident(1, false);

        discover_in_ident(&mut ctx, &ident);
        ctx.finalize_variants();

        let sig = LambdaSignature {
            param_types: vec![Type::Field],
            return_type: Type::Field,
            env_type: Type::Unit,
        };

        assert_eq!(ctx.get_local_id(FuncId(1), &sig, false), Some(0));
    }

    #[test]
    fn test_is_function_value_tuple() {
        let constrained_ident = Expression::Ident(make_func_ident(1, false));
        let unconstrained_ident = Expression::Ident(make_func_ident(2, true));

        assert!(is_function_value_tuple(&[
            constrained_ident,
            unconstrained_ident
        ]));
    }
}
