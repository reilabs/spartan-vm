# Defunctionalization Pass for Noir Monomorphised AST

## Overview

This document describes the implementation of a defunctionalization pass that transforms Noir's monomorphised AST to eliminate higher-order functions. The pass converts function values into `u32` identifiers and replaces indirect calls with dispatches through generated `apply` functions.

**Input**: Monomorphised AST (`Program` with `Function`s containing `Expression`s)
**Output**: Defunctionalized monomorphised AST (no higher-order function calls)

## Background

### Noir Monomorphised AST Structure

The monomorphised AST (from `noirc_frontend/src/monomorphization/ast.rs`) contains:

```rust
pub struct Program {
    pub functions: Vec<Function>,
    pub globals: BTreeMap<GlobalId, (Ident, Expression)>,
    // ... debug info
}

pub struct Function {
    pub id: FuncId,
    pub name: String,
    pub parameters: Vec<(LocalId, bool, String, Type)>,
    pub body: Expression,
    pub return_type: Type,
    pub inline_type: InlineType,
    // ...
}

pub enum Expression {
    Ident(Ident),
    Call(Call),
    // ... other variants
}

pub struct Call {
    pub func: Box<Expression>,      // Can be Ident with Definition::Function, or computed
    pub arguments: Vec<Expression>,
    pub return_type: Type,
    pub location: Location,
}

pub enum Type {
    Function(Vec<Type>, Box<Type>, Box<Type>, bool),  // args, ret, env, unconstrained
    // ... other types
}

pub enum Definition {
    Local(LocalId),
    Function(FuncId),
    // ... others
}
```

### Key Insight: Function Value Representation

In the monomorphised AST, function values are represented as **tuples pairing constrained and unconstrained versions** (see [PR #9484](https://github.com/noir-lang/noir/pull/9484)):

```
function_value = (constrained_version, unconstrained_version)
```

For closures, each element is itself a closure tuple:
```
closure_value = (
    (constrained_func_id, constrained_env),
    (unconstrained_func_id, unconstrained_env)
)
```

At call sites, the appropriate version is selected based on the current runtime context:
- Index 0 for constrained (ACIR) execution
- Index 1 for unconstrained (Brillig) execution

Other key points:
- Direct calls have `Call.func` as `Expression::Ident` with `Definition::Function(FuncId)`
- Higher-order calls have `Call.func` as an expression that evaluates to a function value tuple
- `Type::Function(args, ret, env, unconstrained)` includes the closure environment type and unconstrained flag

## Implementation Plan

### Phase 1: Data Structures

#### 1.1 Function Signature for Grouping

```rust
/// Represents the signature of a lambda type for grouping apply functions.
/// Note: This excludes the `unconstrained` flag because we generate separate
/// apply functions for constrained and unconstrained calls with the same signature.
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
                return_type: *ret.clone(),
                env_type: *env.clone(),
            }),
            _ => None,
        }
    }
}
```

#### 1.2 Defunctionalization Context

```rust
/// Tracks all information needed during defunctionalization.
/// Constrained and unconstrained versions are tracked separately.
/// IDs are local to each (signature, runtime) pair for compact dispatch tables.
pub struct DefunctionalizationContext {
    /// Maps each lambda signature to its list of constrained function variants
    /// The index in the Vec IS the local u32 ID for that variant
    pub constrained_variants: HashMap<LambdaSignature, Vec<FuncId>>,

    /// Maps each lambda signature to its list of unconstrained function variants
    /// The index in the Vec IS the local u32 ID for that variant
    pub unconstrained_variants: HashMap<LambdaSignature, Vec<FuncId>>,

    /// Maps each lambda signature to its generated constrained apply function
    pub constrained_apply_functions: HashMap<LambdaSignature, FuncId>,

    /// Maps each lambda signature to its generated unconstrained apply function
    pub unconstrained_apply_functions: HashMap<LambdaSignature, FuncId>,

    /// Counter for generating new FuncIds
    pub next_func_id: u32,

    /// Counter for generating new LocalIds
    pub next_local_id: u32,
}

impl DefunctionalizationContext {
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
        variants.iter().position(|&id| id == func_id).map(|idx| idx as u32)
    }
}
```

**Why local IDs?**
- IDs are scoped to each `(LambdaSignature, runtime)` pair
- For a signature with 3 variants, IDs are always 0, 1, 2
- Enables compact dispatch: switch/jump tables, binary search, or direct indexing
- The same `FuncId` may have different local IDs in different signatures (rare but possible)

### Phase 2: Discovery Pass

Traverse the entire AST to discover:
1. All functions used as first-class values (in both constrained and unconstrained positions)
2. All higher-order call sites
3. Group functions by their `LambdaSignature`, separately for constrained and unconstrained

#### 2.1 Visitor Implementation

```rust
impl DefunctionalizationContext {
    /// Discover all function values and their usage sites
    pub fn discover(&mut self, program: &Program) {
        for function in &program.functions {
            self.discover_in_function(function);
        }
    }

    fn discover_in_expression(&mut self, expr: &Expression) {
        match expr {
            Expression::Ident(ident) => {
                // Check if this is a function reference not in call position
                if let Definition::Function(func_id) = &ident.definition {
                    if let Some(sig) = LambdaSignature::from_function_type(&ident.typ) {
                        let is_unconstrained = self.is_unconstrained_function_type(&ident.typ);
                        self.register_function_variant(*func_id, sig, is_unconstrained);
                    }
                }
            }
            Expression::Tuple(elements) => {
                // Handle function value tuples: (constrained, unconstrained)
                if self.is_function_value_tuple(elements) {
                    self.discover_function_value_tuple(elements);
                } else {
                    for elem in elements {
                        self.discover_in_expression(elem);
                    }
                }
            }
            Expression::Call(call) => {
                // Check if this is a higher-order call
                if self.is_higher_order_call(call) {
                    if let Some(sig) = LambdaSignature::from_function_type(&self.get_callee_type(call)) {
                        self.register_dynamic_dispatch_site(sig);
                    }
                }
                // Recurse into arguments
                for arg in &call.arguments {
                    self.discover_in_expression(arg);
                }
                // Recurse into func expression (for nested calls)
                self.discover_in_expression(&call.func);
            }
            // ... handle all other Expression variants recursively
        }
    }

    /// Check if a tuple represents a (constrained, unconstrained) function value pair
    fn is_function_value_tuple(&self, elements: &[Expression]) -> bool {
        if elements.len() != 2 {
            return false;
        }
        // Both elements should have function types (or closure tuple types)
        self.expr_has_function_type(&elements[0]) && self.expr_has_function_type(&elements[1])
    }

    /// Discover function variants from a (constrained, unconstrained) tuple
    fn discover_function_value_tuple(&mut self, elements: &[Expression]) {
        // First element: constrained version
        if let Some((func_id, sig)) = self.extract_function_from_expr(&elements[0]) {
            self.register_function_variant(func_id, sig, false);
        }
        // Second element: unconstrained version
        if let Some((func_id, sig)) = self.extract_function_from_expr(&elements[1]) {
            self.register_function_variant(func_id, sig, true);
        }
        // Recurse into nested expressions
        for elem in elements {
            self.discover_in_expression(elem);
        }
    }

    /// Determine if a call is higher-order (callee is not a direct FuncId)
    fn is_higher_order_call(&self, call: &Call) -> bool {
        match call.func.as_ref() {
            Expression::Ident(ident) => {
                !matches!(ident.definition, Definition::Function(_))
            }
            _ => true, // Any computed expression is higher-order
        }
    }

    fn register_function_variant(&mut self, func_id: FuncId, sig: LambdaSignature, unconstrained: bool) {
        let variants = if unconstrained {
            &mut self.unconstrained_variants
        } else {
            &mut self.constrained_variants
        };
        variants
            .entry(sig)
            .or_insert_with(Vec::new)
            .push(func_id);
    }

    fn is_unconstrained_function_type(&self, typ: &Type) -> bool {
        matches!(typ, Type::Function(_, _, _, true))
    }
}
```

### Phase 3: ID Assignment

With local IDs, explicit ID assignment is no longer needed. The index of each `FuncId`
in the variants vector **is** its local ID for that `(signature, runtime)` pair.

```rust
impl DefunctionalizationContext {
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
}
```

**Example**: For a signature with constrained variants `[f1, f2, f3]`:
- `f1` has local ID `0`
- `f2` has local ID `1`
- `f3` has local ID `2`

The same function in a different signature (or runtime) may have a different local ID.

### Phase 4: Apply Function Generation

For each `LambdaSignature`, generate **two** `apply` functions:
1. `apply_constrained_<sig_hash>` - dispatches to constrained function variants
2. `apply_unconstrained_<sig_hash>` - dispatches to unconstrained function variants

This separation ensures that constrained calls only dispatch to constrained implementations
and unconstrained calls only dispatch to unconstrained implementations.

#### 4.1 Apply Function Structure

```rust
/// Generate apply functions for both constrained and unconstrained variants
impl DefunctionalizationContext {
    pub fn generate_apply_functions(&mut self, program: &mut Program) {
        // Collect all signatures that need apply functions
        let all_signatures: HashSet<_> = self.constrained_variants.keys()
            .chain(self.unconstrained_variants.keys())
            .cloned()
            .collect();

        for sig in all_signatures {
            // Generate constrained apply function
            if let Some(variants) = self.constrained_variants.get(&sig) {
                let apply_func = self.create_apply_function(
                    &sig,
                    variants,
                    false, // constrained
                    program
                );
                self.constrained_apply_functions.insert(sig.clone(), apply_func.id);
                program.functions.push(apply_func);
            }

            // Generate unconstrained apply function
            if let Some(variants) = self.unconstrained_variants.get(&sig) {
                let apply_func = self.create_apply_function(
                    &sig,
                    variants,
                    true, // unconstrained
                    program
                );
                self.unconstrained_apply_functions.insert(sig.clone(), apply_func.id);
                program.functions.push(apply_func);
            }
        }
    }

    fn create_apply_function(
        &mut self,
        sig: &LambdaSignature,
        variants: &[FuncId],
        unconstrained: bool,
        program: &Program,
    ) -> Function {
        let apply_id = FuncId(self.next_func_id);
        self.next_func_id += 1;

        // Parameters: (func_id: u32, env: EnvType, ...original_params)
        let mut parameters = Vec::new();

        // First param: function identifier
        let func_id_param = (
            LocalId(self.fresh_local_id()),
            false, // not mutable
            "func_id".to_string(),
            Type::Integer(Signedness::Unsigned, IntegerBitSize::ThirtyTwo),
        );
        parameters.push(func_id_param.clone());

        // Second param: environment (if not Unit)
        let env_param = if sig.env_type != Type::Unit {
            let param = (
                LocalId(self.fresh_local_id()),
                false,
                "env".to_string(),
                sig.env_type.clone(),
            );
            parameters.push(param.clone());
            Some(param)
        } else {
            None
        };

        // Remaining params: original function parameters
        let arg_params: Vec<_> = sig.param_types.iter().enumerate().map(|(i, typ)| {
            (
                LocalId(self.fresh_local_id()),
                false,
                format!("arg{}", i),
                typ.clone(),
            )
        }).collect();
        parameters.extend(arg_params.clone());

        // Generate body: if-else chain dispatching to each variant
        let body = self.generate_dispatch_body(
            &func_id_param,
            &env_param,
            &arg_params,
            variants,
            sig,
            program,
        );

        // Name includes constrained/unconstrained prefix for clarity
        let name_prefix = if unconstrained { "apply_unconstrained" } else { "apply_constrained" };

        Function {
            id: apply_id,
            name: format!("{}_{}", name_prefix, self.signature_hash(sig)),
            parameters,
            body,
            return_type: sig.return_type.clone(),
            inline_type: InlineType::InlineAlways,
            unconstrained,
            // ... other fields with defaults
        }
    }
}
```

#### 4.2 Dispatch Body Generation

```rust
impl DefunctionalizationContext {
    /// Generate if-else chain for dispatching
    fn generate_dispatch_body(
        &mut self,
        func_id_param: &(LocalId, bool, String, Type),
        env_param: &Option<(LocalId, bool, String, Type)>,
        arg_params: &[(LocalId, bool, String, Type)],
        variants: &[FuncId],
        sig: &LambdaSignature,
        program: &Program,
    ) -> Expression {
        // Build if-else chain from last to first
        let mut result: Option<Expression> = None;

        for (idx, &func_id) in variants.iter().enumerate().rev() {
            let call_expr = self.generate_variant_call(
                func_id,
                env_param,
                arg_params,
                program,
            );

            if result.is_none() {
                // Last variant: no condition needed (else branch)
                result = Some(call_expr);
            } else {
                // Generate: if func_id == idx { call_variant } else { previous }
                let condition = Expression::Binary(Binary {
                    lhs: Box::new(self.local_id_to_ident(func_id_param)),
                    operator: BinaryOp::Equal,
                    rhs: Box::new(Expression::Literal(Literal::Integer(
                        FieldElement::from(idx as u128),
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

        result.unwrap_or_else(|| {
            // No variants: generate unreachable/panic
            self.generate_unreachable(sig)
        })
    }

    fn generate_variant_call(
        &self,
        func_id: FuncId,
        env_param: &Option<(LocalId, bool, String, Type)>,
        arg_params: &[(LocalId, bool, String, Type)],
        program: &Program,
    ) -> Expression {
        let func = &program.functions[func_id.0 as usize];

        // Build argument list
        let mut arguments = Vec::new();

        // Add environment if the target function expects it
        if let Some(env) = env_param {
            if self.function_takes_env(func) {
                arguments.push(self.local_id_to_ident(env));
            }
        }

        // Add remaining arguments
        for param in arg_params {
            arguments.push(self.local_id_to_ident(param));
        }

        Expression::Call(Call {
            func: Box::new(Expression::Ident(Ident {
                name: func.name.clone(),
                typ: self.get_function_type(func),
                definition: Definition::Function(func_id),
                // ... other fields
            })),
            arguments,
            return_type: func.return_type.clone(),
            location: Location::dummy(),
        })
    }
}
```

### Phase 5: AST Transformation

Transform the AST to:
1. Convert function value tuples `(constrained, unconstrained)` to `(u32, u32)` or `((u32, env), (u32, env))`
2. Replace higher-order calls with calls to the appropriate apply function
3. Maintain the tuple structure so runtime selection continues to work

#### 5.1 Expression Transformation

Since IDs are local to each `(signature, runtime)` pair, we need to know the target signature
when transforming function references. This is determined from the type context.

```rust
impl DefunctionalizationContext {
    pub fn transform_program(&mut self, program: &mut Program) {
        for function in &mut program.functions {
            let is_unconstrained = function.unconstrained;
            self.transform_function(function, is_unconstrained);
        }
    }

    fn transform_expression(
        &mut self,
        expr: &mut Expression,
        in_unconstrained_context: bool,
        target_sig: Option<&LambdaSignature>, // The signature context for ID lookup
    ) {
        match expr {
            Expression::Ident(ident) => {
                // Convert function references to local u32 IDs
                if let Definition::Function(func_id) = &ident.definition {
                    if let Some(sig) = target_sig.or_else(|| LambdaSignature::from_function_type(&ident.typ).as_ref()) {
                        if let Some(local_id) = self.get_local_id(*func_id, sig, in_unconstrained_context) {
                            *expr = Expression::Literal(Literal::Integer(
                                FieldElement::from(local_id as u128),
                                Type::Integer(Signedness::Unsigned, IntegerBitSize::ThirtyTwo),
                                ident.location,
                            ));
                        }
                    }
                }
            }
            Expression::Tuple(elements) => {
                // Handle function value tuples: (constrained, unconstrained)
                if self.is_function_value_tuple(elements) {
                    // Extract signature from the first element's type
                    let sig = self.get_expression_function_signature(&elements[0]);
                    self.transform_function_value_tuple(elements, sig.as_ref());
                } else {
                    for elem in elements {
                        self.transform_expression(elem, in_unconstrained_context, None);
                    }
                }
            }
            Expression::Call(call) => {
                if self.is_higher_order_call(call) {
                    self.transform_higher_order_call(call, in_unconstrained_context);
                } else {
                    // Direct call: just recurse into arguments
                    for arg in &mut call.arguments {
                        self.transform_expression(arg, in_unconstrained_context, None);
                    }
                }
            }
            Expression::ExtractTupleField(inner, index) => {
                // This is the runtime selection: index 0 = constrained, index 1 = unconstrained
                // Transform the inner expression, selection mechanism stays the same
                self.transform_expression(inner, in_unconstrained_context, target_sig);
            }
            // ... handle all other Expression variants recursively
        }
    }

    /// Transform a (constrained, unconstrained) function value tuple
    /// Each element is transformed with its respective runtime context and the same signature
    fn transform_function_value_tuple(
        &mut self,
        elements: &mut [Expression],
        sig: Option<&LambdaSignature>,
    ) {
        // Transform constrained version (index 0) with constrained context
        self.transform_expression(&mut elements[0], false, sig);
        // Transform unconstrained version (index 1) with unconstrained context
        self.transform_expression(&mut elements[1], true, sig);
    }

    fn transform_higher_order_call(&mut self, call: &mut Call, in_unconstrained_context: bool) {
        // Get the signature from the callee type
        let callee_type = self.get_expression_type(&call.func);
        let sig = LambdaSignature::from_function_type(&callee_type)
            .expect("Higher-order call must have function type");

        // Select the appropriate apply function based on context
        let apply_func_id = if in_unconstrained_context {
            self.unconstrained_apply_functions.get(&sig)
                .expect("Unconstrained apply function must exist for signature")
        } else {
            self.constrained_apply_functions.get(&sig)
                .expect("Constrained apply function must exist for signature")
        };

        // The callee expression should be selecting from a (constrained, unconstrained) tuple
        // We need to extract the appropriate version based on context
        let func_value_expr = std::mem::replace(
            &mut *call.func,
            Expression::Literal(Literal::Unit), // placeholder
        );

        // Extract the right version from the tuple and transform it
        // Pass the signature so local IDs are resolved correctly
        let selected_func = self.extract_runtime_version(func_value_expr, in_unconstrained_context);
        let mut selected_func = selected_func;
        self.transform_expression(&mut selected_func, in_unconstrained_context, Some(&sig));

        // Handle closure extraction: if it's a closure, extract (func_id, env)
        let (func_id_expr, env_expr) = if sig.env_type != Type::Unit {
            self.extract_closure_components(selected_func)
        } else {
            (selected_func, None)
        };

        // Build new argument list: (func_id, env?, ...original_args)
        let mut new_arguments = vec![func_id_expr];
        if let Some(env) = env_expr {
            new_arguments.push(env);
        }

        // Transform and add original arguments (no signature context needed for args)
        for arg in &mut call.arguments {
            self.transform_expression(arg, in_unconstrained_context, None);
        }
        new_arguments.append(&mut call.arguments);

        // Replace call target with appropriate apply function
        let name_prefix = if in_unconstrained_context { "apply_unconstrained" } else { "apply_constrained" };
        call.func = Box::new(Expression::Ident(Ident {
            name: format!("{}_{}", name_prefix, self.signature_hash(&sig)),
            typ: self.get_apply_function_type(&sig, in_unconstrained_context),
            definition: Definition::Function(*apply_func_id),
            // ... other fields
        }));
        call.arguments = new_arguments;
    }

    /// Extract the constrained (index 0) or unconstrained (index 1) version from a function tuple
    fn extract_runtime_version(&self, expr: Expression, unconstrained: bool) -> Expression {
        let index = if unconstrained { 1 } else { 0 };
        match expr {
            Expression::Tuple(mut elements) if elements.len() == 2 => {
                elements.remove(index)
            }
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

    fn extract_closure_components(&self, expr: Expression) -> (Expression, Option<Expression>) {
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
}
```

#### 5.2 Type Transformation

```rust
impl DefunctionalizationContext {
    /// Replace Type::Function with u32 (or tuple for closures)
    fn transform_type(&self, typ: &mut Type) {
        match typ {
            Type::Function(_, _, env, _) => {
                if **env == Type::Unit {
                    // Non-closure: just u32
                    *typ = Type::Integer(Signedness::Unsigned, IntegerBitSize::ThirtyTwo);
                } else {
                    // Closure: (u32, env_type)
                    let mut env_type = *env.clone();
                    self.transform_type(&mut env_type);
                    *typ = Type::Tuple(vec![
                        Type::Integer(Signedness::Unsigned, IntegerBitSize::ThirtyTwo),
                        env_type,
                    ]);
                }
            }
            Type::Array(len, elem) => {
                self.transform_type(elem);
            }
            Type::Tuple(elems) => {
                for elem in elems {
                    self.transform_type(elem);
                }
            }
            Type::Reference(inner, _) => {
                self.transform_type(inner);
            }
            // Primitive types: no change
            _ => {}
        }
    }
}
```

### Phase 6: Main Entry Point

```rust
/// Main defunctionalization pass
pub fn defunctionalize(mut program: Program) -> Program {
    let mut ctx = DefunctionalizationContext::new(&program);

    // Phase 2: Discover all function values and higher-order calls
    ctx.discover(&program);

    // Phase 3: Finalize variants (deduplicate, indices become local IDs)
    ctx.finalize_variants();

    // Phase 4: Generate apply functions (two per signature)
    ctx.generate_apply_functions(&mut program);

    // Phase 5: Transform the AST (using local IDs)
    ctx.transform_program(&mut program);

    // Phase 5.2: Transform all types
    ctx.transform_all_types(&mut program);

    program
}
```

## Edge Cases and Considerations

### 1. Empty Variant Sets

If a `LambdaSignature` is used in call position but has no discovered variants for a particular runtime:
- Generate a "dummy" apply function that panics/asserts false
- This handles dead code paths that the type system permits but are unreachable
- Example: A signature might have constrained variants but no unconstrained variants

### 2. Recursive Functions as Values

When a function recursively passes itself as a value:
- Ensure the function is registered as a variant of its own signature
- The u32 ID assignment handles this naturally

### 3. Constrained vs Unconstrained Separation

Function values are tuples `(constrained, unconstrained)`. We defunctionalize each separately:
- Two apply functions per signature: `apply_constrained_<hash>` and `apply_unconstrained_<hash>`
- Constrained calls dispatch through the constrained apply function
- Unconstrained calls dispatch through the unconstrained apply function
- The tuple structure is preserved: `(constrained_func, unconstrained_func)` becomes `(u32, u32)`

### 4. Nested Closures

Closures whose environment contains other closures:
- The environment type transformation handles this recursively
- Inner function types become `((u32, inner_env), (u32, inner_env))` tuples (preserving the constrained/unconstrained pairing)

### 5. Generic Environment Types

If environment types vary across variants of the same signature:
- This shouldn't happen after monomorphization
- Each closure instantiation has a concrete environment type

### 6. Mixed Availability of Variants

A signature may have variants in one runtime but not the other:
- If only constrained variants exist, only generate `apply_constrained_<hash>`
- If only unconstrained variants exist, only generate `apply_unconstrained_<hash>`
- If both exist, generate both apply functions

## Testing Strategy

1. **Unit tests**: Test each phase independently
   - Discovery correctly identifies all function values
   - ID assignment is deterministic
   - Apply function generation produces correct dispatch logic
   - AST transformation handles all expression types

2. **Integration tests**: End-to-end transformation
   - Simple higher-order function (map, fold)
   - Closures with captured variables
   - Nested higher-order functions
   - Multiple functions with same signature

3. **Verification**: Ensure semantic preservation
   - Compare execution results before/after defunctionalization
   - Verify no function values remain in output AST

## File Structure

```
src/monomorphization/
├── ast.rs                    # Existing AST definitions
├── mod.rs                    # Existing monomorphization
├── defunctionalize/
│   ├── mod.rs               # Main entry point and orchestration
│   ├── context.rs           # DefunctionalizationContext
│   ├── discovery.rs         # Phase 2: AST traversal and variant discovery
│   ├── apply_gen.rs         # Phase 4: Apply function generation
│   ├── transform.rs         # Phase 5: AST transformation
│   └── signature.rs         # LambdaSignature and hashing
```

## Summary

The defunctionalization pass transforms Noir's monomorphised AST in five phases:

1. **Setup**: Initialize context with program metadata
2. **Discovery**: Find all function values (as `(constrained, unconstrained)` tuples) and call sites, group by signature separately for each runtime
3. **Finalization**: Deduplicate variant lists; vector indices become local IDs
4. **Apply Generation**: Create **two** dispatcher functions per signature - one for constrained calls, one for unconstrained calls
5. **Transformation**: Rewrite AST to use local `u32` IDs and appropriate apply functions based on call context

### Key Design Decisions

- **Local IDs**: IDs are scoped to each `(signature, runtime)` pair, not global
  - For a signature with 3 constrained variants: IDs are 0, 1, 2
  - Enables compact dispatch tables (switch, jump table, or direct indexing)
  - The same `FuncId` may have different local IDs in different signatures
- **Dual apply functions**: Each signature gets `apply_constrained_<hash>` and `apply_unconstrained_<hash>`
- **Preserved tuple structure**: Function values remain as `(constrained, unconstrained)` tuples, but with `u32` IDs instead of function references
- **Context-aware dispatch**: Constrained code calls `apply_constrained_*`, unconstrained code calls `apply_unconstrained_*`

This approach ensures 100% correctness by:
- Generating separate apply functions per lambda type signature
- Using local IDs for efficient dispatch within each apply function
- Maintaining complete separation between constrained and unconstrained dispatch paths
- Preserving the runtime selection mechanism from the original monomorphised AST
- Handling closures with their environments correctly in both contexts
