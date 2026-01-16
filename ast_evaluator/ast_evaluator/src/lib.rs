//! A simple, auditable interpreter for Noir's monomorphized AST.
//!
//! This crate provides a direct interpreter that executes Noir programs
//! from their monomorphized AST representation. The interpreter is designed
//! to be as simple and straightforward as possible, prioritizing auditability
//! over performance.
//!
//! # Design Principles
//!
//! - **Simplicity**: No optimizations or clever tricks. Every operation is
//!   implemented in the most direct way possible.
//! - **Auditability**: The code should be easy to read and verify for correctness.
//! - **Directness**: We interpret the AST directly without any intermediate
//!   transformations.
//!
//! # Usage
//!
//! ```ignore
//! use std::path::PathBuf;
//! use ast_evaluator::{run_project, RunOptions};
//!
//! let result = run_project(PathBuf::from("./my_noir_project"), &RunOptions::default());
//! ```

use std::collections::BTreeMap;
use std::path::PathBuf;

use acvm::AcirField;
use ark_bn254::Fr as Field;
use ark_ff::{BigInteger, One, PrimeField, Zero};
use fm::FileManager;
use nargo::workspace::Workspace;
use nargo_toml::PackageSelection::All;
use noirc_abi::{input_parser::Format, input_parser::InputValue, Abi, AbiType};
use noirc_frontend::{
    ast::{BinaryOpKind, IntegerBitSize, UnaryOp},
    hir::ParsedFiles,
    hir_def::expr::Constructor,
    monomorphization::ast::{
        self, Definition, Expression, FuncId, GlobalId, Literal, LocalId, Program, Type,
    },
    shared::Signedness,
};
use thiserror::Error;

/// Errors that can occur during AST evaluation.
#[derive(Debug, Error)]
pub enum EvalError {
    #[error("Undefined variable: {0}")]
    UndefinedVariable(String),

    #[error("Undefined function: {0}")]
    UndefinedFunction(u32),

    #[error("Undefined global: {0}")]
    UndefinedGlobal(u32),

    #[error("Type mismatch: expected {expected}, got {actual}")]
    TypeMismatch { expected: String, actual: String },

    #[error("Index out of bounds: index {index}, length {length}")]
    IndexOutOfBounds { index: usize, length: usize },

    #[error("Division by zero")]
    DivisionByZero,

    #[error("Assertion failed: {0}")]
    AssertionFailed(String),

    #[error("Invalid cast from {from} to {to}")]
    InvalidCast { from: String, to: String },

    #[error("Missing parameter: {0}")]
    MissingParameter(String),

    #[error("Invalid input value for parameter {param}: {reason}")]
    InvalidInputValue { param: String, reason: String },

    #[error("Unsupported operation: {0}")]
    UnsupportedOperation(String),

    #[error("Break outside of loop")]
    BreakOutsideLoop,

    #[error("Continue outside of loop")]
    ContinueOutsideLoop,

    #[error("Integer overflow")]
    IntegerOverflow,
}

/// The result type for evaluation operations.
pub type EvalResult<T> = Result<T, EvalError>;

/// Errors that can occur when running a Noir project.
#[derive(Debug, Error)]
pub enum RunError {
    #[error("Failed to find Nargo.toml: {0}")]
    ManifestNotFound(String),

    #[error("Failed to resolve workspace: {0}")]
    WorkspaceResolutionFailed(String),

    #[error("Expected exactly one package in the project, got: {0}")]
    MultiplePackages(usize),

    #[error("Compilation errors:\n{0}")]
    CompilationFailed(String),

    #[error("No main function found")]
    NoMainFunction,

    #[error("Monomorphization failed: {0}")]
    MonomorphizationFailed(String),

    #[error("Failed to read Prover.toml: {0}")]
    ProverTomlReadFailed(String),

    #[error("Failed to parse Prover.toml: {0}")]
    ProverTomlParseFailed(String),

    #[error("Evaluation error: {0}")]
    EvaluationFailed(#[from] EvalError),

    #[error("Return value mismatch: expected {expected:?}, got {actual:?}")]
    ReturnValueMismatch { expected: Value, actual: Value },

    #[error("Expected return value specified but function has no return type")]
    UnexpectedReturnValue,
}

/// Options for running a Noir project.
#[derive(Debug, Clone, Default)]
pub struct RunOptions {
    /// If true, check the return value against the `return` field in Prover.toml.
    pub check_return_value: bool,
}

/// Result of running a Noir project.
#[derive(Debug, Clone)]
pub struct RunResult {
    /// The return value of the main function.
    pub return_value: Value,
    /// The expected return value from Prover.toml, if any.
    pub expected_return: Option<Value>,
}

/// Run a Noir project from the given root directory.
///
/// This function:
/// 1. Loads the Noir project from the root directory
/// 2. Compiles it to monomorphized AST
/// 3. Parses Prover.toml for input parameters
/// 4. Executes the program using the interpreter
/// 5. Optionally checks the return value against the expected value
///
/// # Arguments
///
/// * `project_root` - The root directory of the Noir project
/// * `options` - Options for running the project
///
/// # Returns
///
/// A `RunResult` containing the return value and optional expected value.
pub fn run_project(project_root: PathBuf, options: &RunOptions) -> Result<RunResult, RunError> {
    // Step 1: Load the project
    let toml_path = nargo_toml::get_package_manifest(&project_root)
        .map_err(|e| RunError::ManifestNotFound(e.to_string()))?;

    let workspace = nargo_toml::resolve_workspace_from_toml(&toml_path, All, None)
        .map_err(|e| RunError::WorkspaceResolutionFailed(e.to_string()))?;

    let (file_manager, parsed_files) = parse_workspace(&workspace);

    let package = if workspace.members.len() != 1 {
        return Err(RunError::MultiplePackages(workspace.members.len()));
    } else {
        &workspace.members[0]
    };

    // Step 2: Compile to monomorphized AST
    let (mut context, crate_id) = nargo::prepare_package(&file_manager, &parsed_files, package);

    noirc_driver::check_crate(
        &mut context,
        crate_id,
        &noirc_driver::CompileOptions {
            deny_warnings: false,
            debug_comptime_in_file: None,
            ..Default::default()
        },
    )
    .map_err(|errors| {
        RunError::CompilationFailed(
            errors
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join("\n"),
        )
    })?;

    let main_function = context
        .get_main_function(context.root_crate_id())
        .ok_or(RunError::NoMainFunction)?;

    let program = noirc_frontend::monomorphization::monomorphize(
        main_function,
        &mut context.def_interner,
        false,
    )
    .map_err(|e| RunError::MonomorphizationFailed(format!("{e:?}")))?;

    let abi = noirc_driver::gen_abi(
        &context,
        &main_function,
        program.return_visibility(),
        BTreeMap::default(),
    );

    // Step 3: Parse Prover.toml
    let prover_path = project_root.join("Prover.toml");
    let inputs = if prover_path.exists() {
        let ext = prover_path.extension().and_then(|e| e.to_str()).unwrap_or("toml");
        let format = Format::from_ext(ext).unwrap_or(Format::Toml);
        let contents = std::fs::read_to_string(&prover_path)
            .map_err(|e| RunError::ProverTomlReadFailed(e.to_string()))?;
        format
            .parse(&contents, &abi)
            .map_err(|e| RunError::ProverTomlParseFailed(e.to_string()))?
    } else {
        BTreeMap::new()
    };

    // Check for expected return value (before removing it from inputs)
    let expected_return_input = inputs.get("return").cloned();

    // Remove the return key from inputs (it's not a parameter)
    let mut param_inputs = inputs;
    param_inputs.remove("return");

    // Step 4: Run the interpreter
    let return_value = evaluate(&program, &abi, &param_inputs)?;

    // Step 5: Check return value if requested
    let expected_return = if let Some(expected_input) = expected_return_input {
        let expected_value = if let Some(ref ret_type) = abi.return_type {
            input_value_to_value(&expected_input, &ret_type.abi_type)?
        } else {
            return Err(RunError::UnexpectedReturnValue);
        };

        if options.check_return_value && !values_equal(&return_value, &expected_value) {
            return Err(RunError::ReturnValueMismatch {
                expected: expected_value,
                actual: return_value,
            });
        }

        Some(expected_value)
    } else {
        None
    };

    Ok(RunResult {
        return_value,
        expected_return,
    })
}

/// Parse workspace files.
fn parse_workspace(workspace: &Workspace) -> (FileManager, ParsedFiles) {
    let mut file_manager = workspace.new_file_manager();
    nargo::insert_all_files_for_workspace_into_file_manager(workspace, &mut file_manager);
    let parsed_files = nargo::parse_all(&file_manager);
    (file_manager, parsed_files)
}

/// Compare two Values for equality.
pub fn values_equal(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Field(fa), Value::Field(fb)) => fa == fb,
        (Value::Integer { value: va, .. }, Value::Integer { value: vb, .. }) => va == vb,
        (Value::Bool(ba), Value::Bool(bb)) => ba == bb,
        (Value::String(sa), Value::String(sb)) => sa == sb,
        (Value::Array(aa), Value::Array(ab)) | (Value::Slice(aa), Value::Slice(ab)) => {
            aa.len() == ab.len() && aa.iter().zip(ab.iter()).all(|(x, y)| values_equal(x, y))
        }
        (Value::Tuple(ta), Value::Tuple(tb)) => {
            ta.len() == tb.len() && ta.iter().zip(tb.iter()).all(|(x, y)| values_equal(x, y))
        }
        (Value::Unit, Value::Unit) => true,
        // Field and Integer can be compared
        (Value::Field(f), Value::Integer { value, .. })
        | (Value::Integer { value, .. }, Value::Field(f)) => f == value,
        _ => false,
    }
}

/// A runtime value in the interpreter.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    /// A field element.
    Field(Field),
    /// An integer value (stored as field, with sign and bit size for semantics).
    Integer {
        value: Field,
        signed: bool,
        bit_size: u32,
    },
    /// A boolean value.
    Bool(bool),
    /// A string value.
    String(String),
    /// An array of values.
    Array(Vec<Value>),
    /// A slice (dynamic array) of values.
    Slice(Vec<Value>),
    /// A tuple of values.
    Tuple(Vec<Value>),
    /// A reference to a value (stored as the underlying value for simplicity).
    Reference(Box<Value>),
    /// The unit value.
    Unit,
    /// A function pointer.
    Function(FuncId),
}

impl Value {
    /// Convert the value to a field element, if possible.
    pub fn to_field(&self) -> EvalResult<Field> {
        match self {
            Value::Field(f) => Ok(*f),
            Value::Integer { value, .. } => Ok(*value),
            Value::Bool(b) => Ok(if *b { Field::one() } else { Field::zero() }),
            _ => Err(EvalError::TypeMismatch {
                expected: "field".to_string(),
                actual: format!("{:?}", self),
            }),
        }
    }

    /// Convert the value to a boolean, if possible.
    pub fn to_bool(&self) -> EvalResult<bool> {
        match self {
            Value::Bool(b) => Ok(*b),
            Value::Field(f) => Ok(!f.is_zero()),
            Value::Integer { value, .. } => Ok(!value.is_zero()),
            _ => Err(EvalError::TypeMismatch {
                expected: "bool".to_string(),
                actual: format!("{:?}", self),
            }),
        }
    }

    /// Convert the value to an integer, if possible.
    pub fn to_integer(&self) -> EvalResult<(Field, bool, u32)> {
        match self {
            Value::Integer {
                value,
                signed,
                bit_size,
            } => Ok((*value, *signed, *bit_size)),
            Value::Field(f) => Ok((*f, false, 254)),
            Value::Bool(b) => Ok((
                if *b { Field::one() } else { Field::zero() },
                false,
                1,
            )),
            _ => Err(EvalError::TypeMismatch {
                expected: "integer".to_string(),
                actual: format!("{:?}", self),
            }),
        }
    }
}

/// Control flow signal for loop handling.
enum ControlFlow {
    /// Normal execution continues.
    Continue,
    /// Break out of the current loop.
    Break,
    /// Continue to the next iteration.
    LoopContinue,
}

/// The interpreter environment, holding variable bindings.
struct Environment {
    /// Stack of scopes. Each scope maps local IDs to values.
    scopes: Vec<BTreeMap<LocalId, Value>>,
}

impl Environment {
    fn new() -> Self {
        Self {
            scopes: vec![BTreeMap::new()],
        }
    }

    fn push_scope(&mut self) {
        self.scopes.push(BTreeMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn define(&mut self, id: LocalId, value: Value) {
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(id, value);
        }
    }

    fn get(&self, id: &LocalId) -> Option<&Value> {
        for scope in self.scopes.iter().rev() {
            if let Some(value) = scope.get(id) {
                return Some(value);
            }
        }
        None
    }

    fn set(&mut self, id: &LocalId, value: Value) -> EvalResult<()> {
        for scope in self.scopes.iter_mut().rev() {
            if scope.contains_key(id) {
                scope.insert(*id, value);
                return Ok(());
            }
        }
        Err(EvalError::UndefinedVariable(format!("{:?}", id)))
    }
}

/// The AST interpreter.
pub struct Interpreter<'a> {
    /// The program being executed.
    program: &'a Program,
    /// The variable environment.
    env: Environment,
    /// Global variable values (lazily evaluated).
    globals: BTreeMap<GlobalId, Value>,
}

impl<'a> Interpreter<'a> {
    /// Create a new interpreter for the given program.
    pub fn new(program: &'a Program) -> Self {
        Self {
            program,
            env: Environment::new(),
            globals: BTreeMap::new(),
        }
    }

    /// Evaluate the program's main function with the given inputs.
    pub fn evaluate(&mut self, inputs: Vec<Value>) -> EvalResult<Value> {
        let main_func = self.program.main();
        self.call_function(main_func.id, inputs)
    }

    /// Call a function by its ID with the given arguments.
    fn call_function(&mut self, func_id: FuncId, args: Vec<Value>) -> EvalResult<Value> {
        let func = self
            .program
            .functions
            .get(func_id.0 as usize)
            .ok_or(EvalError::UndefinedFunction(func_id.0))?;

        self.env.push_scope();

        // Bind parameters to arguments.
        for (i, (param_id, _mutable, _name, _typ, _vis)) in func.parameters.iter().enumerate() {
            let arg = args.get(i).cloned().unwrap_or(Value::Unit);
            self.env.define(*param_id, arg);
        }

        // Evaluate the function body.
        let result = self.eval_expr(&func.body);

        self.env.pop_scope();

        result
    }

    /// Evaluate an expression.
    fn eval_expr(&mut self, expr: &Expression) -> EvalResult<Value> {
        match expr {
            Expression::Ident(ident) => self.eval_ident(ident),
            Expression::Literal(lit) => self.eval_literal(lit),
            Expression::Block(exprs) => self.eval_block(exprs),
            Expression::Unary(unary) => self.eval_unary(unary),
            Expression::Binary(binary) => self.eval_binary(binary),
            Expression::Index(index) => self.eval_index(index),
            Expression::Cast(cast) => self.eval_cast(cast),
            Expression::If(if_expr) => self.eval_if(if_expr),
            Expression::Match(match_expr) => self.eval_match(match_expr),
            Expression::Tuple(exprs) => self.eval_tuple(exprs),
            Expression::ExtractTupleField(expr, idx) => self.eval_extract_tuple_field(expr, *idx),
            Expression::Call(call) => self.eval_call(call),
            Expression::Let(let_expr) => self.eval_let(let_expr),
            Expression::Assign(assign) => self.eval_assign(assign),
            Expression::Constrain(expr, _loc, msg) => self.eval_constrain(expr, msg.as_ref()),
            Expression::Semi(expr) => {
                self.eval_expr(expr)?;
                Ok(Value::Unit)
            }
            Expression::Clone(expr) => self.eval_expr(expr),
            Expression::Drop(expr) => {
                self.eval_expr(expr)?;
                Ok(Value::Unit)
            }
            Expression::While(while_expr) => self.eval_while(while_expr),
            Expression::For(for_expr) => self.eval_for(for_expr),
            Expression::Loop(body) => self.eval_loop(body),
            Expression::Break => Err(EvalError::BreakOutsideLoop),
            Expression::Continue => Err(EvalError::ContinueOutsideLoop),
        }
    }

    /// Evaluate an expression, handling break/continue control flow.
    fn eval_expr_in_loop(&mut self, expr: &Expression) -> EvalResult<(Value, ControlFlow)> {
        match expr {
            Expression::Break => Ok((Value::Unit, ControlFlow::Break)),
            Expression::Continue => Ok((Value::Unit, ControlFlow::LoopContinue)),
            Expression::Block(exprs) => {
                let mut result = Value::Unit;
                for e in exprs {
                    let (val, cf) = self.eval_expr_in_loop(e)?;
                    match cf {
                        ControlFlow::Continue => result = val,
                        ControlFlow::Break | ControlFlow::LoopContinue => return Ok((val, cf)),
                    }
                }
                Ok((result, ControlFlow::Continue))
            }
            Expression::If(if_expr) => {
                let cond = self.eval_expr(&if_expr.condition)?.to_bool()?;
                if cond {
                    self.eval_expr_in_loop(&if_expr.consequence)
                } else if let Some(alt) = &if_expr.alternative {
                    self.eval_expr_in_loop(alt)
                } else {
                    Ok((Value::Unit, ControlFlow::Continue))
                }
            }
            _ => {
                let val = self.eval_expr(expr)?;
                Ok((val, ControlFlow::Continue))
            }
        }
    }

    fn eval_ident(&mut self, ident: &ast::Ident) -> EvalResult<Value> {
        match &ident.definition {
            Definition::Local(id) => self
                .env
                .get(id)
                .cloned()
                .ok_or_else(|| EvalError::UndefinedVariable(ident.name.clone())),
            Definition::Global(id) => self.eval_global(*id),
            Definition::Function(func_id) => Ok(Value::Function(*func_id)),
            Definition::Builtin(name) | Definition::LowLevel(name) | Definition::Oracle(name) => {
                Err(EvalError::UnsupportedOperation(format!(
                    "builtin/lowlevel/oracle: {}",
                    name
                )))
            }
        }
    }

    fn eval_global(&mut self, id: GlobalId) -> EvalResult<Value> {
        if let Some(value) = self.globals.get(&id) {
            return Ok(value.clone());
        }

        let (_name, _typ, init_expr) = self
            .program
            .globals
            .get(&id)
            .ok_or(EvalError::UndefinedGlobal(id.0))?;

        let init_expr = init_expr.clone();
        let value = self.eval_expr(&init_expr)?;
        self.globals.insert(id, value.clone());
        Ok(value)
    }

    fn eval_literal(&mut self, lit: &Literal) -> EvalResult<Value> {
        match lit {
            Literal::Array(arr) => self.eval_array_literal(arr, false),
            Literal::Slice(arr) => self.eval_array_literal(arr, true),
            Literal::Integer(signed_field, typ, _loc) => {
                // Get the absolute value and convert to our Field type
                let abs_value = signed_field.absolute_value();
                let bytes = abs_value.to_be_bytes();
                let mut field_value = Field::from_be_bytes_mod_order(&bytes);

                // Apply sign if negative
                if signed_field.is_negative() {
                    field_value = -field_value;
                }

                match typ {
                    Type::Integer(sign, bit_size) => {
                        let is_signed = is_type_signed(sign);
                        let bits = get_bit_size(bit_size);
                        Ok(Value::Integer {
                            value: field_value,
                            signed: is_signed,
                            bit_size: bits,
                        })
                    }
                    Type::Field => Ok(Value::Field(field_value)),
                    _ => Err(EvalError::TypeMismatch {
                        expected: "integer or field".to_string(),
                        actual: format!("{:?}", typ),
                    }),
                }
            }
            Literal::Bool(b) => Ok(Value::Bool(*b)),
            Literal::Unit => Ok(Value::Unit),
            Literal::Str(s) => Ok(Value::String(s.clone())),
            Literal::FmtStr(fragments, _len, _tuple) => {
                let mut result = String::new();
                for frag in fragments {
                    result.push_str(&format!("{:?}", frag));
                }
                Ok(Value::String(result))
            }
        }
    }

    fn eval_array_literal(
        &mut self,
        arr: &ast::ArrayLiteral,
        is_slice: bool,
    ) -> EvalResult<Value> {
        let values: EvalResult<Vec<Value>> =
            arr.contents.iter().map(|e| self.eval_expr(e)).collect();
        let values = values?;

        if is_slice {
            Ok(Value::Slice(values))
        } else {
            Ok(Value::Array(values))
        }
    }

    fn eval_block(&mut self, exprs: &[Expression]) -> EvalResult<Value> {
        let mut result = Value::Unit;
        for expr in exprs {
            result = self.eval_expr(expr)?;
        }
        Ok(result)
    }

    fn eval_unary(&mut self, unary: &ast::Unary) -> EvalResult<Value> {
        let rhs = self.eval_expr(&unary.rhs)?;

        match unary.operator {
            UnaryOp::Not => match rhs {
                Value::Bool(b) => Ok(Value::Bool(!b)),
                Value::Integer {
                    value,
                    signed,
                    bit_size,
                } => {
                    let mask = if bit_size >= 254 {
                        Field::from(-1i64)
                    } else {
                        Field::from((1u128 << bit_size) - 1)
                    };
                    let not_value = mask - value;
                    Ok(Value::Integer {
                        value: not_value,
                        signed,
                        bit_size,
                    })
                }
                _ => Err(EvalError::TypeMismatch {
                    expected: "bool or integer".to_string(),
                    actual: format!("{:?}", rhs),
                }),
            },
            UnaryOp::Minus => match rhs {
                Value::Field(f) => Ok(Value::Field(-f)),
                Value::Integer {
                    value,
                    signed,
                    bit_size,
                } => Ok(Value::Integer {
                    value: -value,
                    signed,
                    bit_size,
                }),
                _ => Err(EvalError::TypeMismatch {
                    expected: "field or integer".to_string(),
                    actual: format!("{:?}", rhs),
                }),
            },
            UnaryOp::Dereference { .. } => match rhs {
                Value::Reference(inner) => Ok(*inner),
                other => Ok(other),
            },
            UnaryOp::Reference { .. } => Ok(Value::Reference(Box::new(rhs))),
        }
    }

    fn eval_binary(&mut self, binary: &ast::Binary) -> EvalResult<Value> {
        let lhs = self.eval_expr(&binary.lhs)?;

        match binary.operator {
            BinaryOpKind::And => {
                if !lhs.to_bool()? {
                    return Ok(Value::Bool(false));
                }
                let rhs = self.eval_expr(&binary.rhs)?;
                Ok(Value::Bool(rhs.to_bool()?))
            }
            BinaryOpKind::Or => {
                if lhs.to_bool()? {
                    return Ok(Value::Bool(true));
                }
                let rhs = self.eval_expr(&binary.rhs)?;
                Ok(Value::Bool(rhs.to_bool()?))
            }
            _ => {
                let rhs = self.eval_expr(&binary.rhs)?;
                self.eval_binary_op(binary.operator, lhs, rhs)
            }
        }
    }

    fn eval_binary_op(&self, op: BinaryOpKind, lhs: Value, rhs: Value) -> EvalResult<Value> {
        match op {
            BinaryOpKind::Add => self.numeric_op(lhs, rhs, |a, b| a + b),
            BinaryOpKind::Subtract => self.numeric_op(lhs, rhs, |a, b| a - b),
            BinaryOpKind::Multiply => self.numeric_op(lhs, rhs, |a, b| a * b),
            BinaryOpKind::Divide => {
                let rhs_field = rhs.to_field()?;
                if rhs_field.is_zero() {
                    return Err(EvalError::DivisionByZero);
                }
                self.numeric_op(lhs, rhs, |a, b| a / b)
            }
            BinaryOpKind::Modulo => {
                let (lhs_val, _, _) = lhs.to_integer()?;
                let (rhs_val, signed, bit_size) = rhs.to_integer()?;
                if rhs_val.is_zero() {
                    return Err(EvalError::DivisionByZero);
                }
                let lhs_int = field_to_u128(lhs_val);
                let rhs_int = field_to_u128(rhs_val);
                let result = lhs_int % rhs_int;
                Ok(Value::Integer {
                    value: Field::from(result),
                    signed,
                    bit_size,
                })
            }
            BinaryOpKind::Equal => {
                let eq = self.values_equal(&lhs, &rhs)?;
                Ok(Value::Bool(eq))
            }
            BinaryOpKind::NotEqual => {
                let eq = self.values_equal(&lhs, &rhs)?;
                Ok(Value::Bool(!eq))
            }
            BinaryOpKind::Less => self.comparison_op(lhs, rhs, |a, b| a < b),
            BinaryOpKind::LessEqual => self.comparison_op(lhs, rhs, |a, b| a <= b),
            BinaryOpKind::Greater => self.comparison_op(lhs, rhs, |a, b| a > b),
            BinaryOpKind::GreaterEqual => self.comparison_op(lhs, rhs, |a, b| a >= b),
            BinaryOpKind::And => {
                let l = lhs.to_bool()?;
                let r = rhs.to_bool()?;
                Ok(Value::Bool(l && r))
            }
            BinaryOpKind::Or => {
                let l = lhs.to_bool()?;
                let r = rhs.to_bool()?;
                Ok(Value::Bool(l || r))
            }
            BinaryOpKind::Xor => match (&lhs, &rhs) {
                (Value::Bool(l), Value::Bool(r)) => Ok(Value::Bool(*l ^ *r)),
                _ => {
                    let (lhs_val, signed, bit_size) = lhs.to_integer()?;
                    let (rhs_val, _, _) = rhs.to_integer()?;
                    let lhs_int = field_to_u128(lhs_val);
                    let rhs_int = field_to_u128(rhs_val);
                    Ok(Value::Integer {
                        value: Field::from(lhs_int ^ rhs_int),
                        signed,
                        bit_size,
                    })
                }
            },
            BinaryOpKind::ShiftLeft => {
                let (lhs_val, signed, bit_size) = lhs.to_integer()?;
                let (rhs_val, _, _) = rhs.to_integer()?;
                let lhs_int = field_to_u128(lhs_val);
                let rhs_int = field_to_u128(rhs_val) as u32;
                let result = lhs_int.wrapping_shl(rhs_int);
                let mask = if bit_size >= 128 {
                    u128::MAX
                } else {
                    (1u128 << bit_size) - 1
                };
                Ok(Value::Integer {
                    value: Field::from(result & mask),
                    signed,
                    bit_size,
                })
            }
            BinaryOpKind::ShiftRight => {
                let (lhs_val, signed, bit_size) = lhs.to_integer()?;
                let (rhs_val, _, _) = rhs.to_integer()?;
                let lhs_int = field_to_u128(lhs_val);
                let rhs_int = field_to_u128(rhs_val) as u32;
                let result = lhs_int.wrapping_shr(rhs_int);
                Ok(Value::Integer {
                    value: Field::from(result),
                    signed,
                    bit_size,
                })
            }
        }
    }

    fn numeric_op<F>(&self, lhs: Value, rhs: Value, op: F) -> EvalResult<Value>
    where
        F: Fn(Field, Field) -> Field,
    {
        match (&lhs, &rhs) {
            (Value::Field(l), Value::Field(r)) => Ok(Value::Field(op(*l, *r))),
            (Value::Field(l), Value::Integer { value: r, .. }) => Ok(Value::Field(op(*l, *r))),
            (Value::Integer { value: l, .. }, Value::Field(r)) => Ok(Value::Field(op(*l, *r))),
            (
                Value::Integer {
                    value: l,
                    signed: s1,
                    bit_size: b1,
                },
                Value::Integer { value: r, .. },
            ) => Ok(Value::Integer {
                value: op(*l, *r),
                signed: *s1,
                bit_size: *b1,
            }),
            _ => Err(EvalError::TypeMismatch {
                expected: "numeric types".to_string(),
                actual: format!("{:?} and {:?}", lhs, rhs),
            }),
        }
    }

    fn comparison_op<F>(&self, lhs: Value, rhs: Value, op: F) -> EvalResult<Value>
    where
        F: Fn(u128, u128) -> bool,
    {
        let lhs_val = lhs.to_field()?;
        let rhs_val = rhs.to_field()?;
        let lhs_int = field_to_u128(lhs_val);
        let rhs_int = field_to_u128(rhs_val);
        Ok(Value::Bool(op(lhs_int, rhs_int)))
    }

    fn values_equal(&self, lhs: &Value, rhs: &Value) -> EvalResult<bool> {
        match (lhs, rhs) {
            (Value::Field(l), Value::Field(r)) => Ok(l == r),
            (Value::Integer { value: l, .. }, Value::Integer { value: r, .. }) => Ok(l == r),
            (Value::Field(l), Value::Integer { value: r, .. }) => Ok(l == r),
            (Value::Integer { value: l, .. }, Value::Field(r)) => Ok(l == r),
            (Value::Bool(l), Value::Bool(r)) => Ok(l == r),
            (Value::String(l), Value::String(r)) => Ok(l == r),
            (Value::Unit, Value::Unit) => Ok(true),
            (Value::Array(l), Value::Array(r)) | (Value::Slice(l), Value::Slice(r)) => {
                if l.len() != r.len() {
                    return Ok(false);
                }
                for (lv, rv) in l.iter().zip(r.iter()) {
                    if !self.values_equal(lv, rv)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            (Value::Tuple(l), Value::Tuple(r)) => {
                if l.len() != r.len() {
                    return Ok(false);
                }
                for (lv, rv) in l.iter().zip(r.iter()) {
                    if !self.values_equal(lv, rv)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    fn eval_index(&mut self, index: &ast::Index) -> EvalResult<Value> {
        let collection = self.eval_expr(&index.collection)?;
        let idx = self.eval_expr(&index.index)?;
        let idx_val = field_to_u128(idx.to_field()?) as usize;

        match collection {
            Value::Array(arr) | Value::Slice(arr) => {
                arr.get(idx_val).cloned().ok_or(EvalError::IndexOutOfBounds {
                    index: idx_val,
                    length: arr.len(),
                })
            }
            Value::String(s) => {
                let chars: Vec<char> = s.chars().collect();
                chars
                    .get(idx_val)
                    .map(|c| Value::Integer {
                        value: Field::from(*c as u64),
                        signed: false,
                        bit_size: 8,
                    })
                    .ok_or(EvalError::IndexOutOfBounds {
                        index: idx_val,
                        length: chars.len(),
                    })
            }
            _ => Err(EvalError::TypeMismatch {
                expected: "array, slice, or string".to_string(),
                actual: format!("{:?}", collection),
            }),
        }
    }

    fn eval_cast(&mut self, cast: &ast::Cast) -> EvalResult<Value> {
        let value = self.eval_expr(&cast.lhs)?;

        match &cast.r#type {
            Type::Field => Ok(Value::Field(value.to_field()?)),
            Type::Integer(sign, bit_size) => {
                let field_val = value.to_field()?;
                let int_val = field_to_u128(field_val);
                let bit_size_val = get_bit_size(bit_size);
                let mask = if bit_size_val >= 128 {
                    u128::MAX
                } else {
                    (1u128 << bit_size_val) - 1
                };
                Ok(Value::Integer {
                    value: Field::from(int_val & mask),
                    signed: is_type_signed(sign),
                    bit_size: bit_size_val,
                })
            }
            Type::Bool => Ok(Value::Bool(value.to_bool()?)),
            _ => Err(EvalError::InvalidCast {
                from: format!("{:?}", value),
                to: format!("{:?}", cast.r#type),
            }),
        }
    }

    fn eval_if(&mut self, if_expr: &ast::If) -> EvalResult<Value> {
        let condition = self.eval_expr(&if_expr.condition)?.to_bool()?;

        if condition {
            self.eval_expr(&if_expr.consequence)
        } else if let Some(alt) = &if_expr.alternative {
            self.eval_expr(alt)
        } else {
            Ok(Value::Unit)
        }
    }

    fn eval_match(&mut self, match_expr: &ast::Match) -> EvalResult<Value> {
        // variable_to_match is (LocalId, String), get the value from environment.
        let (local_id, _name) = &match_expr.variable_to_match;
        let scrutinee = self
            .env
            .get(local_id)
            .cloned()
            .ok_or_else(|| EvalError::UndefinedVariable(format!("{:?}", local_id)))?;

        for case in &match_expr.cases {
            if let Some(result) = self.try_match_case(&scrutinee, case)? {
                return Ok(result);
            }
        }

        if let Some(default) = &match_expr.default_case {
            return self.eval_expr(default);
        }

        Err(EvalError::AssertionFailed(
            "no match case matched".to_string(),
        ))
    }

    fn try_match_case(
        &mut self,
        scrutinee: &Value,
        case: &ast::MatchCase,
    ) -> EvalResult<Option<Value>> {
        match &case.constructor {
            Constructor::Variant(_, tag) => {
                if let Value::Integer { value, .. } = scrutinee {
                    let variant_int = field_to_u128(*value) as usize;
                    if variant_int == *tag {
                        self.env.push_scope();
                        for (id, _name) in &case.arguments {
                            self.env.define(*id, Value::Unit);
                        }
                        let result = self.eval_expr(&case.branch)?;
                        self.env.pop_scope();
                        return Ok(Some(result));
                    }
                }
            }
            Constructor::Tuple(_) => {
                if let Value::Tuple(elems) = scrutinee {
                    self.env.push_scope();
                    for (i, (id, _name)) in case.arguments.iter().enumerate() {
                        let val = elems.get(i).cloned().unwrap_or(Value::Unit);
                        self.env.define(*id, val);
                    }
                    let result = self.eval_expr(&case.branch)?;
                    self.env.pop_scope();
                    return Ok(Some(result));
                }
            }
            Constructor::True => {
                if let Value::Bool(true) = scrutinee {
                    let result = self.eval_expr(&case.branch)?;
                    return Ok(Some(result));
                }
            }
            Constructor::False => {
                if let Value::Bool(false) = scrutinee {
                    let result = self.eval_expr(&case.branch)?;
                    return Ok(Some(result));
                }
            }
            Constructor::Unit => {
                if let Value::Unit = scrutinee {
                    let result = self.eval_expr(&case.branch)?;
                    return Ok(Some(result));
                }
            }
            Constructor::Int(signed_field) => {
                if let Value::Integer { value, .. } | Value::Field(value) = scrutinee {
                    let abs_val = signed_field.absolute_value();
                    let bytes = abs_val.to_be_bytes();
                    let mut expected = Field::from_be_bytes_mod_order(&bytes);
                    if signed_field.is_negative() {
                        expected = -expected;
                    }
                    if *value == expected {
                        let result = self.eval_expr(&case.branch)?;
                        return Ok(Some(result));
                    }
                }
            }
            Constructor::Range(start, end) => {
                if let Value::Integer { value, .. } | Value::Field(value) = scrutinee {
                    let start_bytes = start.absolute_value().to_be_bytes();
                    let mut start_val = Field::from_be_bytes_mod_order(&start_bytes);
                    if start.is_negative() {
                        start_val = -start_val;
                    }
                    let end_bytes = end.absolute_value().to_be_bytes();
                    let mut end_val = Field::from_be_bytes_mod_order(&end_bytes);
                    if end.is_negative() {
                        end_val = -end_val;
                    }
                    // Check if value is in range [start, end)
                    let val_u128 = field_to_u128(*value);
                    let start_u128 = field_to_u128(start_val);
                    let end_u128 = field_to_u128(end_val);
                    if val_u128 >= start_u128 && val_u128 < end_u128 {
                        let result = self.eval_expr(&case.branch)?;
                        return Ok(Some(result));
                    }
                }
            }
        }
        Ok(None)
    }

    fn eval_tuple(&mut self, exprs: &[Expression]) -> EvalResult<Value> {
        let values: EvalResult<Vec<Value>> = exprs.iter().map(|e| self.eval_expr(e)).collect();
        Ok(Value::Tuple(values?))
    }

    fn eval_extract_tuple_field(&mut self, expr: &Expression, idx: usize) -> EvalResult<Value> {
        let tuple = self.eval_expr(expr)?;
        match tuple {
            Value::Tuple(fields) => {
                fields.get(idx).cloned().ok_or(EvalError::IndexOutOfBounds {
                    index: idx,
                    length: fields.len(),
                })
            }
            _ => Err(EvalError::TypeMismatch {
                expected: "tuple".to_string(),
                actual: format!("{:?}", tuple),
            }),
        }
    }

    fn eval_call(&mut self, call: &ast::Call) -> EvalResult<Value> {
        let func_val = self.eval_expr(&call.func)?;

        let args: EvalResult<Vec<Value>> =
            call.arguments.iter().map(|a| self.eval_expr(a)).collect();
        let args = args?;

        match func_val {
            Value::Function(func_id) => self.call_function(func_id, args),
            _ => Err(EvalError::TypeMismatch {
                expected: "function".to_string(),
                actual: format!("{:?}", func_val),
            }),
        }
    }

    fn eval_let(&mut self, let_expr: &ast::Let) -> EvalResult<Value> {
        let value = self.eval_expr(&let_expr.expression)?;
        self.env.define(let_expr.id, value);
        Ok(Value::Unit)
    }

    fn eval_assign(&mut self, assign: &ast::Assign) -> EvalResult<Value> {
        let value = self.eval_expr(&assign.expression)?;
        self.assign_lvalue(&assign.lvalue, value)?;
        Ok(Value::Unit)
    }

    fn assign_lvalue(&mut self, lvalue: &ast::LValue, value: Value) -> EvalResult<()> {
        match lvalue {
            ast::LValue::Ident(ident) => {
                if let Definition::Local(id) = &ident.definition {
                    self.env.set(id, value)
                } else {
                    Err(EvalError::UnsupportedOperation(
                        "assignment to non-local".to_string(),
                    ))
                }
            }
            ast::LValue::Index { array, index, .. } => {
                let idx = self.eval_expr(index)?;
                let idx_val = field_to_u128(idx.to_field()?) as usize;

                let mut array_val = self.eval_lvalue_to_ref(array)?;
                match &mut array_val {
                    Value::Array(arr) | Value::Slice(arr) => {
                        if idx_val >= arr.len() {
                            return Err(EvalError::IndexOutOfBounds {
                                index: idx_val,
                                length: arr.len(),
                            });
                        }
                        arr[idx_val] = value;
                        self.write_lvalue_back(array, array_val)?;
                        Ok(())
                    }
                    _ => Err(EvalError::TypeMismatch {
                        expected: "array or slice".to_string(),
                        actual: format!("{:?}", array_val),
                    }),
                }
            }
            ast::LValue::MemberAccess {
                object,
                field_index,
                ..
            } => {
                let mut obj_val = self.eval_lvalue_to_ref(object)?;
                match &mut obj_val {
                    Value::Tuple(fields) => {
                        if *field_index >= fields.len() {
                            return Err(EvalError::IndexOutOfBounds {
                                index: *field_index,
                                length: fields.len(),
                            });
                        }
                        fields[*field_index] = value;
                        self.write_lvalue_back(object, obj_val)?;
                        Ok(())
                    }
                    _ => Err(EvalError::TypeMismatch {
                        expected: "tuple".to_string(),
                        actual: format!("{:?}", obj_val),
                    }),
                }
            }
            ast::LValue::Dereference { reference, .. } => {
                let ref_val = self.eval_lvalue_to_ref(reference)?;
                match ref_val {
                    Value::Reference(_) => {
                        self.write_lvalue_back(reference, Value::Reference(Box::new(value)))?;
                        Ok(())
                    }
                    _ => Err(EvalError::TypeMismatch {
                        expected: "reference".to_string(),
                        actual: format!("{:?}", ref_val),
                    }),
                }
            }
            ast::LValue::Clone(inner) => self.assign_lvalue(inner, value),
        }
    }

    fn eval_lvalue_to_ref(&mut self, lvalue: &ast::LValue) -> EvalResult<Value> {
        match lvalue {
            ast::LValue::Ident(ident) => self.eval_ident(ident),
            ast::LValue::Index { array, index, .. } => {
                let arr = self.eval_lvalue_to_ref(array)?;
                let idx = self.eval_expr(index)?;
                let idx_val = field_to_u128(idx.to_field()?) as usize;
                match arr {
                    Value::Array(vals) | Value::Slice(vals) => {
                        vals.get(idx_val).cloned().ok_or(EvalError::IndexOutOfBounds {
                            index: idx_val,
                            length: vals.len(),
                        })
                    }
                    _ => Err(EvalError::TypeMismatch {
                        expected: "array or slice".to_string(),
                        actual: format!("{:?}", arr),
                    }),
                }
            }
            ast::LValue::MemberAccess {
                object,
                field_index,
                ..
            } => {
                let obj = self.eval_lvalue_to_ref(object)?;
                match obj {
                    Value::Tuple(fields) => {
                        fields.get(*field_index).cloned().ok_or(EvalError::IndexOutOfBounds {
                            index: *field_index,
                            length: fields.len(),
                        })
                    }
                    _ => Err(EvalError::TypeMismatch {
                        expected: "tuple".to_string(),
                        actual: format!("{:?}", obj),
                    }),
                }
            }
            ast::LValue::Dereference { reference, .. } => {
                let ref_val = self.eval_lvalue_to_ref(reference)?;
                match ref_val {
                    Value::Reference(inner) => Ok(*inner),
                    other => Ok(other),
                }
            }
            ast::LValue::Clone(inner) => self.eval_lvalue_to_ref(inner),
        }
    }

    fn write_lvalue_back(&mut self, lvalue: &ast::LValue, value: Value) -> EvalResult<()> {
        match lvalue {
            ast::LValue::Ident(ident) => {
                if let Definition::Local(id) = &ident.definition {
                    self.env.set(id, value)
                } else {
                    Err(EvalError::UnsupportedOperation(
                        "assignment to non-local".to_string(),
                    ))
                }
            }
            ast::LValue::Index { array, index, .. } => {
                let idx = self.eval_expr(index)?;
                let idx_val = field_to_u128(idx.to_field()?) as usize;
                let mut arr_val = self.eval_lvalue_to_ref(array)?;
                match &mut arr_val {
                    Value::Array(arr) | Value::Slice(arr) => {
                        if idx_val >= arr.len() {
                            return Err(EvalError::IndexOutOfBounds {
                                index: idx_val,
                                length: arr.len(),
                            });
                        }
                        arr[idx_val] = value;
                        self.write_lvalue_back(array, arr_val)
                    }
                    _ => Err(EvalError::TypeMismatch {
                        expected: "array or slice".to_string(),
                        actual: format!("{:?}", arr_val),
                    }),
                }
            }
            ast::LValue::MemberAccess {
                object,
                field_index,
                ..
            } => {
                let mut obj_val = self.eval_lvalue_to_ref(object)?;
                match &mut obj_val {
                    Value::Tuple(fields) => {
                        if *field_index >= fields.len() {
                            return Err(EvalError::IndexOutOfBounds {
                                index: *field_index,
                                length: fields.len(),
                            });
                        }
                        fields[*field_index] = value;
                        self.write_lvalue_back(object, obj_val)
                    }
                    _ => Err(EvalError::TypeMismatch {
                        expected: "tuple".to_string(),
                        actual: format!("{:?}", obj_val),
                    }),
                }
            }
            ast::LValue::Dereference { reference, .. } => {
                self.write_lvalue_back(reference, Value::Reference(Box::new(value)))
            }
            ast::LValue::Clone(inner) => self.write_lvalue_back(inner, value),
        }
    }

    fn eval_constrain(
        &mut self,
        expr: &Expression,
        msg: Option<&Box<(Expression, noirc_frontend::hir_def::types::Type)>>,
    ) -> EvalResult<Value> {
        let condition = self.eval_expr(expr)?.to_bool()?;

        if !condition {
            let message = if let Some(msg_expr) = msg {
                let msg_val = self.eval_expr(&msg_expr.0)?;
                format!("{:?}", msg_val)
            } else {
                "constraint failed".to_string()
            };
            return Err(EvalError::AssertionFailed(message));
        }

        Ok(Value::Unit)
    }

    fn eval_while(&mut self, while_expr: &ast::While) -> EvalResult<Value> {
        loop {
            let cond = self.eval_expr(&while_expr.condition)?.to_bool()?;
            if !cond {
                break;
            }

            let (_, cf) = self.eval_expr_in_loop(&while_expr.body)?;
            match cf {
                ControlFlow::Continue | ControlFlow::LoopContinue => continue,
                ControlFlow::Break => break,
            }
        }
        Ok(Value::Unit)
    }

    fn eval_for(&mut self, for_expr: &ast::For) -> EvalResult<Value> {
        let start = self.eval_expr(&for_expr.start_range)?;
        let end = self.eval_expr(&for_expr.end_range)?;

        let start_int = field_to_u128(start.to_field()?) as i128;
        let end_int = field_to_u128(end.to_field()?) as i128;

        self.env.push_scope();

        for i in start_int..end_int {
            self.env.define(
                for_expr.index_variable,
                Value::Integer {
                    value: Field::from(i as u64),
                    signed: false,
                    bit_size: 64,
                },
            );

            let (_, cf) = self.eval_expr_in_loop(&for_expr.block)?;
            match cf {
                ControlFlow::Continue | ControlFlow::LoopContinue => continue,
                ControlFlow::Break => break,
            }
        }

        self.env.pop_scope();
        Ok(Value::Unit)
    }

    fn eval_loop(&mut self, body: &Expression) -> EvalResult<Value> {
        loop {
            let (_, cf) = self.eval_expr_in_loop(body)?;
            match cf {
                ControlFlow::Continue | ControlFlow::LoopContinue => continue,
                ControlFlow::Break => break,
            }
        }
        Ok(Value::Unit)
    }
}

/// Convert a field element to u128 (truncating if necessary).
fn field_to_u128(f: Field) -> u128 {
    let bytes = f.into_bigint().to_bytes_le();
    let mut result = 0u128;
    for (i, byte) in bytes.iter().take(16).enumerate() {
        result |= (*byte as u128) << (8 * i);
    }
    result
}

/// Check if a signedness type is signed.
fn is_type_signed(sign: &Signedness) -> bool {
    matches!(sign, Signedness::Signed)
}

/// Get the bit size from an IntegerBitSize.
fn get_bit_size(bit_size: &IntegerBitSize) -> u32 {
    match bit_size {
        IntegerBitSize::One => 1,
        IntegerBitSize::Eight => 8,
        IntegerBitSize::Sixteen => 16,
        IntegerBitSize::ThirtyTwo => 32,
        IntegerBitSize::SixtyFour => 64,
        IntegerBitSize::HundredTwentyEight => 128,
    }
}

/// Convert an input value from the ABI to an interpreter Value.
pub fn input_value_to_value(input: &InputValue, typ: &AbiType) -> EvalResult<Value> {
    match input {
        InputValue::Field(f) => {
            let bytes = f.to_le_bytes();
            let field = Field::from_le_bytes_mod_order(&bytes);
            Ok(Value::Field(field))
        }
        InputValue::String(s) => Ok(Value::String(s.clone())),
        InputValue::Vec(vec) => {
            let elem_type = match typ {
                AbiType::Array { typ, .. } => typ.as_ref(),
                _ => {
                    return Err(EvalError::InvalidInputValue {
                        param: "array".to_string(),
                        reason: "expected array type".to_string(),
                    })
                }
            };
            let values: EvalResult<Vec<Value>> = vec
                .iter()
                .map(|v| input_value_to_value(v, elem_type))
                .collect();
            Ok(Value::Array(values?))
        }
        InputValue::Struct(map) => {
            let fields = match typ {
                AbiType::Struct { fields, .. } => fields,
                _ => {
                    return Err(EvalError::InvalidInputValue {
                        param: "struct".to_string(),
                        reason: "expected struct type".to_string(),
                    })
                }
            };
            let mut values = Vec::new();
            for (name, field_type) in fields {
                let val = map.get(name).ok_or_else(|| EvalError::InvalidInputValue {
                    param: name.clone(),
                    reason: "missing field".to_string(),
                })?;
                values.push(input_value_to_value(val, field_type)?);
            }
            Ok(Value::Tuple(values))
        }
    }
}

/// Evaluate a Noir program with the given ABI and input parameters.
///
/// This is the main entry point for the interpreter. It takes:
/// - `program`: The monomorphized Noir program
/// - `abi`: The ABI describing the program's interface
/// - `inputs`: A map of parameter names to input values
///
/// Returns the result of evaluating the program's main function.
pub fn evaluate(
    program: &Program,
    abi: &Abi,
    inputs: &BTreeMap<String, InputValue>,
) -> EvalResult<Value> {
    let main_func = program.main();

    let mut ordered_inputs = Vec::new();
    for (_param_id, _mutable, param_name, _typ, _vis) in &main_func.parameters {
        let input = inputs
            .get(param_name)
            .ok_or_else(|| EvalError::MissingParameter(param_name.clone()))?;

        let abi_param = abi
            .parameters
            .iter()
            .find(|p| &p.name == param_name)
            .ok_or_else(|| EvalError::MissingParameter(param_name.clone()))?;

        let value = input_value_to_value(input, &abi_param.typ)?;
        ordered_inputs.push(value);
    }

    let mut interpreter = Interpreter::new(program);
    interpreter.evaluate(ordered_inputs)
}
