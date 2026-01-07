//! BN254 Field Operations for LLVM Code Generation
//!
//! This module provides LLVM implementations of BN254 field arithmetic.
//! Field elements are represented as [4 x i64] arrays in Montgomery form.
//!
//! Currently only supports operations needed for the `power` example:
//! - Field multiplication (via external runtime call)
//! - Write operations for witnesses and constraints

use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::values::{BasicValueEnum, FunctionValue, PointerValue};
use inkwell::AddressSpace;

use ark_bn254::Fr;

use super::types::FIELD_LIMBS;

/// Scratch space for field operations - allocated once per function
/// to avoid stack growth from repeated alloca in loops
pub struct FieldScratch<'ctx> {
    pub result_ptr: PointerValue<'ctx>,
    pub lhs_ptr: PointerValue<'ctx>,
    pub rhs_ptr: PointerValue<'ctx>,
    pub write_val_ptr: PointerValue<'ctx>,
}

/// Field operations implementation
pub struct FieldOps<'ctx> {
    context: &'ctx Context,

    // Field multiplication function
    field_mul_fn: Option<FunctionValue<'ctx>>,

    // VM write functions
    write_witness_fn: Option<FunctionValue<'ctx>>,
    write_a_fn: Option<FunctionValue<'ctx>>,
    write_b_fn: Option<FunctionValue<'ctx>>,
    write_c_fn: Option<FunctionValue<'ctx>>,

    // Per-function scratch space (initialized at function entry)
    scratch: Option<FieldScratch<'ctx>>,
}

impl<'ctx> FieldOps<'ctx> {
    pub fn new(context: &'ctx Context, module: &Module<'ctx>) -> Self {
        let mut ops = Self {
            context,
            field_mul_fn: None,
            write_witness_fn: None,
            write_a_fn: None,
            write_b_fn: None,
            write_c_fn: None,
            scratch: None,
        };

        ops.declare_field_functions(module);
        ops
    }

    /// Allocate scratch space for field operations at function entry.
    /// This must be called once at the start of each function, in the entry block.
    pub fn init_scratch(&mut self, builder: &Builder<'ctx>) {
        let field_type = self.field_type();

        let result_ptr = builder.build_alloca(field_type, "field_scratch_result").unwrap();
        let lhs_ptr = builder.build_alloca(field_type, "field_scratch_lhs").unwrap();
        let rhs_ptr = builder.build_alloca(field_type, "field_scratch_rhs").unwrap();
        let write_val_ptr = builder.build_alloca(field_type, "field_scratch_write").unwrap();

        self.scratch = Some(FieldScratch {
            result_ptr,
            lhs_ptr,
            rhs_ptr,
            write_val_ptr,
        });
    }

    /// Clear scratch space when done with a function
    pub fn clear_scratch(&mut self) {
        self.scratch = None;
    }

    /// Get the field type ([4 x i64])
    fn field_type(&self) -> inkwell::types::ArrayType<'ctx> {
        self.context.i64_type().array_type(FIELD_LIMBS)
    }

    /// Declare all field operation functions in the module
    fn declare_field_functions(&mut self, module: &Module<'ctx>) {
        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let void_type = self.context.void_type();

        // Field multiplication: void __field_mul(ptr result, ptr a, ptr b)
        let field_binop_type = void_type.fn_type(
            &[ptr_type.into(), ptr_type.into(), ptr_type.into()],
            false
        );
        self.field_mul_fn = Some(module.add_function("__field_mul", field_binop_type, None));

        // Also declare add/sub/div for the runtime (even though we don't use them yet)
        module.add_function("__field_add", field_binop_type, None);
        module.add_function("__field_sub", field_binop_type, None);
        module.add_function("__field_div", field_binop_type, None);

        // Write functions: void __write_X(ptr vm, ptr value)
        let write_fn_type = void_type.fn_type(
            &[ptr_type.into(), ptr_type.into()],
            false
        );

        self.write_witness_fn = Some(module.add_function("__write_witness", write_fn_type, None));
        self.write_a_fn = Some(module.add_function("__write_a", write_fn_type, None));
        self.write_b_fn = Some(module.add_function("__write_b", write_fn_type, None));
        self.write_c_fn = Some(module.add_function("__write_c", write_fn_type, None));
    }

    /// Create a constant field value from an ark_bn254::Fr
    pub fn const_field(&self, value: &Fr) -> BasicValueEnum<'ctx> {
        let i64_type = self.context.i64_type();
        let limbs = value.0.0; // Access Montgomery form limbs

        let mut values = Vec::with_capacity(FIELD_LIMBS as usize);
        for i in 0..FIELD_LIMBS as usize {
            values.push(i64_type.const_int(limbs[i], false));
        }

        let array = i64_type.const_array(&values);
        array.into()
    }

    /// Field multiplication
    pub fn mul(
        &self,
        builder: &Builder<'ctx>,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        let mul_fn = self.field_mul_fn.expect("__field_mul not declared");
        self.call_field_binop(builder, mul_fn, lhs, rhs, "field_mul")
    }

    /// Helper to call a field binary operation using pointer-based ABI.
    fn call_field_binop(
        &self,
        builder: &Builder<'ctx>,
        func: FunctionValue<'ctx>,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
        name: &str,
    ) -> BasicValueEnum<'ctx> {
        let field_type = self.field_type();
        let scratch = self.scratch.as_ref()
            .expect("field_ops scratch space not initialized - call init_scratch first");

        // Store operands to scratch space
        builder.build_store(scratch.lhs_ptr, lhs).unwrap();
        builder.build_store(scratch.rhs_ptr, rhs).unwrap();

        // Call function: void __field_op(ptr result, ptr a, ptr b)
        builder
            .build_call(func, &[scratch.result_ptr.into(), scratch.lhs_ptr.into(), scratch.rhs_ptr.into()], name)
            .unwrap();

        // Load and return result
        builder.build_load(field_type, scratch.result_ptr, &format!("{}_val", name)).unwrap()
    }

    /// Write a witness value
    pub fn write_witness(
        &self,
        builder: &Builder<'ctx>,
        vm_ptr: PointerValue<'ctx>,
        value: BasicValueEnum<'ctx>,
    ) {
        let write_fn = self.write_witness_fn.expect("__write_witness not declared");
        self.call_write_fn(builder, write_fn, vm_ptr, value);
    }

    /// Write constraint 'a' value
    pub fn write_a(
        &self,
        builder: &Builder<'ctx>,
        vm_ptr: PointerValue<'ctx>,
        value: BasicValueEnum<'ctx>,
    ) {
        let write_fn = self.write_a_fn.expect("__write_a not declared");
        self.call_write_fn(builder, write_fn, vm_ptr, value);
    }

    /// Write constraint 'b' value
    pub fn write_b(
        &self,
        builder: &Builder<'ctx>,
        vm_ptr: PointerValue<'ctx>,
        value: BasicValueEnum<'ctx>,
    ) {
        let write_fn = self.write_b_fn.expect("__write_b not declared");
        self.call_write_fn(builder, write_fn, vm_ptr, value);
    }

    /// Write constraint 'c' value
    pub fn write_c(
        &self,
        builder: &Builder<'ctx>,
        vm_ptr: PointerValue<'ctx>,
        value: BasicValueEnum<'ctx>,
    ) {
        let write_fn = self.write_c_fn.expect("__write_c not declared");
        self.call_write_fn(builder, write_fn, vm_ptr, value);
    }

    /// Helper to call a write function using pointer-based ABI.
    fn call_write_fn(
        &self,
        builder: &Builder<'ctx>,
        func: FunctionValue<'ctx>,
        vm_ptr: PointerValue<'ctx>,
        value: BasicValueEnum<'ctx>,
    ) {
        let scratch = self.scratch.as_ref()
            .expect("field_ops scratch space not initialized - call init_scratch first");

        // Store value to scratch space
        builder.build_store(scratch.write_val_ptr, value).unwrap();

        // Call function: void __write_X(ptr vm, ptr value)
        builder
            .build_call(func, &[vm_ptr.into(), scratch.write_val_ptr.into()], "")
            .unwrap();
    }
}
