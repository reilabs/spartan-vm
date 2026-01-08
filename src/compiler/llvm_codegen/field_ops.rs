//! BN254 Field Operations for LLVM Code Generation
//!
//! This module provides LLVM implementations of BN254 field arithmetic.
//! Field elements are represented as [4 x i64] arrays in Montgomery form.
//!
//! Uses WASM-friendly calling convention: field elements passed by value.

use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::values::{BasicValueEnum, FunctionValue, PointerValue, ValueKind};
use inkwell::AddressSpace;

use ark_bn254::Fr;

use super::types::FIELD_LIMBS;

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
        };

        ops.declare_field_functions(module);
        ops
    }

    /// Get the field type ([4 x i64])
    fn field_type(&self) -> inkwell::types::ArrayType<'ctx> {
        self.context.i64_type().array_type(FIELD_LIMBS)
    }

    /// Declare all field operation functions in the module
    fn declare_field_functions(&mut self, module: &Module<'ctx>) {
        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let void_type = self.context.void_type();
        let field_type = self.field_type();

        // Field multiplication: [4 x i64] __field_mul([4 x i64] a, [4 x i64] b)
        // Pass field elements by value, return result by value
        let field_mul_type = field_type.fn_type(
            &[field_type.into(), field_type.into()],
            false
        );
        self.field_mul_fn = Some(module.add_function("__field_mul", field_mul_type, None));

        // Write functions: void __write_X(ptr vm, [4 x i64] value)
        // VM pointer first, then field value directly
        let write_fn_type = void_type.fn_type(
            &[ptr_type.into(), field_type.into()],
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

    /// Field multiplication - pass values directly, get result directly
    pub fn mul(
        &self,
        builder: &Builder<'ctx>,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        let mul_fn = self.field_mul_fn.expect("__field_mul not declared");

        let call_site = builder
            .build_call(mul_fn, &[lhs.into(), rhs.into()], "field_mul")
            .unwrap();

        match call_site.try_as_basic_value() {
            ValueKind::Basic(val) => val,
            ValueKind::Instruction(_) => panic!("field_mul should return a value"),
        }
    }

    /// Write a witness value
    pub fn write_witness(
        &self,
        builder: &Builder<'ctx>,
        vm_ptr: PointerValue<'ctx>,
        value: BasicValueEnum<'ctx>,
    ) {
        let write_fn = self.write_witness_fn.expect("__write_witness not declared");
        builder
            .build_call(write_fn, &[vm_ptr.into(), value.into()], "")
            .unwrap();
    }

    /// Write constraint 'a' value
    pub fn write_a(
        &self,
        builder: &Builder<'ctx>,
        vm_ptr: PointerValue<'ctx>,
        value: BasicValueEnum<'ctx>,
    ) {
        let write_fn = self.write_a_fn.expect("__write_a not declared");
        builder
            .build_call(write_fn, &[vm_ptr.into(), value.into()], "")
            .unwrap();
    }

    /// Write constraint 'b' value
    pub fn write_b(
        &self,
        builder: &Builder<'ctx>,
        vm_ptr: PointerValue<'ctx>,
        value: BasicValueEnum<'ctx>,
    ) {
        let write_fn = self.write_b_fn.expect("__write_b not declared");
        builder
            .build_call(write_fn, &[vm_ptr.into(), value.into()], "")
            .unwrap();
    }

    /// Write constraint 'c' value
    pub fn write_c(
        &self,
        builder: &Builder<'ctx>,
        vm_ptr: PointerValue<'ctx>,
        value: BasicValueEnum<'ctx>,
    ) {
        let write_fn = self.write_c_fn.expect("__write_c not declared");
        builder
            .build_call(write_fn, &[vm_ptr.into(), value.into()], "")
            .unwrap();
    }
}
