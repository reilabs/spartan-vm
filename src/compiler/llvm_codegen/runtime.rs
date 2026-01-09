//! Runtime function declarations for LLVM codegen
//!
//! Declares external functions that will be provided by the WASM runtime:
//! - Field arithmetic operations
//! - VM output write functions
//!
//! Field elements are represented as [4 x i64] arrays in Montgomery form.
//! Uses WASM-friendly calling convention: field elements passed by value.

use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::values::{BasicValueEnum, FunctionValue, PointerValue};
use inkwell::AddressSpace;

use ark_bn254::Fr;

use super::types::FIELD_LIMBS;

/// VM struct containing output pointers
pub struct VMType<'ctx> {
    pub struct_type: inkwell::types::StructType<'ctx>,
    pub ptr_type: inkwell::types::PointerType<'ctx>,
}

impl<'ctx> VMType<'ctx> {
    pub const NUM_OUTPUT_PTRS: usize = 4;

    pub fn new(context: &'ctx Context, _field_type: inkwell::types::ArrayType<'ctx>) -> Self {
        let field_ptr_type = context.ptr_type(AddressSpace::default());

        let field_types: Vec<inkwell::types::BasicTypeEnum> = (0..Self::NUM_OUTPUT_PTRS)
            .map(|_| field_ptr_type.into())
            .collect();

        let struct_type = context.struct_type(&field_types, false);
        let ptr_type = context.ptr_type(AddressSpace::default());

        Self { struct_type, ptr_type }
    }

    pub fn get_output_ptr(
        &self,
        builder: &Builder<'ctx>,
        vm_ptr: PointerValue<'ctx>,
        index: u32,
        name: &str,
    ) -> PointerValue<'ctx> {
        assert!((index as usize) < Self::NUM_OUTPUT_PTRS);

        let field_ptr_ptr = builder
            .build_struct_gep(self.struct_type, vm_ptr, index, &format!("{}_ptr_ptr", name))
            .unwrap();

        let ptr_type = builder.get_insert_block().unwrap().get_context().ptr_type(AddressSpace::default());
        builder
            .build_load(ptr_type, field_ptr_ptr, &format!("{}_ptr", name))
            .unwrap()
            .into_pointer_value()
    }
}

/// Runtime function declarations
pub struct Runtime<'ctx> {
    context: &'ctx Context,
    field_mul_fn: Option<FunctionValue<'ctx>>,
    write_witness_fn: Option<FunctionValue<'ctx>>,
    write_a_fn: Option<FunctionValue<'ctx>>,
    write_b_fn: Option<FunctionValue<'ctx>>,
    write_c_fn: Option<FunctionValue<'ctx>>,
}

impl<'ctx> Runtime<'ctx> {
    pub fn new(context: &'ctx Context, module: &Module<'ctx>) -> Self {
        let mut rt = Self {
            context,
            field_mul_fn: None,
            write_witness_fn: None,
            write_a_fn: None,
            write_b_fn: None,
            write_c_fn: None,
        };

        rt.declare_functions(module);
        rt
    }

    fn field_type(&self) -> inkwell::types::ArrayType<'ctx> {
        self.context.i64_type().array_type(FIELD_LIMBS)
    }

    fn declare_functions(&mut self, module: &Module<'ctx>) {
        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let void_type = self.context.void_type();
        let field_type = self.field_type();

        let field_mul_type = field_type.fn_type(
            &[field_type.into(), field_type.into()],
            false
        );
        self.field_mul_fn = Some(module.add_function("__field_mul", field_mul_type, None));

        let write_fn_type = void_type.fn_type(
            &[ptr_type.into(), field_type.into()],
            false
        );

        self.write_witness_fn = Some(module.add_function("__write_witness", write_fn_type, None));
        self.write_a_fn = Some(module.add_function("__write_a", write_fn_type, None));
        self.write_b_fn = Some(module.add_function("__write_b", write_fn_type, None));
        self.write_c_fn = Some(module.add_function("__write_c", write_fn_type, None));
    }

    pub fn const_field(&self, value: &Fr) -> BasicValueEnum<'ctx> {
        let i64_type = self.context.i64_type();
        let limbs = value.0.0;

        let mut values = Vec::with_capacity(FIELD_LIMBS as usize);
        for i in 0..FIELD_LIMBS as usize {
            values.push(i64_type.const_int(limbs[i], false));
        }

        let array = i64_type.const_array(&values);
        array.into()
    }

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

        call_site
            .try_as_basic_value()
            .left()
            .expect("field_mul should return a value")
    }

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
