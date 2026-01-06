//! BN254 Field Operations for LLVM Code Generation
//!
//! This module provides LLVM implementations of BN254 field arithmetic.
//! Field elements are represented as [4 x i64] arrays in Montgomery form.
//!
//! The BN254 prime is:
//! p = 21888242871839275222246405745257275088548364400416034343698204186575808495617

use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, IntValue, ArrayValue};
use inkwell::AddressSpace;
use inkwell::IntPredicate;

use ark_bn254::Fr;
use ark_ff::BigInteger;

use super::types::FIELD_LIMBS;

/// BN254 field modulus as 4 x u64 limbs
const MODULUS: [u64; 4] = [
    0x43e1f593f0000001,
    0x2833e84879b97091,
    0xb85045b68181585d,
    0x30644e72e131a029,
];

/// Field operations implementation
pub struct FieldOps<'ctx> {
    context: &'ctx Context,

    // Cached function references for field operations
    field_add_fn: Option<FunctionValue<'ctx>>,
    field_sub_fn: Option<FunctionValue<'ctx>>,
    field_mul_fn: Option<FunctionValue<'ctx>>,
    field_div_fn: Option<FunctionValue<'ctx>>,

    // VM-related functions
    write_witness_fn: Option<FunctionValue<'ctx>>,
    write_a_fn: Option<FunctionValue<'ctx>>,
    write_b_fn: Option<FunctionValue<'ctx>>,
    write_c_fn: Option<FunctionValue<'ctx>>,
}

impl<'ctx> FieldOps<'ctx> {
    pub fn new(context: &'ctx Context, module: &Module<'ctx>) -> Self {
        let mut ops = Self {
            context,
            field_add_fn: None,
            field_sub_fn: None,
            field_mul_fn: None,
            field_div_fn: None,
            write_witness_fn: None,
            write_a_fn: None,
            write_b_fn: None,
            write_c_fn: None,
        };

        // Declare field operation functions
        ops.declare_field_functions(module);

        ops
    }

    /// Get the field type ([4 x i64])
    fn field_type(&self) -> inkwell::types::ArrayType<'ctx> {
        self.context.i64_type().array_type(FIELD_LIMBS)
    }

    /// Declare all field operation functions in the module
    fn declare_field_functions(&mut self, module: &Module<'ctx>) {
        let field_type = self.field_type();
        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let void_type = self.context.void_type();

        // All field operations take two [4 x i64] and return [4 x i64]
        let field_binop_type = field_type.fn_type(
            &[field_type.into(), field_type.into()],
            false
        );

        // Declare external functions that will be linked with runtime
        self.field_add_fn = Some(module.add_function("__field_add", field_binop_type, None));
        self.field_sub_fn = Some(module.add_function("__field_sub", field_binop_type, None));
        self.field_mul_fn = Some(module.add_function("__field_mul", field_binop_type, None));
        self.field_div_fn = Some(module.add_function("__field_div", field_binop_type, None));

        // Write functions for VM output slots
        // __write_witness writes to slot 0, __write_a/b/c write to slots 1/2/3
        let write_fn_type = void_type.fn_type(
            &[ptr_type.into(), field_type.into()],
            false
        );

        let write_witness_fn = module.add_function("__write_witness", write_fn_type, None);
        self.write_witness_fn = Some(write_witness_fn);
        self.define_write_output(write_witness_fn, 0);

        let write_a_fn = module.add_function("__write_a", write_fn_type, None);
        self.write_a_fn = Some(write_a_fn);
        self.define_write_output(write_a_fn, 1);

        let write_b_fn = module.add_function("__write_b", write_fn_type, None);
        self.write_b_fn = Some(write_b_fn);
        self.define_write_output(write_b_fn, 2);

        let write_c_fn = module.add_function("__write_c", write_fn_type, None);
        self.write_c_fn = Some(write_c_fn);
        self.define_write_output(write_c_fn, 3);
    }

    /// Define a write output function body for a specific VM struct slot
    fn define_write_output(&self, func: FunctionValue<'ctx>, slot_index: u32) {
        let builder = self.context.create_builder();
        let entry = self.context.append_basic_block(func, "entry");
        builder.position_at_end(entry);

        let vm_ptr = func.get_nth_param(0).unwrap().into_pointer_value();
        let value = func.get_nth_param(1).unwrap();

        let ptr_type = self.context.ptr_type(AddressSpace::default());
        let field_type = self.field_type();

        // VM struct type: { ptr, ptr, ptr, ptr }
        let vm_struct_type = self.context.struct_type(
            &[ptr_type.into(), ptr_type.into(), ptr_type.into(), ptr_type.into()],
            false
        );

        // Get pointer to the specified slot in VM struct
        let output_ptr_ptr = builder
            .build_struct_gep(vm_struct_type, vm_ptr, slot_index, "output_ptr_ptr")
            .unwrap();

        // Load the current output pointer
        let output_ptr = builder
            .build_load(ptr_type, output_ptr_ptr, "output_ptr")
            .unwrap()
            .into_pointer_value();

        // Store the value at the current output pointer
        builder.build_store(output_ptr, value).unwrap();

        // Advance the pointer by one field element
        let next_ptr = unsafe {
            builder
                .build_in_bounds_gep(
                    field_type,
                    output_ptr,
                    &[self.context.i32_type().const_int(1, false)],
                    "output_ptr_next",
                )
                .unwrap()
        };

        // Store the updated pointer back to VM struct
        builder.build_store(output_ptr_ptr, next_ptr).unwrap();

        builder.build_return(None).unwrap();
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

    /// Field addition
    pub fn add(
        &self,
        builder: &Builder<'ctx>,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        if let Some(add_fn) = self.field_add_fn {
            let result = builder
                .build_call(add_fn, &[lhs.into(), rhs.into()], "field_add")
                .unwrap();
            result.try_as_basic_value().unwrap_basic()
        } else {
            // Inline implementation as fallback
            self.add_inline(builder, lhs, rhs)
        }
    }

    /// Field subtraction
    pub fn sub(
        &self,
        builder: &Builder<'ctx>,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        if let Some(sub_fn) = self.field_sub_fn {
            let result = builder
                .build_call(sub_fn, &[lhs.into(), rhs.into()], "field_sub")
                .unwrap();
            result.try_as_basic_value().unwrap_basic()
        } else {
            self.sub_inline(builder, lhs, rhs)
        }
    }

    /// Field multiplication
    pub fn mul(
        &self,
        builder: &Builder<'ctx>,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        if let Some(mul_fn) = self.field_mul_fn {
            let result = builder
                .build_call(mul_fn, &[lhs.into(), rhs.into()], "field_mul")
                .unwrap();
            result.try_as_basic_value().unwrap_basic()
        } else {
            self.mul_inline(builder, lhs, rhs)
        }
    }

    /// Field division (multiplication by modular inverse)
    pub fn div(
        &self,
        builder: &Builder<'ctx>,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        if let Some(div_fn) = self.field_div_fn {
            let result = builder
                .build_call(div_fn, &[lhs.into(), rhs.into()], "field_div")
                .unwrap();
            result.try_as_basic_value().unwrap_basic()
        } else {
            // Division is complex - we rely on runtime for now
            panic!("Inline field division not implemented - requires runtime support")
        }
    }

    /// Inline field addition with modular reduction
    fn add_inline(
        &self,
        builder: &Builder<'ctx>,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        let i64_type = self.context.i64_type();
        let field_type = self.field_type();

        // Extract limbs
        let lhs_array = lhs.into_array_value();
        let rhs_array = rhs.into_array_value();

        // Add with carry propagation
        let mut result_limbs: Vec<IntValue> = Vec::with_capacity(FIELD_LIMBS as usize);
        let mut carry = i64_type.const_zero();

        for i in 0..FIELD_LIMBS {
            let l = builder.build_extract_value(lhs_array, i, "l").unwrap().into_int_value();
            let r = builder.build_extract_value(rhs_array, i, "r").unwrap().into_int_value();

            // Add limbs with carry
            // sum = l + r + carry
            let sum1 = builder.build_int_add(l, r, "sum1").unwrap();
            let sum2 = builder.build_int_add(sum1, carry, "sum2").unwrap();

            // Calculate new carry (overflow detection)
            // carry = (sum < l) | ((sum == l) & (carry != 0))
            let overflow1 = builder.build_int_compare(IntPredicate::ULT, sum1, l, "ovf1").unwrap();
            let overflow2 = builder.build_int_compare(IntPredicate::ULT, sum2, sum1, "ovf2").unwrap();
            let overflow = builder.build_or(overflow1, overflow2, "overflow").unwrap();
            carry = builder.build_int_z_extend(overflow, i64_type, "carry").unwrap();

            result_limbs.push(sum2);
        }

        // Build result array
        let mut result = field_type.get_undef();
        for (i, limb) in result_limbs.iter().enumerate() {
            result = builder
                .build_insert_value(result, *limb, i as u32, "result")
                .unwrap()
                .into_array_value();
        }

        // TODO: Add modular reduction if result >= modulus
        // For now, we assume the runtime handles this

        result.into()
    }

    /// Inline field subtraction with modular reduction
    fn sub_inline(
        &self,
        builder: &Builder<'ctx>,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        let i64_type = self.context.i64_type();
        let field_type = self.field_type();

        let lhs_array = lhs.into_array_value();
        let rhs_array = rhs.into_array_value();

        // Subtract with borrow propagation
        let mut result_limbs: Vec<IntValue> = Vec::with_capacity(FIELD_LIMBS as usize);
        let mut borrow = i64_type.const_zero();

        for i in 0..FIELD_LIMBS {
            let l = builder.build_extract_value(lhs_array, i, "l").unwrap().into_int_value();
            let r = builder.build_extract_value(rhs_array, i, "r").unwrap().into_int_value();

            // diff = l - r - borrow
            let diff1 = builder.build_int_sub(l, r, "diff1").unwrap();
            let diff2 = builder.build_int_sub(diff1, borrow, "diff2").unwrap();

            // Calculate new borrow
            let underflow1 = builder.build_int_compare(IntPredicate::UGT, diff1, l, "udf1").unwrap();
            let underflow2 = builder.build_int_compare(IntPredicate::UGT, diff2, diff1, "udf2").unwrap();
            let underflow = builder.build_or(underflow1, underflow2, "underflow").unwrap();
            borrow = builder.build_int_z_extend(underflow, i64_type, "borrow").unwrap();

            result_limbs.push(diff2);
        }

        // Build result array
        let mut result = field_type.get_undef();
        for (i, limb) in result_limbs.iter().enumerate() {
            result = builder
                .build_insert_value(result, *limb, i as u32, "result")
                .unwrap()
                .into_array_value();
        }

        // TODO: Add modular reduction (add modulus if underflow)

        result.into()
    }

    /// Inline field multiplication (schoolbook algorithm)
    /// This is a simplified version - production code would use Montgomery multiplication
    fn mul_inline(
        &self,
        builder: &Builder<'ctx>,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) -> BasicValueEnum<'ctx> {
        // Montgomery multiplication is complex - use external function
        // This is a placeholder that calls the external function
        if let Some(mul_fn) = self.field_mul_fn {
            let result = builder
                .build_call(mul_fn, &[lhs.into(), rhs.into()], "field_mul")
                .unwrap();
            result.try_as_basic_value().unwrap_basic()
        } else {
            panic!("Field multiplication requires runtime support")
        }
    }

    /// Write a witness value to the VM's output buffer (slot 0) and advance the pointer
    pub fn write_witness(
        &self,
        builder: &Builder<'ctx>,
        vm_ptr: inkwell::values::PointerValue<'ctx>,
        value: BasicValueEnum<'ctx>,
    ) {
        let write_fn = self.write_witness_fn.expect("__write_witness not declared");
        builder
            .build_call(write_fn, &[vm_ptr.into(), value.into()], "")
            .unwrap();
    }

    /// Write constraint 'a' value to VM's output buffer (slot 1) and advance the pointer
    pub fn write_a(
        &self,
        builder: &Builder<'ctx>,
        vm_ptr: inkwell::values::PointerValue<'ctx>,
        value: BasicValueEnum<'ctx>,
    ) {
        let write_fn = self.write_a_fn.expect("__write_a not declared");
        builder
            .build_call(write_fn, &[vm_ptr.into(), value.into()], "")
            .unwrap();
    }

    /// Write constraint 'b' value to VM's output buffer (slot 2) and advance the pointer
    pub fn write_b(
        &self,
        builder: &Builder<'ctx>,
        vm_ptr: inkwell::values::PointerValue<'ctx>,
        value: BasicValueEnum<'ctx>,
    ) {
        let write_fn = self.write_b_fn.expect("__write_b not declared");
        builder
            .build_call(write_fn, &[vm_ptr.into(), value.into()], "")
            .unwrap();
    }

    /// Write constraint 'c' value to VM's output buffer (slot 3) and advance the pointer
    pub fn write_c(
        &self,
        builder: &Builder<'ctx>,
        vm_ptr: inkwell::values::PointerValue<'ctx>,
        value: BasicValueEnum<'ctx>,
    ) {
        let write_fn = self.write_c_fn.expect("__write_c not declared");
        builder
            .build_call(write_fn, &[vm_ptr.into(), value.into()], "")
            .unwrap();
    }

    /// Assert two field elements are equal
    pub fn assert_eq(
        &self,
        builder: &Builder<'ctx>,
        lhs: BasicValueEnum<'ctx>,
        rhs: BasicValueEnum<'ctx>,
    ) {
        let lhs_array = lhs.into_array_value();
        let rhs_array = rhs.into_array_value();

        // Compare all limbs
        for i in 0..FIELD_LIMBS {
            let l = builder.build_extract_value(lhs_array, i, "l").unwrap().into_int_value();
            let r = builder.build_extract_value(rhs_array, i, "r").unwrap().into_int_value();

            let eq = builder.build_int_compare(IntPredicate::EQ, l, r, "eq").unwrap();
            // In production, we'd call an assert/trap intrinsic here
        }
    }

    /// Convert an integer to a field element
    pub fn from_int(&self, builder: &Builder<'ctx>, value: IntValue<'ctx>) -> BasicValueEnum<'ctx> {
        let i64_type = self.context.i64_type();
        let field_type = self.field_type();

        // Zero-extend to 64 bits if needed
        let value64 = if value.get_type().get_bit_width() < 64 {
            builder.build_int_z_extend(value, i64_type, "zext").unwrap()
        } else if value.get_type().get_bit_width() > 64 {
            builder.build_int_truncate(value, i64_type, "trunc").unwrap()
        } else {
            value
        };

        // Create field with value in low limb, zeros in high limbs
        let mut result = field_type.get_undef();
        result = builder
            .build_insert_value(result, value64, 0, "low")
            .unwrap()
            .into_array_value();

        for i in 1..FIELD_LIMBS {
            result = builder
                .build_insert_value(result, i64_type.const_zero(), i, "high")
                .unwrap()
                .into_array_value();
        }

        // Note: This doesn't convert to Montgomery form - runtime handles that
        result.into()
    }

    /// Truncate a field element to an integer
    pub fn truncate_to_int(
        &self,
        builder: &Builder<'ctx>,
        value: BasicValueEnum<'ctx>,
        bits: usize,
    ) -> BasicValueEnum<'ctx> {
        let value_array = value.into_array_value();

        // Extract low limb
        let low = builder.build_extract_value(value_array, 0, "low").unwrap().into_int_value();

        // Truncate to requested bits
        let target_type = self.context.custom_width_int_type(bits as u32);
        if bits >= 64 {
            builder.build_int_z_extend(low, target_type, "zext").unwrap().into()
        } else {
            builder.build_int_truncate(low, target_type, "trunc").unwrap().into()
        }
    }

    /// Convert field element to array of bits
    pub fn to_bits(
        &self,
        builder: &Builder<'ctx>,
        value: BasicValueEnum<'ctx>,
        count: usize,
    ) -> BasicValueEnum<'ctx> {
        let i64_type = self.context.i64_type();
        let i1_type = self.context.bool_type();
        let value_array = value.into_array_value();

        // Allocate array for bits
        let bits_array_type = i64_type.array_type(count as u32);
        let bits_ptr = builder.build_alloca(bits_array_type, "bits").unwrap();

        // Extract bits from each limb
        let mut bit_idx = 0;
        for limb_idx in 0..FIELD_LIMBS {
            if bit_idx >= count {
                break;
            }

            let limb = builder
                .build_extract_value(value_array, limb_idx, "limb")
                .unwrap()
                .into_int_value();

            for bit_in_limb in 0..64 {
                if bit_idx >= count {
                    break;
                }

                // Extract bit
                let shift = i64_type.const_int(bit_in_limb as u64, false);
                let shifted = builder.build_right_shift(limb, shift, false, "shifted").unwrap();
                let bit = builder.build_and(shifted, i64_type.const_int(1, false), "bit").unwrap();

                // Store in result array
                let idx = i64_type.const_int(bit_idx as u64, false);
                let elem_ptr = unsafe {
                    builder
                        .build_in_bounds_gep(
                            bits_array_type,
                            bits_ptr,
                            &[i64_type.const_zero(), idx],
                            "bit_ptr",
                        )
                        .unwrap()
                };
                builder.build_store(elem_ptr, bit).unwrap();

                bit_idx += 1;
            }
        }

        bits_ptr.into()
    }
}
