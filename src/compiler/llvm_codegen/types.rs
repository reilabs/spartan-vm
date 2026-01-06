//! Type conversion from Spartan VM types to LLVM types

use inkwell::context::Context;
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::AddressSpace;

use crate::compiler::ir::r#type::{Type, TypeExpr};
use crate::compiler::taint_analysis::ConstantTaint;

/// Number of 64-bit limbs used to represent a BN254 field element
pub const FIELD_LIMBS: u32 = 4;

/// Converts Spartan VM types to LLVM types
pub struct TypeConverter<'ctx> {
    context: &'ctx Context,
}

impl<'ctx> TypeConverter<'ctx> {
    pub fn new(context: &'ctx Context) -> Self {
        Self { context }
    }

    /// Convert a Spartan type to an LLVM type
    pub fn convert_type(&self, ty: &Type<ConstantTaint>) -> BasicTypeEnum<'ctx> {
        match &ty.expr {
            TypeExpr::Field => {
                // Field is represented as [4 x i64] - 256 bits in Montgomery form
                self.field_type().into()
            }
            TypeExpr::BoxedField => {
                // BoxedField is a pointer to a field
                // For simplicity in LLVM, we'll represent it the same as Field
                // In a more sophisticated implementation, this would be a pointer
                self.field_type().into()
            }
            TypeExpr::U(bits) => {
                // Map to appropriate LLVM integer type
                self.int_type(*bits).into()
            }
            TypeExpr::Array(elem_type, size) => {
                // Fixed-size array - represented as pointer to first element
                let elem_llvm_type = self.convert_type(elem_type);
                let array_type = elem_llvm_type.array_type(*size as u32);
                self.context.ptr_type(AddressSpace::default()).into()
            }
            TypeExpr::Slice(elem_type) => {
                // Slice - pointer type (dynamic size)
                self.context.ptr_type(AddressSpace::default()).into()
            }
            TypeExpr::Ref(inner_type) => {
                // Reference/pointer
                self.context.ptr_type(AddressSpace::default()).into()
            }
        }
    }

    /// Get the LLVM type for a field element ([4 x i64])
    pub fn field_type(&self) -> inkwell::types::ArrayType<'ctx> {
        self.context.i64_type().array_type(FIELD_LIMBS)
    }

    /// Get an integer type of the specified bit width
    pub fn int_type(&self, bits: usize) -> inkwell::types::IntType<'ctx> {
        match bits {
            1 => self.context.bool_type(),
            8 => self.context.i8_type(),
            16 => self.context.i16_type(),
            32 => self.context.i32_type(),
            64 => self.context.i64_type(),
            128 => self.context.i128_type(),
            _ => self.context.custom_width_int_type(bits as u32),
        }
    }

    /// Get the size in bytes of a type
    pub fn type_size(&self, ty: &Type<ConstantTaint>) -> u64 {
        match &ty.expr {
            TypeExpr::Field => FIELD_LIMBS as u64 * 8, // 4 * 8 = 32 bytes
            TypeExpr::BoxedField => FIELD_LIMBS as u64 * 8,
            TypeExpr::U(bits) => (*bits as u64 + 7) / 8,
            TypeExpr::Array(elem_type, size) => self.type_size(elem_type) * (*size as u64),
            TypeExpr::Slice(_) => 8, // Pointer size
            TypeExpr::Ref(_) => 8,   // Pointer size
        }
    }
}
