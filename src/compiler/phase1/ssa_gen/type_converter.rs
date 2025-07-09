use crate::compiler::phase1::ssa::Type;
use std::sync::Arc;
use noirc_evaluator::ssa::ir::types::{Type as NoirType, NumericType};

pub struct TypeConverter;

impl TypeConverter {
    pub fn new() -> Self {
        TypeConverter
    }

    pub fn convert_type(&self, noir_type: &NoirType) -> Type {
        match noir_type {
            NoirType::Numeric(numeric) => match numeric {
                NumericType::NativeField => Type::Field,
                NumericType::Unsigned { bit_size: 1 } => Type::Bool,
                NumericType::Unsigned { bit_size: 32 } => Type::U32,
                NumericType::Unsigned { bit_size } => {
                    panic!("Unsupported unsigned integer size: {}", bit_size)
                }
                NumericType::Signed { bit_size } => {
                    panic!("Signed integers not supported: {} bits", bit_size)
                }
            },
            NoirType::Reference(inner) => {
                let inner_converted = self.convert_type(inner);
                Type::Ref(Box::new(inner_converted))
            }
            NoirType::Array(element_types, size) => {
                if element_types.len() != 1 {
                    panic!("Only single-type arrays are supported, got element_types = {:?}", element_types)
                }
                let element_type = &element_types[0];
                let converted_element = self.convert_type(element_type);
                Type::Array(Box::new(converted_element), (*size).try_into().unwrap())
            }
            NoirType::Slice(_) => {
                panic!("Slice types are not supported in custom SSA")
            }
            NoirType::Function => {
                panic!("Function types are not supported in custom SSA")
            }
        }
    }
} 