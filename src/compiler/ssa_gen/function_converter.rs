use std::collections::HashMap;

use super::TypeConverter;
use crate::compiler::{
    ir::r#type::Empty,
    ssa::{BlockId, Function, FunctionId, Terminator, ValueId},
};
use noirc_evaluator::ssa::ir::{
    basic_block::BasicBlockId,
    function::{Function as NoirFunction, FunctionId as NoirFunctionId},
    instruction::{BinaryOp, Instruction as NoirInstruction, TerminatorInstruction},
    types::NumericType,
    value::{Value, ValueId as NoirValueId},
};

use std::str::FromStr;

pub struct FunctionConverter {
    type_converter: TypeConverter,
    value_mapper: HashMap<NoirValueId, ValueId>,
    block_mapper: HashMap<BasicBlockId, BlockId>,
}

impl FunctionConverter {
    pub fn new() -> Self {
        FunctionConverter {
            type_converter: TypeConverter::new(),
            value_mapper: HashMap::new(),
            block_mapper: HashMap::new(),
        }
    }

    pub fn convert_function(
        &mut self,
        noir_function: &NoirFunction,
        function_mapper: &HashMap<NoirFunctionId, FunctionId>,
    ) -> Function<Empty> {
        let mut custom_function = Function::empty();
        let entry_block_id = custom_function.get_entry_id();

        for return_val in noir_function.returns().iter() {
            let return_type = &noir_function.dfg.values[*return_val].get_type();
            let converted_return_type = self.type_converter.convert_type(return_type);
            custom_function.add_return_type(converted_return_type);
        }

        for (block_id, _) in noir_function.dfg.basic_blocks_iter() {
            if block_id == noir_function.entry_block {
                self.block_mapper.insert(block_id, entry_block_id);
            } else {
                self.block_mapper
                    .insert(block_id, custom_function.add_block());
            }
        }

        for (block_id, block) in noir_function.dfg.basic_blocks_iter() {
            let custom_block_id = *self.block_mapper.get(&block_id).unwrap();

            for noir_param_id in block.parameters() {
                let param_value = &noir_function.dfg.values[*noir_param_id];
                let param_type = param_value.get_type();
                let converted_type = self.type_converter.convert_type(&param_type);
                let param_id = custom_function.add_parameter(custom_block_id, converted_type);
                self.value_mapper.insert(*noir_param_id, param_id);
            }

            for noir_instruction_id in block.instructions() {
                let noir_instruction = &noir_function.dfg.instructions[*noir_instruction_id];
                match noir_instruction {
                    NoirInstruction::Binary(binary) => {
                        let left_id = binary.lhs;
                        let right_id = binary.rhs;
                        let result_id =
                            noir_function.dfg.instruction_results(*noir_instruction_id)[0];
                        let left_value = &noir_function.dfg.values[left_id];
                        let right_value = &noir_function.dfg.values[right_id];
                        let left_value =
                            self.convert_value(&mut custom_function, left_id, left_value);
                        let right_value =
                            self.convert_value(&mut custom_function, right_id, right_value);
                        let rr_id = match binary.operator {
                            BinaryOp::Add { unchecked } => {
                                custom_function.push_add(custom_block_id, left_value, right_value)
                            }
                            BinaryOp::Lt => {
                                custom_function.push_lt(custom_block_id, left_value, right_value)
                            }
                            BinaryOp::Mul { unchecked } => {
                                custom_function.push_mul(custom_block_id, left_value, right_value)
                            }
                            BinaryOp::Eq => {
                                custom_function.push_eq(custom_block_id, left_value, right_value)
                            }
                            _ => panic!("Unsupported binary operation: {:?}", binary.operator),
                        };
                        self.value_mapper.insert(result_id, rr_id);
                    }
                    NoirInstruction::Call { func, arguments } => {
                        let function_value = &noir_function.dfg.values[*func];

                        if let Value::Function(func) = function_value {
                            let result_ids =
                                noir_function.dfg.instruction_results(*noir_instruction_id);

                            let mut converted_args = Vec::new();
                            for arg_id in arguments {
                                let arg_value = &noir_function.dfg.values[*arg_id];
                                let converted_arg =
                                    self.convert_value(&mut custom_function, *arg_id, arg_value);
                                converted_args.push(converted_arg);
                            }

                            let function_id = function_mapper.get(func).unwrap();

                            let return_values = custom_function.push_call(
                                custom_block_id,
                                *function_id,
                                converted_args,
                                result_ids.len(),
                            );

                            for (result_id, return_value) in
                                result_ids.iter().zip(return_values.iter())
                            {
                                self.value_mapper.insert(*result_id, *return_value);
                            }
                        } else {
                            panic!(
                                "Call instruction with non-constant function value not supported: {:?}",
                                function_value
                            );
                        }
                    }
                    NoirInstruction::Constrain(l, r, _) => {
                        let left_value = &noir_function.dfg.values[*l];
                        let right_value = &noir_function.dfg.values[*r];
                        let left_converted =
                            self.convert_value(&mut custom_function, *l, left_value);
                        let right_converted =
                            self.convert_value(&mut custom_function, *r, right_value);

                        custom_function.push_assert_eq(
                            custom_block_id,
                            left_converted,
                            right_converted,
                        );
                    }
                    NoirInstruction::Allocate => {
                        let result_id =
                            noir_function.dfg.instruction_results(*noir_instruction_id)[0];
                        let result_value = &noir_function.dfg.values[result_id];
                        let result_type = result_value.get_type();

                        let converted_type = match &*result_type {
                            noirc_evaluator::ssa::ir::types::Type::Reference(inner) => {
                                self.type_converter.convert_type(&inner)
                            }
                            _ => panic!(
                                "Allocate instruction result should be a reference type, got: {:?}",
                                result_type
                            ),
                        };

                        let alloc_result =
                            custom_function.push_alloc(custom_block_id, converted_type, Empty);

                        self.value_mapper.insert(result_id, alloc_result);
                    }
                    NoirInstruction::Store { address, value } => {
                        let address_value = &noir_function.dfg.values[*address];
                        let value_value = &noir_function.dfg.values[*value];
                        let address_converted =
                            self.convert_value(&mut custom_function, *address, address_value);
                        let value_converted =
                            self.convert_value(&mut custom_function, *value, value_value);

                        custom_function.push_store(
                            custom_block_id,
                            address_converted,
                            value_converted,
                        );
                    }
                    NoirInstruction::ArrayGet { array, index, .. } => {
                        let array_value = &noir_function.dfg.values[*array];
                        let index_value = &noir_function.dfg.values[*index];
                        let array_converted =
                            self.convert_value(&mut custom_function, *array, array_value);
                        let index_converted =
                            self.convert_value(&mut custom_function, *index, index_value);

                        let result_id =
                            noir_function.dfg.instruction_results(*noir_instruction_id)[0];

                        let array_get_result = custom_function.push_array_get(
                            custom_block_id,
                            array_converted,
                            index_converted,
                        );

                        self.value_mapper.insert(result_id, array_get_result);
                    }
                    NoirInstruction::Load { address } => {
                        let address_value = &noir_function.dfg.values[*address];
                        let address_converted =
                            self.convert_value(&mut custom_function, *address, address_value);

                        let result_id =
                            noir_function.dfg.instruction_results(*noir_instruction_id)[0];

                        let load_result =
                            custom_function.push_load(custom_block_id, address_converted);

                        self.value_mapper.insert(result_id, load_result);
                    }
                    _ => panic!("Unsupported instruction: {:?}", noir_instruction),
                }
            }

            match block.terminator() {
                Some(TerminatorInstruction::JmpIf {
                    condition,
                    then_destination,
                    else_destination,
                    ..
                }) => {
                    let condition_converted = self.convert_value(
                        &mut custom_function,
                        *condition,
                        &noir_function.dfg.values[*condition],
                    );
                    let then_destination_converted =
                        *self.block_mapper.get(then_destination).unwrap();
                    let else_destination_converted =
                        *self.block_mapper.get(else_destination).unwrap();
                    custom_function.terminate_block_with_jmp_if(
                        custom_block_id,
                        condition_converted,
                        then_destination_converted,
                        else_destination_converted,
                    );
                }
                Some(TerminatorInstruction::Jmp {
                    destination,
                    arguments,
                    ..
                }) => {
                    let destination_converted = *self.block_mapper.get(destination).unwrap();
                    let arguments_converted = arguments
                        .iter()
                        .map(|id| {
                            self.convert_value(
                                &mut custom_function,
                                *id,
                                &noir_function.dfg.values[*id],
                            )
                        })
                        .collect();
                    custom_function.terminate_block_with_jmp(
                        custom_block_id,
                        destination_converted,
                        arguments_converted,
                    );
                }
                Some(TerminatorInstruction::Return { return_values, .. }) => {
                    let return_values_converted = return_values
                        .iter()
                        .map(|id| {
                            self.convert_value(
                                &mut custom_function,
                                *id,
                                &noir_function.dfg.values[*id],
                            )
                        })
                        .collect();
                    custom_function
                        .terminate_block_with_return(custom_block_id, return_values_converted);
                }
                _ => panic!("Unsupported terminator: {:?}", block.terminator()),
            }
        }

        custom_function
    }

    fn convert_value(
        &mut self,
        custom_function: &mut Function<Empty>,
        noir_value_id: NoirValueId,
        noir_value: &Value,
    ) -> ValueId {
        match noir_value {
            Value::NumericConstant { constant, typ } => match typ {
                NumericType::Unsigned { bit_size: 32 } => {
                    let custom_value_id = custom_function
                        .push_u32_const(constant.to_string().parse::<u32>().unwrap());
                    self.value_mapper.insert(noir_value_id, custom_value_id);
                    custom_value_id
                }
                NumericType::Unsigned { bit_size: 1 } => {
                    let u32_value = constant.to_string().parse::<u32>().unwrap();
                    let bool_value = u32_value != 0;
                    let custom_value_id = custom_function.push_bool_const(bool_value);
                    self.value_mapper.insert(noir_value_id, custom_value_id);
                    custom_value_id
                }
                NumericType::NativeField => {
                    let field_value = constant.to_string();
                    let field_value = ark_bn254::Fr::from_str(&field_value).unwrap();
                    let custom_value_id = custom_function.push_field_const(field_value);
                    self.value_mapper.insert(noir_value_id, custom_value_id);
                    custom_value_id
                }
                _ => {
                    panic!("Unsupported numeric type: {:?}", typ);
                }
            },
            _ => *self.value_mapper.get(&noir_value_id).unwrap(),
        }
    }
}
