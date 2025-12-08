use core::panic;
use std::collections::HashMap;

use noirc_evaluator::ssa::{interpreter::value, ir::instruction::Instruction};

use crate::compiler::{analysis::value_definitions::ValueDefinition, ir::r#type::Empty, pass_manager::{DataPoint, Pass}, ssa::{BinaryArithOpKind, Const, OpCode, TupleIdx}};

pub struct MakeStructAccessStatic {}

impl Pass<Empty> for MakeStructAccessStatic {
    fn run(
        &self,
        ssa: &mut crate::compiler::ssa::SSA<Empty>,
        pass_manager: &crate::compiler::pass_manager::PassManager<Empty>,
    ) {
        self.do_run(ssa, pass_manager.get_value_definitions());
    }

    fn pass_info(&self) -> crate::compiler::pass_manager::PassInfo {
        crate::compiler::pass_manager::PassInfo {
            name: "make_struct_access_static",
            needs: vec![DataPoint::ValueDefinitions],
        }
    }

    fn invalidates_cfg(&self) -> bool {
        false
    }
}

impl MakeStructAccessStatic {
    pub fn new() -> Self {
        Self {}
    }

    pub fn do_run(
        &self,
        ssa: &mut crate::compiler::ssa::SSA<Empty>,
        value_definitions: &crate::compiler::analysis::value_definitions::ValueDefinitions<
            Empty,
        >,
    ) {
        for (function_id, function) in ssa.iter_functions_mut() {
            let value_definitions = value_definitions.get_function(*function_id);
            let mut new_blocks = HashMap::new();
            for (bid, mut block) in function.take_blocks().into_iter() {
                let mut new_instructions = Vec::new();
                for instruction in block.take_instructions().into_iter() {
                    match instruction {
                        OpCode::TupleProj {
                            result: item_val_id, 
                            tuple, 
                            idx
                        } => { 
                            // tuple_field_index_val_id = flat_array_index_value_id - flat_array_tuple_starting_index_value_id
                                // flat_array_tuple_starting_index_value_id = tuple_array_index_value_id * stride
                                    // tuple_array_index_value_id = flat_array_index_value_id / stride
                                        // flat_array_index_value_id = tuple_array_index_value_id * stride_value_id
                                        // flat_array_index_value_id = flat_array_tuple_starting_index_value_id_og + tuple_field_index_val_id_og
                                

                            if let TupleIdx::Dynamic(tuple_field_index_val_id, tp) = idx {
                                let tuple_field_index_definition = value_definitions.get_definition(tuple_field_index_val_id);
                                if let ValueDefinition::Instruction(_, _, OpCode::BinaryArithOp { 
                                    kind: BinaryArithOpKind::Sub,
                                    result: tuple_field_index_val_id, 
                                    lhs: flat_array_index_value_id, 
                                    rhs: flat_array_tuple_starting_index_value_id, 
                                }) = tuple_field_index_definition {
                                    let tuple_starting_index_definition = value_definitions.get_definition(*flat_array_tuple_starting_index_value_id);
                                    if let ValueDefinition::Instruction(_, _, OpCode::BinaryArithOp {
                                        kind: BinaryArithOpKind::Mul,
                                        result: _,
                                        lhs: tuple_array_index_value_id,
                                        rhs: stride,
                                    }) = tuple_starting_index_definition {
                                        let tuple_array_index_definition = value_definitions.get_definition(*tuple_array_index_value_id);
                                        if let ValueDefinition::Instruction(_, _, OpCode::BinaryArithOp { 
                                            kind: BinaryArithOpKind::Div, 
                                            result: _, 
                                            lhs: flat_array_index_value_id, 
                                            rhs: stride, 
                                        }) = tuple_array_index_definition {
                                            let flat_array_index_definition = value_definitions.get_definition(*flat_array_index_value_id);
                                            if let ValueDefinition::Instruction(_, _, OpCode::BinaryArithOp { 
                                                kind, 
                                                result, 
                                                lhs, 
                                                rhs }) = flat_array_index_definition {
                                                
                                                match kind {
                                                    BinaryArithOpKind::Mul => {
                                                        new_instructions.push(
                                                            OpCode::TupleProj {
                                                                result: item_val_id, 
                                                                tuple, 
                                                                idx: TupleIdx::Static(0),
                                                            }
                                                        );
                                                    }
                                                    BinaryArithOpKind::Add => {
                                                        let tuple_field_index_val_id_og_definition = value_definitions.get_definition(*rhs);
                                                        if let ValueDefinition::Const(Const::U(sz, val)) = tuple_field_index_val_id_og_definition {
                                                            new_instructions.push(
                                                            OpCode::TupleProj {
                                                                result: item_val_id, 
                                                                tuple, 
                                                                idx: TupleIdx::Static(*val as usize),
                                                            }
                                                        );
                                                        }
                                                    } 
                                                    _ => panic!("Expected Add or Mul operation for flat_array_index_definition")
                                                }
                                            } else {
                                                panic!("Expected instruction for flat_array_index_definition")
                                            }   
                                        } else {
                                            panic!("Expected div instruction for tuple_array_index_definition")
                                        }
                                    } else {
                                        panic!("Expected multiplication instruction for flat_array_tuple_starting_index_value_id");
                                    }
                                } else {
                                    panic!("Expected dynamic tuple index");
                                }
                            } else {
                                panic!("Expected dynamic tuple index");
                            }
                        }
                        _ => {
                            new_instructions.push(instruction);
                        }
                    }
                }
                block.put_instructions(new_instructions);
                new_blocks.insert(bid, block);
            }
            function.put_blocks(new_blocks);
        }
    }
}