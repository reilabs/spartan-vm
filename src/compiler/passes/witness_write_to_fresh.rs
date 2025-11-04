use crate::compiler::{
    ir::r#type::{Type, TypeExpr},
    pass_manager::{DataPoint, Pass},
    ssa::OpCode,
    taint_analysis::ConstantTaint,
};

pub struct WitnessWriteToFresh {}

impl Pass<ConstantTaint> for WitnessWriteToFresh {
    fn run(
        &self,
        ssa: &mut crate::compiler::ssa::SSA<ConstantTaint>,
        pass_manager: &crate::compiler::pass_manager::PassManager<ConstantTaint>,
    ) {
        self.do_run(ssa, pass_manager.get_type_info());
    }

    fn pass_info(&self) -> crate::compiler::pass_manager::PassInfo {
        crate::compiler::pass_manager::PassInfo {
            name: "witness_write_to_fresh",
            needs: vec![DataPoint::Types],
        }
    }

    fn invalidates_cfg(&self) -> bool {
        false
    }

}

impl WitnessWriteToFresh {
    pub fn new() -> Self {
        Self {}
    }

    pub fn do_run(
        &self,
        ssa: &mut crate::compiler::ssa::SSA<ConstantTaint>,
        type_info: &crate::compiler::analysis::types::TypeInfo<ConstantTaint>,
    ) {
        let main_id = ssa.get_main_id();
        let main_function = ssa.get_function_mut(main_id);
        let main_block = main_function.get_block_mut(main_function.get_entry_id());
        let old_params = main_block.take_parameters();
        let old_instructions = main_block.take_instructions();
        let new_instructions = old_params
            .into_iter()
            .map(|(r, tp)| {
                assert!(matches!(tp.expr, TypeExpr::Field));
                OpCode::FreshWitness {
                    result: r,
                    result_type: Type::field(ConstantTaint::Witness)
                }
            })
            .chain(old_instructions.into_iter())
            .collect();
        main_block.put_instructions(new_instructions);

        for (function_id, function) in ssa.iter_functions_mut() {
            println!("Function {}:", function.get_name());
            for (_, block) in function.get_blocks_mut() {
                for instruction in block.get_instructions_mut() {
                    let new_instruction = match instruction {
                        OpCode::WriteWitness { result: r, value: _, witness_annotation: _ } => {
                            let tp = type_info
                                .get_function(*function_id)
                                .get_value_type(r.unwrap());
                            if !matches!(tp.expr, TypeExpr::Field) {
                                panic!("Expected field type, got {:?}", tp);
                            }
                            OpCode::FreshWitness {
                                result: r.unwrap(),
                                result_type: Type::field(ConstantTaint::Witness)
                            }
                        }
                        OpCode::Cmp { .. }
                        | OpCode::Cast { .. }
                        | OpCode::MkSeq { .. }
                        | OpCode::Alloc { .. }
                        | OpCode::BinaryArithOp { .. }
                        | OpCode::Truncate { .. }
                        | OpCode::Not { .. }
                        | OpCode::Store { .. }
                        | OpCode::Load { .. }
                        | OpCode::AssertEq { .. }
                        | OpCode::AssertR1C { .. }
                        | OpCode::Call { .. }
                        | OpCode::ArrayGet { .. }
                        | OpCode::ArraySet { .. }
                        | OpCode::Select { .. }
                        | OpCode::ToBits { .. }
                        | OpCode::ToRadix { .. }
                        | OpCode::MemOp { .. }
                        | OpCode::FreshWitness { .. }
                        | OpCode::Constrain { .. }
                        | OpCode::NextDCoeff { .. }
                        | OpCode::BoxField { .. }
                        | OpCode::UnboxField { .. }
                        | OpCode::MulConst { .. }
                        | OpCode::BumpD { .. }
                        | OpCode::Rangecheck { .. }
                        | OpCode::Lookup { .. }
                        | OpCode::DLookup { .. }
                        | OpCode::ReadGlobal { .. }
                        | OpCode::Todo { .. } => instruction.clone(),
                    };
                    *instruction = new_instruction;
                }
            }
        }
    }
}
