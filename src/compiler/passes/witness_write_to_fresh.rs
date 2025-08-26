use crate::compiler::{pass_manager::Pass, ssa::OpCode, taint_analysis::ConstantTaint};

pub struct WitnessWriteToFresh {}

impl Pass<ConstantTaint> for WitnessWriteToFresh {
    fn run(
        &self,
        ssa: &mut crate::compiler::ssa::SSA<ConstantTaint>,
        _pass_manager: &crate::compiler::pass_manager::PassManager<ConstantTaint>,
    ) {
        self.do_run(ssa);
    }

    fn pass_info(&self) -> crate::compiler::pass_manager::PassInfo {
        crate::compiler::pass_manager::PassInfo {
            name: "witness_write_to_fresh",
            invalidates: vec![],
            needs: vec![],
        }
    }
}

impl WitnessWriteToFresh {
    pub fn new() -> Self {
        Self {}
    }

    pub fn do_run(&self, ssa: &mut crate::compiler::ssa::SSA<ConstantTaint>) {
        for (_, function) in ssa.iter_functions_mut() {
            for (_, block) in function.get_blocks_mut() {
                for instruction in block.get_instructions_mut() {
                    let new_instruction = if let OpCode::WriteWitness(r, _, _) = instruction {
                        OpCode::FreshWitness(r.unwrap(), ConstantTaint::Witness)
                    } else {
                        instruction.clone()
                    };
                    *instruction = new_instruction;
                }
            }
        }
    }
}
