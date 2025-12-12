use crate::compiler::{
    pass_manager::{Pass, PassInfo, PassManager},
    passes::fix_double_jumps::ValueReplacements,
    ssa::{OpCode, SSA},
    taint_analysis::ConstantTaint,
};

pub struct WitnessWriteToVoid {}

impl Pass<ConstantTaint> for WitnessWriteToVoid {
    fn run(&self, ssa: &mut SSA<ConstantTaint>, _pass_manager: &PassManager<ConstantTaint>) {
        self.do_run(ssa);
    }
    fn pass_info(&self) -> PassInfo {
        PassInfo {
            name: "witness_write_to_void",
            needs: vec![],
        }
    }
    fn invalidates_cfg(&self) -> bool {
        false
    }
}

impl WitnessWriteToVoid {
    pub fn new() -> Self {
        Self {}
    }

    fn do_run(&self, ssa: &mut SSA<ConstantTaint>) {
        for (_, function) in ssa.iter_functions_mut() {
            let mut replacements = ValueReplacements::new();

            for (_, block) in function.get_blocks_mut() {
                for instruction in block.get_instructions_mut() {
                    match instruction {
                        OpCode::WriteWitness {
                            result: r,
                            value: b,
                            witness_annotation: _,
                        } => {
                            if let Some(r) = r {
                                replacements.insert(*r, *b);
                            }
                            *r = None;
                        }
                        _ => {}
                    }
                }
            }

            for (_, block) in function.get_blocks_mut() {
                for instruction in block.get_instructions_mut() {
                    replacements.replace_instruction(instruction);
                }
                replacements.replace_terminator(block.get_terminator_mut());
            }
        }
    }
}
