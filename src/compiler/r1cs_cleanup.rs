use crate::compiler::{
    passes::fix_double_jumps::ValueReplacements,
    ssa::{OpCode, SSA},
    taint_analysis::ConstantTaint,
};

pub struct R1CSCleanup {}

impl R1CSCleanup {
    pub fn new() -> Self {
        Self {}
    }

    pub fn run(&self, ssa: &mut SSA<ConstantTaint>) {
        for (_, function) in ssa.iter_functions_mut() {
            let mut replacements = ValueReplacements::new();

            for (_, block) in function.get_blocks_mut() {
                for instruction in block.get_instructions_mut() {
                    match instruction {
                        OpCode::WriteWitness(r, b, _) => {
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
