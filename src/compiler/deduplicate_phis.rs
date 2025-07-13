use std::collections::HashMap;

use crate::compiler::ssa::{BlockId, SSA, Terminator, ValueId};

pub struct DeduplicatePhis {}

impl DeduplicatePhis {
    pub fn new() -> Self {
        Self {}
    }

    pub fn run(&self, ssa: &mut SSA) {
        for (_, function) in ssa.iter_functions_mut() {
            let mut unifications: HashMap<(BlockId, Vec<ValueId>), Vec<BlockId>> = HashMap::new();
            for (block_id, block) in function.get_blocks() {
                match block.get_terminator() {
                    Some(Terminator::Jmp(target, inputs)) => {
                        if inputs.len() > 0 {
                            unifications
                                .entry((*target, inputs.clone()))
                                .or_insert(vec![])
                                .push(*block_id);
                        }
                    }
                    _ => {}
                }
            }

            for ((target, inputs), blocks) in unifications {
                if blocks.len() <= 1 {
                    continue;
                }
                let new_block = function.add_block();
                function.terminate_block_with_jmp(new_block, target, inputs);
                for block_id in blocks {
                    function.terminate_block_with_jmp(block_id, new_block, vec![]);
                }
            }
        }
    }
}
