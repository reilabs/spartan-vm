use std::collections::HashMap;

use crate::compiler::{analysis::value_definitions::ValueDefinitions, ir::r#type::Empty, pass_manager::{DataPoint, Pass, PassInfo}};

pub struct RebuildMainParams {}

impl Pass<Empty> for RebuildMainParams {
    fn run(
        &self,
        ssa: &mut crate::compiler::ssa::SSA<Empty>,
        pass_manager: &crate::compiler::pass_manager::PassManager<Empty>,
    ) {
        self.do_run(ssa, pass_manager.get_value_definitions());
    }

    fn pass_info(&self) -> PassInfo {
        PassInfo {
            name: "rebuild_main_params",
            needs: vec![DataPoint::ValueDefinitions],
        }
    }

    fn invalidates_cfg(&self) -> bool {
        false
    }
}

impl RebuildMainParams {
    pub fn new() -> Self {
        Self {}
    }

    pub fn do_run(
        &self,
        ssa: &mut crate::compiler::ssa::SSA<Empty>,
        value_definitions: &ValueDefinitions<Empty>,
    ) {
        for (function_id, function) in ssa.iter_functions_mut() {
            let value_definitions = value_definitions.get_function(*function_id);
            let mut new_blocks = HashMap::new();
            for (bid, mut block) in function.take_blocks().into_iter() {
                let mut new_instructions = Vec::new();
                for instruction in block.take_instructions().into_iter() {
                    new_instructions.push(instruction);
                }
                block.put_instructions(new_instructions);
                new_blocks.insert(bid, block);
            }
            function.put_blocks(new_blocks);
        }
    }
}
