use std::collections::HashMap;

use super::FunctionConverter;
use crate::compiler::ir::r#type::Empty;
use crate::compiler::ssa::{FunctionId, SSA, ValueId};
use noirc_evaluator::ssa::ir::dfg::DataFlowGraph;
use noirc_evaluator::ssa::ir::function::FunctionId as NoirFunctionId;
use noirc_evaluator::ssa::ir::value::ValueId as NoirValueId;
use noirc_evaluator::ssa::ssa_gen::Ssa as NoirSsa;

pub struct SsaConverter {
    function_mapper: HashMap<NoirFunctionId, FunctionId>,
    global_value_mapper: HashMap<NoirValueId, ValueId>,
}

impl SsaConverter {
    pub fn new() -> Self {
        SsaConverter {
            function_mapper: HashMap::new(),
            global_value_mapper: HashMap::new(),
        }
    }

    pub fn convert_noir_ssa(&mut self, noir_ssa: &NoirSsa) -> SSA<Empty> {
        let mut custom_ssa = SSA::new();

        for (noir_function_id, _) in noir_ssa.functions.iter() {
            if *noir_function_id == noir_ssa.main_id {
                self.function_mapper
                    .insert(*noir_function_id, custom_ssa.get_main_id());
            } else {
                self.function_mapper.insert(
                    *noir_function_id,
                    custom_ssa
                        .add_function(noir_ssa.functions[noir_function_id].name().to_string()),
                );
            };
        }

        let mut globals_init = false;
        // for noir_value_id in noir_ssa

        for (noir_function_id, noir_function) in noir_ssa.functions.iter() {
            if !globals_init {
                let globals = DataFlowGraph::from(noir_function.dfg.globals.as_ref().clone());
                let mut cur_val = 0;
                for (noir_value_id, _) in globals.values.iter() {
                    self.global_value_mapper
                        .insert(noir_value_id, ValueId(cur_val));
                    cur_val += 1;
                }
                globals_init = true;
            }

            let mut function_converter = FunctionConverter::new(self.global_value_mapper.clone());
            let custom_function =
                function_converter.convert_function(noir_function, &self.function_mapper);
            let function_id = self.function_mapper.get(noir_function_id).unwrap();
            *custom_ssa.get_function_mut(*function_id) = custom_function;
        }

        custom_ssa
    }
}
