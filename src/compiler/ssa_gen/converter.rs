use std::collections::HashMap;

use super::FunctionConverter;
use crate::compiler::ssa::{FunctionId, SSA};
use noirc_evaluator::ssa::ssa_gen::Ssa as NoirSsa;
use noirc_evaluator::ssa::ir::function::FunctionId as NoirFunctionId;

/// Main converter that converts Noir SSA to custom SSA
pub struct SsaConverter {
    function_converter: FunctionConverter,
    function_mapper: HashMap<NoirFunctionId, FunctionId>,
}

impl SsaConverter {
    pub fn new() -> Self {
        SsaConverter {
            function_converter: FunctionConverter::new(),
            function_mapper: HashMap::new(),
        }
    }

    /// Convert a Noir SSA to a custom SSA
    pub fn convert_noir_ssa(&mut self, noir_ssa: &NoirSsa) -> SSA {
        let mut custom_ssa = SSA::new();

        for (noir_function_id, _) in noir_ssa.functions.iter() {
            if *noir_function_id == noir_ssa.main_id {
                self.function_mapper.insert(*noir_function_id, custom_ssa.get_main_id());
            } else {
                self.function_mapper.insert(*noir_function_id, custom_ssa.add_function());
            };
        }

        for (noir_function_id, noir_function) in noir_ssa.functions.iter() {
            let custom_function = self.function_converter.convert_function(noir_function, &self.function_mapper);
            let function_id = self.function_mapper.get(noir_function_id).unwrap();
            *custom_ssa.get_function_mut(*function_id) = custom_function;
        }

        custom_ssa
    }
}