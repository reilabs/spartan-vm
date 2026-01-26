use crate::compiler::{analysis::value_definitions::ValueDefinitions, ir::r#type::{Empty, Type, TypeExpr}, pass_manager::{DataPoint, Pass, PassInfo}, ssa::{OpCode, SeqType}};

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
        let main_id = ssa.get_main_id();
        let _value_definitions = value_definitions.get_function(main_id);
        let function = ssa.get_main_mut();

        let params: Vec<_> = function.get_entry().get_parameters().cloned().collect();

        let mut new_instructions = Vec::new();
        let mut new_parameters = Vec::new();

        for (value_id, typ) in params.iter() {
            if let TypeExpr::Array(inner, size) = &typ.expr {
                let mut elems = Vec::new();
                for _ in 0..*size {
                    let fresh_id = function.fresh_value();
                    let inner_type: Type<Empty> = *inner.clone();
                    new_parameters.push((fresh_id, inner_type));
                    elems.push(fresh_id);
                }
                new_instructions.push(OpCode::MkSeq {
                    result: *value_id,
                    elems,
                    seq_type: SeqType::Array(*size),
                    elem_type: *inner.clone(),
                });
            }
        }

        let entry_id = function.get_entry_id();
        let entry_block = function.get_block_mut(entry_id);

        for instruction in entry_block.take_instructions().into_iter() {
            new_instructions.push(instruction);
        }
        entry_block.put_parameters(new_parameters);
        entry_block.put_instructions(new_instructions);
    }
}
