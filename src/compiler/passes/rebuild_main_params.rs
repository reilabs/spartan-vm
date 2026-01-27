use noirc_evaluator::ssa::interpreter::value;

use crate::compiler::{analysis::value_definitions::ValueDefinitions, ir::r#type::{Empty, Type, TypeExpr}, pass_manager::{DataPoint, Pass, PassInfo}, passes::rebuild_main_params, ssa::{Function, LookupTarget, OpCode, SeqType, ValueId}};

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
            let (_, child_parameters, child_instructions) = Self::reconstruct_param(Some(value_id), typ, function);
            new_parameters.extend(child_parameters);
            new_instructions.extend(child_instructions);
        }

        let entry_id = function.get_entry_id();
        let entry_block = function.get_block_mut(entry_id);

        for instruction in entry_block.take_instructions().into_iter() {
            new_instructions.push(instruction);
        }
        entry_block.put_parameters(new_parameters);
        entry_block.put_instructions(new_instructions);
    }

    fn reconstruct_param (value_id: Option<&ValueId>, typ: &Type<Empty>, function: &mut Function<Empty>) -> (ValueId, Vec<(ValueId, Type<Empty>)>, Vec<OpCode<Empty>>) {
        let mut new_instructions = Vec::new();
        let mut new_parameters = Vec::new();

        let value_id = if let Some(id) = value_id {
            id
        } else {
            &(function.fresh_value())
        };

        match &typ.expr {
            TypeExpr::Field => {
                new_parameters.push((*value_id, typ.clone()))
            } 
            TypeExpr::U(size) => {
                new_parameters.push((*value_id, Type{expr: TypeExpr::Field, annotation: Empty}));
                new_instructions.push(
                    OpCode::Rangecheck {
                        value: *value_id,
                        max_bits: *size,
                    }
                )
            }
            TypeExpr::Array(inner, size) => {
                let mut elems = Vec::new();
                for _ in 0..*size {
                    let (child_id, child_parameters, child_instructions) = Self::reconstruct_param(None, inner, function);
                    elems.push(child_id);
                    new_parameters.extend(child_parameters);
                    new_instructions.extend(child_instructions);
                }
                new_instructions.push(OpCode::MkSeq {
                    result: *value_id,
                    elems,
                    seq_type: SeqType::Array(*size),
                    elem_type: *inner.clone(),
                });
            }
            TypeExpr::Tuple(element_types) => {
                let mut elems = Vec::new();
                let mut elem_types = Vec::new();
                for elem_type in element_types {
                    let (child_id, child_parameters, child_instructions) = Self::reconstruct_param(None, elem_type, function);
                    elems.push(child_id);
                    elem_types.push(elem_type.clone());
                    new_parameters.extend(child_parameters);
                    new_instructions.extend(child_instructions);
                }
                new_instructions.push(OpCode::MkTuple {
                    result: *value_id,
                    elems,
                    element_types: elem_types,
                });
            }
            _ => todo!("Not implemented yet")
        }

        return (*value_id, new_parameters, new_instructions);
    }
}
