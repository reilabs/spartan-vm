use std::collections::HashMap;

use crate::compiler::{
    ir::r#type::{Type, TypeExpr},
    pass_manager::{DataPoint, Pass},
    ssa::{CastTarget, Const, DMatrix, OpCode},
    taint_analysis::ConstantTaint,
};

pub struct BoxFields {}

impl Pass<ConstantTaint> for BoxFields {
    fn run(
        &self,
        ssa: &mut crate::compiler::ssa::SSA<ConstantTaint>,
        pass_manager: &crate::compiler::pass_manager::PassManager<ConstantTaint>,
    ) {
        self.do_run(ssa, pass_manager.get_type_info());
    }

    fn pass_info(&self) -> crate::compiler::pass_manager::PassInfo {
        crate::compiler::pass_manager::PassInfo {
            name: "box_fields",
            invalidates: vec![DataPoint::Types],
            needs: vec![DataPoint::Types],
        }
    }
}

impl BoxFields {
    pub fn new() -> Self {
        Self {}
    }

    pub fn do_run(
        &self,
        ssa: &mut crate::compiler::ssa::SSA<ConstantTaint>,
        type_info: &crate::compiler::analysis::types::TypeInfo<ConstantTaint>,
    ) {
        for (function_id, function) in ssa.iter_functions_mut() {
            for (_, constant) in function.iter_consts_mut() {
                let new = match constant {
                    Const::U(s, value) => Const::U(*s, *value),
                    Const::Field(value) => Const::BoxedField(*value),
                    Const::BoxedField(value) => Const::BoxedField(*value),
                };
                *constant = new;
            }
            let mut new_blocks = HashMap::new();
            for (bid, mut block) in function.take_blocks().into_iter() {
                let old_params = block.take_parameters();
                let new_params = old_params
                    .into_iter()
                    .map(|(r, tp)| (r, self.box_fields_in_type(&tp)))
                    .collect();
                block.put_parameters(new_params);
                let mut new_instructions = vec![];
                for instruction in block.take_instructions().into_iter() {
                    match instruction {
                        OpCode::Cast(r, v, t) => {
                            let i = if matches!(t, CastTarget::Field) {
                                OpCode::Cast(r, v, CastTarget::BoxedField)
                            } else {
                                OpCode::Cast(r, v, t)
                            };
                            new_instructions.push(i);
                        }
                        OpCode::FreshWitness(r, tp) => {
                            let i = OpCode::FreshWitness(r, self.box_fields_in_type(&tp));
                            new_instructions.push(i);
                        }
                        OpCode::MkSeq(r, vs, s, tp) => {
                            let i = OpCode::MkSeq(r, vs.clone(), s, self.box_fields_in_type(&tp));
                            new_instructions.push(i);
                        }
                        OpCode::Alloc(r, tp, v) => {
                            let i = OpCode::Alloc(r, self.box_fields_in_type(&tp), v);
                            new_instructions.push(i);
                        }
                        OpCode::Constrain(a, b, c) => {
                            let new_val = function.fresh_value();
                            new_instructions.push(OpCode::NextDCoeff(new_val));
                            new_instructions.push(OpCode::BumpD(DMatrix::A, a, new_val));
                            new_instructions.push(OpCode::BumpD(DMatrix::B, b, new_val));
                            new_instructions.push(OpCode::BumpD(DMatrix::C, c, new_val));
                        }
                        OpCode::Cmp { .. }
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
                        | OpCode::MemOp { .. }
                        | OpCode::WriteWitness { .. }
                        | OpCode::NextDCoeff { .. }
                        | OpCode::BumpD { .. } => new_instructions.push(instruction),
                    };
                }
                block.put_instructions(new_instructions);
                new_blocks.insert(bid, block);
            }
            function.put_blocks(new_blocks);
        }
    }

    fn box_fields_in_type(&self, tp: &Type<ConstantTaint>) -> Type<ConstantTaint> {
        match &tp.expr {
            TypeExpr::Field => Type::boxed_field(tp.annotation.clone()),
            TypeExpr::U(_) => tp.clone(),
            TypeExpr::Array(inner, size) => {
                Type::array_of(self.box_fields_in_type(inner), *size, tp.annotation.clone())
            }
            TypeExpr::Slice(inner) => {
                Type::slice_of(self.box_fields_in_type(inner), tp.annotation.clone())
            }
            TypeExpr::Ref(inner) => {
                Type::ref_of(self.box_fields_in_type(inner), tp.annotation.clone())
            }
            TypeExpr::BoxedField => tp.clone(),
        }
    }
}
