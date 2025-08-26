use std::collections::HashMap;

use crate::compiler::{
    ir::r#type::{Type, TypeExpr},
    pass_manager::{DataPoint, Pass},
    ssa::{BinaryArithOpKind, CastTarget, Const, DMatrix, OpCode},
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
            let type_info = type_info.get_function(*function_id);
            for rtp in function.iter_returns_mut() {
                *rtp = self.box_fields_in_type(rtp);
            }
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
                            let v_type = type_info.get_value_type(v);
                            let v = if v_type.is_field() {
                                let new_v = function.fresh_value();
                                new_instructions.push(OpCode::UnboxField(new_v, v));
                                new_v
                            } else {
                                v
                            };
                            
                            if matches!(t, CastTarget::Field) {
                                let new_r = function.fresh_value();
                                new_instructions.push(OpCode::Cast(new_r, v, CastTarget::Field));
                                new_instructions.push(OpCode::BoxField(r, new_r, type_info.get_value_type(r).annotation));
                            } else {
                                new_instructions.push(OpCode::Cast(r, v, t));
                            };
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
                        OpCode::Cmp(kind, r, a, b) => {
                            let a_type = type_info.get_value_type(a);
                            let b_type = type_info.get_value_type(b);
                            assert!(
                                *a_type.get_annotation() == ConstantTaint::Pure,
                                "Cannot handle impure comparisons, should be removed already"
                            );
                            assert!(
                                *b_type.get_annotation() == ConstantTaint::Pure,
                                "Cannot handle impure comparisons, should be removed already"
                            );
                            match (&a_type.expr, &b_type.expr) {
                                (TypeExpr::Field, TypeExpr::Field) => {
                                    // These will get boxed, so we need to explicitly unbox them
                                    let new_a = function.fresh_value();
                                    let new_b = function.fresh_value();
                                    new_instructions.push(OpCode::UnboxField(new_a, a));
                                    new_instructions.push(OpCode::UnboxField(new_b, b));
                                    new_instructions.push(OpCode::Cmp(kind, r, new_a, new_b));
                                }
                                _ => {
                                    new_instructions.push(OpCode::Cmp(kind, r, a, b));
                                }
                            }
                        }
                        OpCode::BinaryArithOp(kind, r, a, b) => {
                            let a_type = type_info.get_value_type(a);
                            let b_type = type_info.get_value_type(b);
                            if *a_type.get_annotation() == ConstantTaint::Pure
                                && *b_type.get_annotation() == ConstantTaint::Pure
                            {
                                match (&a_type.expr, &b_type.expr) {
                                    (TypeExpr::Field, TypeExpr::Field) => {
                                        let new_a = function.fresh_value();
                                        let new_b = function.fresh_value();
                                        let new_r = function.fresh_value();
                                        new_instructions.push(OpCode::UnboxField(new_a, a));
                                        new_instructions.push(OpCode::UnboxField(new_b, b));
                                        new_instructions
                                            .push(OpCode::BinaryArithOp(kind, new_r, new_a, new_b));
                                        new_instructions.push(OpCode::BoxField(
                                            r,
                                            new_r,
                                            ConstantTaint::Witness,
                                        ));
                                    }
                                    _ => {
                                        new_instructions.push(OpCode::BinaryArithOp(kind, r, a, b));
                                    }
                                }
                            } else {
                                match kind {
                                    BinaryArithOpKind::Add | BinaryArithOpKind::Sub => {
                                        assert!(
                                            matches!(a_type.expr, TypeExpr::Field)
                                                && matches!(b_type.expr, TypeExpr::Field),
                                            "Cannot handle impure binary arithmetic operations on non-field types, should be removed already"
                                        );
                                        new_instructions.push(OpCode::BinaryArithOp(kind, r, a, b));
                                    }
                                    BinaryArithOpKind::Mul => {
                                        match (
                                            (a_type.get_annotation(), a),
                                            (b_type.get_annotation(), b),
                                        ) {
                                            (
                                                (ConstantTaint::Pure, pure_v),
                                                (ConstantTaint::Witness, witness_v),
                                            )
                                            | (
                                                (ConstantTaint::Witness, witness_v),
                                                (ConstantTaint::Pure, pure_v),
                                            ) => {
                                                let new_pure_v = function.fresh_value();
                                                new_instructions.push(OpCode::UnboxField(new_pure_v, pure_v));
                                                new_instructions.push(OpCode::MulConst(r, new_pure_v, witness_v));
                                            }
                                            _ => {
                                                panic!("Cannot multiply two witness values, should be removed already");
                                            }
                                        }
                                    }
                                    BinaryArithOpKind::Div | BinaryArithOpKind::And => {
                                        panic!("Cannot handle this operation with witness values, should be removed already {:?}", kind);
                                    }
                                }
                            }
                        }
                        OpCode::Truncate(r, v, f, t) => {
                            let v_type = type_info.get_value_type(v);
                            if matches!(v_type.expr, TypeExpr::Field) {
                                assert!(*v_type.get_annotation() == ConstantTaint::Pure, "Cannot truncate witness values, should be removed already");
                                let new_r = function.fresh_value();
                                let new_v = function.fresh_value();
                                new_instructions.push(OpCode::UnboxField(new_v, v));
                                new_instructions.push(OpCode::Truncate(new_r, new_v, f, t));
                                new_instructions.push(OpCode::BoxField(r, new_r, v_type.annotation.clone()));
                            } else {
                                new_instructions.push(OpCode::Truncate(r, v, f, t));
                            }
                        }
                        OpCode::AssertEq(a, b) => {
                            let a_type = type_info.get_value_type(a);
                            let b_type = type_info.get_value_type(b);
                            if matches!(a_type.expr, TypeExpr::Field) && matches!(b_type.expr, TypeExpr::Field) {
                                assert!(*a_type.get_annotation() == ConstantTaint::Pure, "Cannot handle impure assertions, should be removed already");
                                assert!(*b_type.get_annotation() == ConstantTaint::Pure, "Cannot handle impure assertions, should be removed already");
                                let new_a = function.fresh_value();
                                let new_b = function.fresh_value();
                                new_instructions.push(OpCode::UnboxField(new_a, a));
                                new_instructions.push(OpCode::UnboxField(new_b, b));
                                new_instructions.push(OpCode::AssertEq(new_a, new_b));
                            } else {
                                new_instructions.push(OpCode::AssertEq(a, b));
                            }
                        }
                        | OpCode::Not { .. }
                        | OpCode::Store { .. }
                        | OpCode::Load { .. }
                        | OpCode::AssertR1C { .. }
                        | OpCode::Call { .. }
                        | OpCode::ArrayGet { .. }
                        | OpCode::ArraySet { .. }
                        | OpCode::Select { .. }
                        | OpCode::ToBits { .. }
                        | OpCode::MemOp { .. }
                        | OpCode::WriteWitness { .. }
                        | OpCode::NextDCoeff { .. }
                        | OpCode::BoxField { .. }
                        | OpCode::UnboxField { .. }
                        | OpCode::MulConst { .. }
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
