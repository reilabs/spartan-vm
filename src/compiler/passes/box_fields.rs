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
            needs: vec![DataPoint::Types],
        }
    }

    fn invalidates_cfg(&self) -> bool {
        false
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
                        OpCode::Cast { result: r, value: v, target: t } => {
                            let v_type = type_info.get_value_type(v);
                            let v = if v_type.is_field() {
                                let new_v = function.fresh_value();
                                new_instructions.push(OpCode::UnboxField {
                                    result: new_v,
                                    value: v
                                });
                                new_v
                            } else {
                                v
                            };
                            
                            if matches!(t, CastTarget::Field) {
                                let new_r = function.fresh_value();
                                new_instructions.push(OpCode::Cast {
                                    result: new_r,
                                    value: v,
                                    target: CastTarget::Field
                                });
                                new_instructions.push(OpCode::BoxField {
                                    result: r,
                                    value: new_r,
                                    result_annotation: type_info.get_value_type(r).annotation
                                });
                            } else {
                                new_instructions.push(OpCode::Cast {
                                    result: r,
                                    value: v,
                                    target: t
                                });
                            };
                        }
                        OpCode::FreshWitness { result: r, result_type: tp } => {
                            let i = OpCode::FreshWitness {
                                result: r,
                                result_type: self.box_fields_in_type(&tp)
                            };
                            new_instructions.push(i);
                        }
                        OpCode::MkSeq { result: r, elems: vs, seq_type: s, elem_type: tp } => {
                            let i = OpCode::MkSeq {
                                result: r,
                                elems: vs.clone(),
                                seq_type: s,
                                elem_type: self.box_fields_in_type(&tp)
                            };
                            new_instructions.push(i);
                        }
                        OpCode::Alloc { result: r, elem_type: tp, result_annotation: v } => {
                            let i = OpCode::Alloc {
                                result: r,
                                elem_type: self.box_fields_in_type(&tp),
                                result_annotation: v
                            };
                            new_instructions.push(i);
                        }
                        OpCode::Constrain { a, b, c } => {
                            let new_val = function.fresh_value();
                            new_instructions.push(OpCode::NextDCoeff { result: new_val });
                            new_instructions.push(OpCode::BumpD {
                                matrix: DMatrix::A,
                                variable: a,
                                sensitivity: new_val
                            });
                            new_instructions.push(OpCode::BumpD {
                                matrix: DMatrix::B,
                                variable: b,
                                sensitivity: new_val
                            });
                            new_instructions.push(OpCode::BumpD {
                                matrix: DMatrix::C,
                                variable: c,
                                sensitivity: new_val
                            });
                        }
                        OpCode::Cmp { kind, result: r, lhs: a, rhs: b } => {
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
                                    new_instructions.push(OpCode::UnboxField {
                                        result: new_a,
                                        value: a
                                    });
                                    new_instructions.push(OpCode::UnboxField {
                                        result: new_b,
                                        value: b
                                    });
                                    new_instructions.push(OpCode::Cmp {
                                        kind: kind,
                                        result: r,
                                        lhs: new_a,
                                        rhs: new_b
                                    });
                                }
                                _ => {
                                    new_instructions.push(OpCode::Cmp {
                                        kind: kind,
                                        result: r,
                                        lhs: a,
                                        rhs: b
                                    });
                                }
                            }
                        }
                        OpCode::BinaryArithOp { kind, result: r, lhs: a, rhs: b } => {
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
                                        new_instructions.push(OpCode::UnboxField {
                                            result: new_a,
                                            value: a
                                        });
                                        new_instructions.push(OpCode::UnboxField {
                                            result: new_b,
                                            value: b
                                        });
                                        new_instructions
                                            .push(OpCode::BinaryArithOp {
                                                kind: kind,
                                                result: new_r,
                                                lhs: new_a,
                                                rhs: new_b
                                            });
                                        new_instructions.push(OpCode::BoxField {
                                            result: r,
                                            value: new_r,
                                            result_annotation: ConstantTaint::Witness
                                        });
                                    }
                                    _ => {
                                        new_instructions.push(OpCode::BinaryArithOp {
                                            kind: kind,
                                            result: r,
                                            lhs: a,
                                            rhs: b
                                        });
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
                                        new_instructions.push(OpCode::BinaryArithOp {
                                            kind: kind,
                                            result: r,
                                            lhs: a,
                                            rhs: b
                                        });
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
                                                new_instructions.push(OpCode::UnboxField {
                                                    result: new_pure_v,
                                                    value: pure_v
                                                });
                                                new_instructions.push(OpCode::MulConst {
                                                    result: r,
                                                    const_val: new_pure_v,
                                                    var: witness_v
                                                });
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
                        OpCode::Truncate { result: r, value: v, to_bits: f, from_bits: t } => {
                            let v_type = type_info.get_value_type(v);
                            if matches!(v_type.expr, TypeExpr::Field) {
                                assert!(*v_type.get_annotation() == ConstantTaint::Pure, "Cannot truncate witness values, should be removed already");
                                let new_r = function.fresh_value();
                                let new_v = function.fresh_value();
                                new_instructions.push(OpCode::UnboxField {
                                    result: new_v,
                                    value: v
                                });
                                new_instructions.push(OpCode::Truncate {
                                    result: new_r,
                                    value: new_v,
                                    to_bits: f,
                                    from_bits: t
                                });
                                new_instructions.push(OpCode::BoxField {
                                    result: r,
                                    value: new_r,
                                    result_annotation: v_type.annotation.clone()
                                });
                            } else {
                                new_instructions.push(OpCode::Truncate {
                                    result: r,
                                    value: v,
                                    to_bits: f,
                                    from_bits: t
                                });
                            }
                        }
                        OpCode::AssertEq { lhs: a, rhs: b } => {
                            let a_type = type_info.get_value_type(a);
                            let b_type = type_info.get_value_type(b);
                            if matches!(a_type.expr, TypeExpr::Field) && matches!(b_type.expr, TypeExpr::Field) {
                                assert!(*a_type.get_annotation() == ConstantTaint::Pure, "Cannot handle impure assertions, should be removed already");
                                assert!(*b_type.get_annotation() == ConstantTaint::Pure, "Cannot handle impure assertions, should be removed already");
                                let new_a = function.fresh_value();
                                let new_b = function.fresh_value();
                                new_instructions.push(OpCode::UnboxField {
                                    result: new_a,
                                    value: a
                                });
                                new_instructions.push(OpCode::UnboxField {
                                    result: new_b,
                                    value: b
                                });
                                new_instructions.push(OpCode::AssertEq {
                                    lhs: new_a,
                                    rhs: new_b
                                });
                            } else {
                                new_instructions.push(OpCode::AssertEq {
                                    lhs: a,
                                    rhs: b
                                });
                            }
                        }
                        OpCode::Rangecheck { value: val, max_bits } => {
                            let unboxed_val = function.fresh_value();
                            new_instructions.push(OpCode::UnboxField {
                                result: unboxed_val,
                                value: val
                            });
                            new_instructions.push(OpCode::Rangecheck {
                                value: unboxed_val,
                                max_bits: max_bits
                            });
                        }
                        OpCode::ReadGlobal { result: r, offset: index, result_type: tp } => {
                            new_instructions.push(OpCode::ReadGlobal {
                                result: r,
                                offset: index,
                                result_type: self.box_fields_in_type(&tp)
                            });
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
                        | OpCode::ToRadix { .. }
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
