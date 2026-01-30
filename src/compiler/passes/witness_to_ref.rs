use std::collections::HashMap;

use noirc_evaluator::ssa::ir::dfg;

use crate::compiler::{
    ir::r#type::{Type, TypeExpr},
    pass_manager::{DataPoint, Pass},
    ssa::{BinaryArithOpKind, CastTarget, Const, DMatrix, OpCode},
    taint_analysis::ConstantTaint,
};

pub struct WitnessToRef {}

impl Pass<ConstantTaint> for WitnessToRef {
    fn run(
        &self,
        ssa: &mut crate::compiler::ssa::SSA<ConstantTaint>,
        pass_manager: &crate::compiler::pass_manager::PassManager<ConstantTaint>,
    ) {
        self.do_run(ssa, pass_manager.get_type_info());
    }

    fn pass_info(&self) -> crate::compiler::pass_manager::PassInfo {
        crate::compiler::pass_manager::PassInfo {
            name: "witness_to_ref",
            needs: vec![DataPoint::Types],
        }
    }

    fn invalidates_cfg(&self) -> bool {
        false
    }
}

impl WitnessToRef {
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
                *rtp = self.witness_to_ref_in_type(rtp);
            }
            let mut new_blocks = HashMap::new();
            for (bid, mut block) in function.take_blocks().into_iter() {
                let old_params = block.take_parameters();
                let new_params = old_params
                    .into_iter()
                    .map(|(r, tp)| (r, self.witness_to_ref_in_type(&tp)))
                    .collect();
                block.put_parameters(new_params);
                let mut new_instructions = vec![];
                for instruction in block.take_instructions().into_iter() {
                    match instruction {
                        OpCode::Cast {
                            result: r,
                            value: v,
                            target: t,
                        } => {
                            let v_type = type_info.get_value_type(v);
                            // Otherwise becomes witness ref -> witness ref cast, so we can skip it
                            if v_type.get_annotation().is_witness() {
                                new_instructions.push(OpCode::Cast {
                                    result: r,
                                    value: v,
                                    target: CastTarget::Nop,
                                });
                            } else {
                                new_instructions.push(instruction);
                            }
                        }
                        OpCode::FreshWitness {
                            result: r,
                            result_type: tp,
                        } => {
                            let i = OpCode::FreshWitness {
                                result: r,
                                result_type: Type::witness_ref(tp.annotation.clone()),
                            };
                            new_instructions.push(i);
                        }
                        OpCode::MkSeq {
                            result: r,
                            elems: vs,
                            seq_type: s,
                            elem_type: tp,
                        } => {
                            let new_elem_type = self.witness_to_ref_in_type(&tp);
                            let mut new_vs = vec![];
                            for v in vs.iter() {
                                let v_type = type_info.get_value_type(*v);
                                let new_v_type = self.witness_to_ref_in_type(&v_type);
                                if new_v_type == new_elem_type {
                                    new_vs.push(*v);
                                } else {
                                    todo!(
                                        "Value casting in witness_to_ref MkSeq {:?} -> {:?}",
                                        new_v_type,
                                        new_elem_type
                                    );
                                }
                            }
                            let i = OpCode::MkSeq {
                                result: r,
                                elems: new_vs,
                                seq_type: s,
                                elem_type: new_elem_type,
                            };
                            new_instructions.push(i);
                        }
                        OpCode::Alloc {
                            result: r,
                            elem_type: tp,
                            result_annotation: v,
                        } => {
                            let i = OpCode::Alloc {
                                result: r,
                                elem_type: self.witness_to_ref_in_type(&tp),
                                result_annotation: v,
                            };
                            new_instructions.push(i);
                        }
                        OpCode::Constrain { a, b, c } => {
                            let new_val = function.fresh_value();
                            new_instructions.push(OpCode::NextDCoeff { result: new_val });
                            new_instructions.push(OpCode::BumpD {
                                matrix: DMatrix::A,
                                variable: a,
                                sensitivity: new_val,
                            });
                            new_instructions.push(OpCode::BumpD {
                                matrix: DMatrix::B,
                                variable: b,
                                sensitivity: new_val,
                            });
                            new_instructions.push(OpCode::BumpD {
                                matrix: DMatrix::C,
                                variable: c,
                                sensitivity: new_val,
                            });
                        }
                        OpCode::Lookup {
                            target,
                            keys,
                            results,
                        } => {
                            let mut new_keys = vec![];
                            for key in keys.iter() {
                                let key_type = type_info.get_value_type(*key);
                                assert!(key_type.is_field(), "Keys of lookup must be fields");
                                if !key_type.get_annotation().is_witness() {
                                    let refed = function.fresh_value();
                                    new_instructions.push(OpCode::PureToWitnessRef {
                                        result: refed,
                                        value: *key,
                                        result_annotation: key_type.annotation.clone(),
                                    });
                                    new_keys.push(refed);
                                } else {
                                    new_keys.push(*key);
                                }
                            }
                            let mut new_results = vec![];
                            for result in results.iter() {
                                let result_type = type_info.get_value_type(*result);
                                assert!(result_type.is_field(), "Results of lookup must be fields");
                                if !result_type.get_annotation().is_witness() {
                                    let refed = function.fresh_value();
                                    new_instructions.push(OpCode::PureToWitnessRef {
                                        result: refed,
                                        value: *result,
                                        result_annotation: result_type.annotation.clone(),
                                    });
                                    new_results.push(refed);
                                } else {
                                    new_results.push(*result);
                                }
                            }
                            new_instructions.push(OpCode::DLookup {
                                target,
                                keys: new_keys,
                                results: new_results,
                            });
                        }
                        OpCode::BinaryArithOp {
                            kind,
                            result: r,
                            lhs: a,
                            rhs: b,
                        } => {
                            let a_type = type_info.get_value_type(a);
                            let b_type = type_info.get_value_type(b);
                            match (
                                a,
                                a_type.get_annotation().is_witness(),
                                b,
                                b_type.get_annotation().is_witness(),
                            ) {
                                (_, true, _, true) | (_, false, _, false) => {
                                    new_instructions.push(instruction);
                                }
                                (wit, true, pure, false) | (pure, false, wit, true) => match kind {
                                    BinaryArithOpKind::Add => {
                                        let pure_refed = function.fresh_value();
                                        new_instructions.push(OpCode::PureToWitnessRef {
                                            result: pure_refed,
                                            value: wit,
                                            result_annotation: ConstantTaint::Witness,
                                        });
                                        new_instructions.push(OpCode::BinaryArithOp {
                                            kind: kind,
                                            result: r,
                                            lhs: pure_refed,
                                            rhs: wit,
                                        });
                                    }
                                    BinaryArithOpKind::Mul => {
                                        new_instructions.push(OpCode::MulConst {
                                            result: r,
                                            const_val: pure,
                                            var: wit,
                                        });
                                    }
                                    BinaryArithOpKind::Div => {
                                        panic!("Div is not supported for witness-pure arithmetic")
                                    }
                                    BinaryArithOpKind::Sub => {
                                        let pure_refed = function.fresh_value();
                                        new_instructions.push(OpCode::PureToWitnessRef {
                                            result: pure_refed,
                                            value: wit,
                                            result_annotation: ConstantTaint::Witness,
                                        });
                                        let a = if a == wit { wit } else { pure_refed };
                                        let b = if b == wit { wit } else { pure_refed };
                                        new_instructions.push(OpCode::BinaryArithOp {
                                            kind: kind,
                                            result: r,
                                            lhs: a,
                                            rhs: b,
                                        });
                                    }
                                    BinaryArithOpKind::And => {
                                        panic!("And is not supported for witness-pure arithmetic")
                                    }
                                },
                            }
                        }
                        OpCode::Store { ptr, value } => {
                            let ptr_type = type_info.get_value_type(ptr);
                            let value_type = type_info.get_value_type(value);
                            let new_ptr_type = self.witness_to_ref_in_type(&ptr_type);
                            let new_value_type = self.witness_to_ref_in_type(&value_type);
                            if new_ptr_type == new_value_type {
                                new_instructions.push(instruction);
                            } else {
                                todo!(
                                    "Value casting in witness_to_ref Store {:?} -> {:?}",
                                    new_value_type,
                                    new_ptr_type
                                );
                            }
                        }
                        OpCode::ArraySet {
                            result,
                            array,
                            index,
                            value,
                        } => todo!(),
                        OpCode::SlicePush {
                            dir,
                            result,
                            slice,
                            values,
                        } => todo!(),
                        OpCode::Not { .. }
                        | OpCode::Cmp { .. }
                        | OpCode::Truncate { .. }
                        | OpCode::Load { .. }
                        | OpCode::AssertEq { .. }
                        | OpCode::AssertR1C { .. }
                        | OpCode::Call { .. }
                        | OpCode::ArrayGet { .. }
                        | OpCode::SliceLen { .. }
                        | OpCode::Select { .. }
                        | OpCode::ToBits { .. }
                        | OpCode::ToRadix { .. }
                        | OpCode::MemOp { .. }
                        | OpCode::WriteWitness { .. }
                        | OpCode::NextDCoeff { .. }
                        | OpCode::BumpD { .. }
                        | OpCode::DLookup { .. }
                        | OpCode::PureToWitnessRef { .. }
                        | OpCode::UnboxField { .. }
                        | OpCode::MulConst { .. }
                        | OpCode::Rangecheck { .. }
                        | OpCode::ReadGlobal { .. }
                        | OpCode::TupleProj { .. }
                        | OpCode::MkTuple { .. }
                        | OpCode::Todo { .. } => {
                            new_instructions.push(instruction);
                        }
                    };
                }
                block.put_instructions(new_instructions);
                new_blocks.insert(bid, block);
            }
            function.put_blocks(new_blocks);
        }
    }

    fn witness_to_ref_in_type(&self, tp: &Type<ConstantTaint>) -> Type<ConstantTaint> {
        match &tp.expr {
            TypeExpr::Field | TypeExpr::U(_) => {
                if tp.annotation == ConstantTaint::Witness {
                    Type::witness_ref(tp.annotation.clone())
                } else {
                    tp.clone()
                }
            }
            TypeExpr::Array(inner, size) => Type::array_of(
                self.witness_to_ref_in_type(inner),
                *size,
                tp.annotation.clone(),
            ),
            TypeExpr::Slice(inner) => {
                Type::slice_of(self.witness_to_ref_in_type(inner), tp.annotation.clone())
            }
            TypeExpr::Ref(inner) => {
                Type::ref_of(self.witness_to_ref_in_type(inner), tp.annotation.clone())
            }
            TypeExpr::WitnessRef => tp.clone(),
            TypeExpr::Tuple(elements) => {
                let boxed_elements = elements
                    .iter()
                    .map(|elem| self.witness_to_ref_in_type(elem))
                    .collect();
                Type::tuple_of(boxed_elements, tp.annotation.clone())
            }
        }
    }
}
