use std::collections::HashMap;

use crate::compiler::{
    analysis::types::TypeInfo,
    pass_manager::{DataPoint, Pass},
    ssa::{BinaryArithOpKind, Block, BlockId, OpCode, SSA},
    taint_analysis::ConstantTaint,
};

pub struct ExplicitWitness {}

impl Pass<ConstantTaint> for ExplicitWitness {
    fn run(
        &self,
        ssa: &mut SSA<ConstantTaint>,
        pass_manager: &crate::compiler::pass_manager::PassManager<ConstantTaint>,
    ) {
        self.do_run(ssa, pass_manager.get_type_info());
    }

    fn pass_info(&self) -> crate::compiler::pass_manager::PassInfo {
        crate::compiler::pass_manager::PassInfo {
            name: "explicit_witness",
            invalidates: vec![DataPoint::Types],
            needs: vec![DataPoint::Types],
        }
    }
}

impl ExplicitWitness {
    pub fn new() -> Self {
        Self {}
    }

    pub fn do_run(&self, ssa: &mut SSA<ConstantTaint>, type_info: &TypeInfo<ConstantTaint>) {
        for (function_id, function) in ssa.iter_functions_mut() {
            let function_type_info = type_info.get_function(*function_id);
            let mut new_blocks = HashMap::<BlockId, Block<ConstantTaint>>::new();
            for (bid, mut block) in function.take_blocks().into_iter() {
                let mut new_instructions = Vec::new();
                for instruction in block.take_instructions().into_iter() {
                    match instruction {
                        OpCode::BinaryArithOp(BinaryArithOpKind::Add, ..) => {
                            new_instructions.push(instruction);
                        }
                        OpCode::BinaryArithOp(BinaryArithOpKind::Sub, ..) => {
                            new_instructions.push(instruction);
                        }
                        OpCode::Alloc { .. }
                        | OpCode::Call { .. }
                        | OpCode::Constrain { .. }
                        | OpCode::WriteWitness { .. }
                        | OpCode::FreshWitness(_, _) => {
                            new_instructions.push(instruction);
                        }
                        OpCode::Cmp(_, r, l, _) => {
                            let l_taint = function_type_info.get_value_type(l).get_annotation();
                            let r_taint = function_type_info.get_value_type(r).get_annotation();
                            // TODO: witness versions
                            assert!(l_taint.is_pure());
                            assert!(r_taint.is_pure());
                            new_instructions.push(instruction);
                        }
                        OpCode::BinaryArithOp(BinaryArithOpKind::Mul, res, l, r) => {
                            let l_taint = function_type_info.get_value_type(l).get_annotation();
                            let r_taint = function_type_info.get_value_type(r).get_annotation();

                            if l_taint.is_pure() || r_taint.is_pure() {
                                new_instructions.push(instruction);
                                continue;
                            }

                            // witness-witness mul
                            let mul_witness = function.fresh_value();
                            new_instructions.push(OpCode::BinaryArithOp(
                                BinaryArithOpKind::Mul,
                                mul_witness,
                                l,
                                r,
                            ));
                            new_instructions.push(OpCode::WriteWitness(
                                Some(res),
                                mul_witness,
                                ConstantTaint::Witness,
                            ));
                            new_instructions.push(OpCode::Constrain(l, r, res));
                        }
                        OpCode::BinaryArithOp(BinaryArithOpKind::Div, _, l, r) => {
                            let l_taint = function_type_info.get_value_type(l).get_annotation();
                            let r_taint = function_type_info.get_value_type(r).get_annotation();
                            assert!(l_taint.is_pure());
                            assert!(r_taint.is_pure());
                            new_instructions.push(instruction);
                        }
                        OpCode::BinaryArithOp(BinaryArithOpKind::And, _, l, r) => {
                            let l_taint = function_type_info.get_value_type(l).get_annotation();
                            let r_taint = function_type_info.get_value_type(r).get_annotation();
                            assert!(l_taint.is_pure());
                            assert!(r_taint.is_pure());
                            new_instructions.push(instruction);
                        }
                        OpCode::Store(ptr, _) => {
                            let ptr_taint = function_type_info.get_value_type(ptr).get_annotation();
                            assert!(ptr_taint.is_pure());
                            new_instructions.push(instruction);
                        }
                        OpCode::Load(_, ptr) => {
                            let ptr_taint = function_type_info.get_value_type(ptr).get_annotation();
                            assert!(ptr_taint.is_pure());
                            new_instructions.push(instruction);
                        }
                        OpCode::AssertEq(l, r) => {
                            let l_taint = function_type_info.get_value_type(l).get_annotation();
                            let r_taint = function_type_info.get_value_type(r).get_annotation();
                            if l_taint.is_pure() && r_taint.is_pure() {
                                new_instructions.push(instruction);
                                continue;
                            }
                            let one = function.push_field_const(ark_ff::Fp::from(1));
                            new_instructions.push(OpCode::Constrain(l, one, r));
                        }
                        OpCode::AssertR1C(a, b, c) => {
                            let a_taint = function_type_info.get_value_type(a).get_annotation();
                            let b_taint = function_type_info.get_value_type(b).get_annotation();
                            let c_taint = function_type_info.get_value_type(c).get_annotation();
                            if a_taint.is_pure() && b_taint.is_pure() && c_taint.is_pure() {
                                new_instructions.push(instruction);
                                continue;
                            }
                            new_instructions.push(OpCode::Constrain(a, b, c));
                        }
                        OpCode::ArrayGet(_, arr, idx) => {
                            let arr_taint = function_type_info.get_value_type(arr).get_annotation();
                            let idx_taint = function_type_info.get_value_type(idx).get_annotation();
                            assert!(arr_taint.is_pure());
                            assert!(idx_taint.is_pure());
                            new_instructions.push(instruction);
                        }
                        OpCode::ArraySet(_, arr, idx, _) => {
                            let arr_taint = function_type_info.get_value_type(arr).get_annotation();
                            let idx_taint = function_type_info.get_value_type(idx).get_annotation();
                            assert!(arr_taint.is_pure());
                            assert!(idx_taint.is_pure());
                            new_instructions.push(instruction);
                        }
                        OpCode::Select(res, cond, l, r) => {
                            let cond_taint =
                                function_type_info.get_value_type(cond).get_annotation();
                            let l_taint = function_type_info.get_value_type(l).get_annotation();
                            let r_taint = function_type_info.get_value_type(r).get_annotation();
                            // The result is cond * l + (1 - cond) * r
                            // If either cond or both l and r and pure, this becomes a linear combination
                            // and as such doesn't need a witness
                            if cond_taint.is_pure() || (l_taint.is_pure() && r_taint.is_pure()) {
                                new_instructions.push(instruction);
                                continue;
                            }
                            let select_witness = function.fresh_value();
                            new_instructions.push(OpCode::Select(select_witness, cond, l, r));
                            new_instructions.push(OpCode::WriteWitness(
                                Some(res),
                                select_witness,
                                ConstantTaint::Witness,
                            ));
                            // Goal is to assert 0 = cond * l + (1 - cond) * r - res
                            // This is equivalent to 0 = cond * (l - r) + r - res = cond * (l - r) - (res - r)
                            let neg_one = function.push_field_const(ark_ff::Fp::from(-1));
                            let neg_r = function.fresh_value();
                            new_instructions.push(OpCode::BinaryArithOp(
                                BinaryArithOpKind::Mul,
                                neg_r,
                                r,
                                neg_one,
                            ));
                            let l_sub_r = function.fresh_value();
                            new_instructions.push(OpCode::BinaryArithOp(
                                BinaryArithOpKind::Add,
                                l_sub_r,
                                l,
                                neg_r,
                            ));
                            let res_sub_r = function.fresh_value();
                            new_instructions.push(OpCode::BinaryArithOp(
                                BinaryArithOpKind::Add,
                                res_sub_r,
                                res,
                                neg_r,
                            ));
                            new_instructions.push(OpCode::Constrain(cond, l_sub_r, res_sub_r));
                        }

                        OpCode::MkSeq(_, _, _, _) => {
                            new_instructions.push(instruction);
                        }
                        OpCode::Cast(_, _, _) => {
                            new_instructions.push(instruction);
                        }
                        OpCode::Truncate(_, i, _, _) => {
                            let i_taint = function_type_info.get_value_type(i).get_annotation();
                            assert!(i_taint.is_pure()); // TODO: witness versions
                            new_instructions.push(instruction);
                        }
                        OpCode::Not(_, i) => {
                            let i_taint = function_type_info.get_value_type(i).get_annotation();
                            assert!(i_taint.is_pure()); // TODO: witness versions
                            new_instructions.push(instruction);
                        }
                        OpCode::ToBits(_, i, _, _) => {
                            let i_taint = function_type_info.get_value_type(i).get_annotation();
                            assert!(i_taint.is_pure()); // Only handle pure input case for now
                            new_instructions.push(instruction);
                        }
                        OpCode::MemOp(_, _) => {
                            new_instructions.push(instruction);
                        }
                    }
                }
                block.put_instructions(new_instructions);
                new_blocks.insert(bid, block);
            }
            function.put_blocks(new_blocks);
        }
    }
}
