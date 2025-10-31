use std::collections::HashMap;

use ark_ff::AdditiveGroup;

use crate::compiler::{
    analysis::types::TypeInfo,
    pass_manager::{DataPoint, Pass},
    ssa::{BinaryArithOpKind, Block, BlockId, CastTarget, Endianness, LookupTarget, OpCode, Radix, SSA},
    taint_analysis::ConstantTaint, Field,
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
            needs: vec![DataPoint::Types],
        }
    }

    fn invalidates_cfg(&self) -> bool {
        false
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
                        OpCode::BinaryArithOp { kind: BinaryArithOpKind::Add, .. } => {
                            new_instructions.push(instruction);
                        }
                        OpCode::BinaryArithOp { kind: BinaryArithOpKind::Sub, .. } => {
                            new_instructions.push(instruction);
                        }
                        OpCode::Alloc { .. }
                        | OpCode::Call { .. }
                        | OpCode::Constrain { .. }
                        | OpCode::WriteWitness { .. }
                        | OpCode::FreshWitness { result: _, result_type: _ } => {
                            new_instructions.push(instruction);
                        }
                        OpCode::Cmp { kind: _, result: r, lhs: l, rhs: _ } => {
                            let l_taint = function_type_info.get_value_type(l).get_annotation();
                            let r_taint = function_type_info.get_value_type(r).get_annotation();
                            // TODO: witness versions
                            assert!(l_taint.is_pure());
                            assert!(r_taint.is_pure());
                            new_instructions.push(instruction);
                        }
                        OpCode::BinaryArithOp { kind: BinaryArithOpKind::Mul, result: res, lhs: l, rhs: r } => {
                            let l_taint = function_type_info.get_value_type(l).get_annotation();
                            let r_taint = function_type_info.get_value_type(r).get_annotation();

                            if l_taint.is_pure() || r_taint.is_pure() {
                                new_instructions.push(instruction);
                                continue;
                            }

                            // witness-witness mul
                            let mul_witness = function.fresh_value();
                            new_instructions.push(OpCode::BinaryArithOp {
                                kind: BinaryArithOpKind::Mul,
                                result: mul_witness,
                                lhs: l,
                                rhs: r
                            });
                            new_instructions.push(OpCode::WriteWitness {
                                result: Some(res),
                                value: mul_witness,
                                witness_annotation: ConstantTaint::Witness
                            });
                            new_instructions.push(OpCode::Constrain {
                                a: l,
                                b: r,
                                c: res
                            });
                        }
                        OpCode::BinaryArithOp { kind: BinaryArithOpKind::Div, result: _, lhs: l, rhs: r } => {
                            let l_taint = function_type_info.get_value_type(l).get_annotation();
                            let r_taint = function_type_info.get_value_type(r).get_annotation();
                            assert!(l_taint.is_pure());
                            assert!(r_taint.is_pure());
                            new_instructions.push(instruction);
                        }
                        OpCode::BinaryArithOp { kind: BinaryArithOpKind::And, result: _, lhs: l, rhs: r } => {
                            let l_taint = function_type_info.get_value_type(l).get_annotation();
                            let r_taint = function_type_info.get_value_type(r).get_annotation();
                            assert!(l_taint.is_pure());
                            assert!(r_taint.is_pure());
                            new_instructions.push(instruction);
                        }
                        OpCode::Store { ptr, value: _ } => {
                            let ptr_taint = function_type_info.get_value_type(ptr).get_annotation();
                            assert!(ptr_taint.is_pure());
                            new_instructions.push(instruction);
                        }
                        OpCode::Load { result: _, ptr } => {
                            let ptr_taint = function_type_info.get_value_type(ptr).get_annotation();
                            assert!(ptr_taint.is_pure());
                            new_instructions.push(instruction);
                        }
                        OpCode::AssertEq { lhs: l, rhs: r } => {
                            let l_taint = function_type_info.get_value_type(l).get_annotation();
                            let r_taint = function_type_info.get_value_type(r).get_annotation();
                            if l_taint.is_pure() && r_taint.is_pure() {
                                new_instructions.push(instruction);
                                continue;
                            }
                            let one = function.push_field_const(ark_ff::Fp::from(1));
                            new_instructions.push(OpCode::Constrain {
                                a: l,
                                b: one,
                                c: r
                            });
                        }
                        OpCode::AssertR1C { a, b, c } => {
                            let a_taint = function_type_info.get_value_type(a).get_annotation();
                            let b_taint = function_type_info.get_value_type(b).get_annotation();
                            let c_taint = function_type_info.get_value_type(c).get_annotation();
                            if a_taint.is_pure() && b_taint.is_pure() && c_taint.is_pure() {
                                new_instructions.push(instruction);
                                continue;
                            }
                            new_instructions.push(OpCode::Constrain {
                                a: a,
                                b: b,
                                c: c
                            });
                        }
                        OpCode::NextDCoeff { result: _ } => {
                            panic!("ICE: should not be present at this stage");
                        }
                        OpCode::BumpD { matrix: _, variable: _, sensitivity: _ } => {
                            panic!("ICE: should not be present at this stage");
                        }
                        OpCode::ArrayGet { result: _, array: arr, index: idx } => {
                            let arr_taint = function_type_info.get_value_type(arr).get_annotation();
                            let idx_taint = function_type_info.get_value_type(idx).get_annotation();
                            assert!(arr_taint.is_pure());
                            assert!(idx_taint.is_pure());
                            new_instructions.push(instruction);
                        }
                        OpCode::ArraySet { result: _, array: arr, index: idx, value: _ } => {
                            let arr_taint = function_type_info.get_value_type(arr).get_annotation();
                            let idx_taint = function_type_info.get_value_type(idx).get_annotation();
                            assert!(arr_taint.is_pure());
                            assert!(idx_taint.is_pure());
                            new_instructions.push(instruction);
                        }
                        OpCode::Select { result: res, cond, if_t: l, if_f: r } => {
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
                            new_instructions.push(OpCode::Select {
                                result: select_witness,
                                cond: cond,
                                if_t: l,
                                if_f: r
                            });
                            new_instructions.push(OpCode::WriteWitness {
                                result: Some(res),
                                value: select_witness,
                                witness_annotation: ConstantTaint::Witness
                            });
                            // Goal is to assert 0 = cond * l + (1 - cond) * r - res
                            // This is equivalent to 0 = cond * (l - r) + r - res = cond * (l - r) - (res - r)
                            let neg_one = function.push_field_const(ark_ff::Fp::from(-1));
                            let neg_r = function.fresh_value();
                            new_instructions.push(OpCode::BinaryArithOp {
                                kind: BinaryArithOpKind::Mul,
                                result: neg_r,
                                lhs: r,
                                rhs: neg_one
                            });
                            let l_sub_r = function.fresh_value();
                            new_instructions.push(OpCode::BinaryArithOp {
                                kind: BinaryArithOpKind::Add,
                                result: l_sub_r,
                                lhs: l,
                                rhs: neg_r
                            });
                            let res_sub_r = function.fresh_value();
                            new_instructions.push(OpCode::BinaryArithOp {
                                kind: BinaryArithOpKind::Add,
                                result: res_sub_r,
                                lhs: res,
                                rhs: neg_r
                            });
                            new_instructions.push(OpCode::Constrain {
                                a: cond,
                                b: l_sub_r,
                                c: res_sub_r
                            });
                        }

                        OpCode::MkSeq { result: _, elems: _, seq_type: _, elem_type: _ } => {
                            new_instructions.push(instruction);
                        }
                        OpCode::Cast { result: _, value: _, target: _ } => {
                            new_instructions.push(instruction);
                        }
                        OpCode::Truncate { result: _, value: i, to_bits: _, from_bits: _ } => {
                            let i_taint = function_type_info.get_value_type(i).get_annotation();
                            assert!(i_taint.is_pure()); // TODO: witness versions
                            new_instructions.push(instruction);
                        }
                        OpCode::Not { result: _, value: i } => {
                            let i_taint = function_type_info.get_value_type(i).get_annotation();
                            assert!(i_taint.is_pure()); // TODO: witness versions
                            new_instructions.push(instruction);
                        }
                        OpCode::ToBits { result: _, value: i, endianness: _, count: _ } => {
                            let i_taint = function_type_info.get_value_type(i).get_annotation();
                            assert!(i_taint.is_pure()); // Only handle pure input case for now
                            new_instructions.push(instruction);
                        }
                        OpCode::ToRadix { result: _, value: i, radix: _, endianness: _, count: _ } => {
                            let i_taint = function_type_info.get_value_type(i).get_annotation();
                            assert!(i_taint.is_pure()); // Only handle pure input case for now
                            new_instructions.push(instruction);
                        }
                        OpCode::MemOp { kind: _, value: _ } => {
                            new_instructions.push(instruction);
                        }
                        OpCode::BoxField { result: _, value: _, result_annotation: _ } => {
                            new_instructions.push(instruction);
                        }
                        OpCode::UnboxField { result: _, value: _ } => {
                            new_instructions.push(instruction);
                        }
                        OpCode::MulConst { result: _, const_val: _, var: _ } => {
                            new_instructions.push(instruction);
                        }
                        OpCode::Rangecheck { value, max_bits } => {
                            let v_taint = function_type_info.get_value_type(value).get_annotation();
                            if v_taint.is_pure() {
                                new_instructions.push(instruction);
                            } else {
                                assert!(max_bits % 8 == 0); // TODO
                                let bytes_val = function.fresh_value();
                                new_instructions.push(OpCode::ToRadix { result: bytes_val, value: value, radix: Radix::Bytes, endianness: Endianness::Big, count: max_bits / 8 });
                                let chunks = max_bits / 8;
                                let mut result = function.push_field_const(Field::ZERO);
                                let two_to_8 = function.push_field_const(Field::from(256));
                                let one = function.push_field_const(Field::from(1));
                                for i in 0..chunks {
                                    let byte = function.fresh_value();
                                    new_instructions.push(OpCode::ArrayGet { result: byte, array: bytes_val, index: function.push_u_const(32, i as u128) });
                                    let byte_field = function.fresh_value();
                                    new_instructions.push(OpCode::Cast { result: byte_field, value: byte, target: CastTarget::Field });
                                    let byte_wit = function.fresh_value();
                                    new_instructions.push(OpCode::WriteWitness { result: Some(byte_wit), value: byte_field, witness_annotation: ConstantTaint::Witness });
                                    new_instructions.push(OpCode::Lookup { target: LookupTarget::Rangecheck(8), keys: vec![byte_wit], results: vec![] });
                                    let shift_prev_res = function.fresh_value();
                                    new_instructions.push(OpCode::BinaryArithOp { kind: BinaryArithOpKind::Mul, result: shift_prev_res, lhs: result, rhs: two_to_8 });
                                    let new_result = function.fresh_value();
                                    new_instructions.push(OpCode::BinaryArithOp { kind: BinaryArithOpKind::Add, result: new_result, lhs: shift_prev_res, rhs: byte_wit });
                                    result = new_result;
                                }
                                new_instructions.push(OpCode::Constrain { a: result, b: one, c: value });
                            }
                            // new_instructions.push(instruction);
                        }
                        OpCode::ReadGlobal { result: _, offset: _, result_type: _ } => {
                            new_instructions.push(instruction);
                        }
                        OpCode::Lookup { .. } => {
                            new_instructions.push(instruction);
                        }
                        OpCode::DLookup { .. } => {
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
