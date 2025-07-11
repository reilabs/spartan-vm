use std::collections::HashMap;

use crate::compiler::{
    flow_analysis::FlowAnalysis,
    ssa::{BlockId, Function, FunctionId, OpCode, SSA, Terminator, Type, ValueId},
    taint_analysis::{ConstantTaint, FunctionTaint, Taint, TaintAnalysis},
};

use ark_bn254::Fr;
use ark_ff::Field;
use noirc_frontend::hir::type_check;

pub struct ExplicitWitness {}

impl ExplicitWitness {
    pub fn new() -> Self {
        Self {}
    }

    pub fn run(
        &mut self,
        ssa: &mut SSA,
        taint_analysis: &TaintAnalysis,
        flow_analysis: &FlowAnalysis,
    ) {
        for (function_id, function) in ssa.iter_functions_mut() {
            let function_taint = taint_analysis.get_function_taint(*function_id);
            self.run_function(*function_id, function, function_taint, flow_analysis);
        }
    }

    fn run_function(
        &mut self,
        function_id: FunctionId,
        function: &mut Function,
        function_taint: &FunctionTaint,
        flow_analysis: &FlowAnalysis,
    ) {
        let cfg = flow_analysis.get_function_cfg(function_id);

        let cfg_taint_param = if matches!(
            function_taint.cfg_taint,
            Taint::Constant(ConstantTaint::Witness)
        ) {
            Some(function.add_parameter(function.get_entry_id(), Type::Bool))
        } else {
            None
        };

        let mut block_taint_vars = HashMap::new();
        for (block_id, _) in function.get_blocks() {
            block_taint_vars.insert(*block_id, cfg_taint_param.clone());
        }

        for block_id in cfg.get_blocks_bfs() {
            let mut block = function.take_block(block_id);
            let block_taint = block_taint_vars.get(&block_id).unwrap().clone();

            let old_instructions = block.take_instructions();
            let mut new_instructions = Vec::new();

            for instruction in old_instructions {
                match instruction {
                    OpCode::Mul(result, lhs, rhs) => {
                        let lhs_type = function.get_value_type(lhs).unwrap();
                        assert_eq!(*lhs_type, Type::Field); // TODO
                        let rhs_type = function.get_value_type(rhs).unwrap();
                        assert_eq!(*rhs_type, Type::Field); // TODO

                        let lhs_taint = function_taint
                            .get_value_taint(lhs)
                            .toplevel_taint()
                            .expect_constant();
                        let rhs_taint = function_taint
                            .get_value_taint(rhs)
                            .toplevel_taint()
                            .expect_constant();

                        match (lhs_taint, rhs_taint) {
                            (ConstantTaint::Witness, ConstantTaint::Witness) => {
                                let result_val = function.fresh_value();
                                new_instructions.push(OpCode::Mul(result_val, lhs, rhs));
                                new_instructions.push(OpCode::WriteWitness(result, result_val));
                                new_instructions.push(OpCode::Constrain(lhs, rhs, result));
                            }
                            _ => {
                                new_instructions.push(instruction);
                            }
                        }
                    }
                    OpCode::Add(_, _, _) => {
                        new_instructions.push(instruction);
                    }
                    OpCode::AssertEq(lhs, rhs) => {
                        let lhs_taint = function_taint
                            .get_value_taint(lhs)
                            .toplevel_taint()
                            .expect_constant();
                        let rhs_taint = function_taint
                            .get_value_taint(rhs)
                            .toplevel_taint()
                            .expect_constant();

                        match (lhs_taint, rhs_taint) {
                            (ConstantTaint::Pure, ConstantTaint::Pure) => {
                                new_instructions.push(instruction);
                            }
                            _ => {
                                let one = function.fresh_value();
                                new_instructions.push(OpCode::FieldConst(one, ark_bn254::Fr::ONE));
                                new_instructions.push(OpCode::Constrain(lhs, one, rhs));
                            }
                        }
                    }
                    OpCode::Lt(_, lhs, rhs) => {
                        let lhs_taint = function_taint
                            .get_value_taint(lhs)
                            .toplevel_taint()
                            .expect_constant();
                        let rhs_taint = function_taint
                            .get_value_taint(rhs)
                            .toplevel_taint()
                            .expect_constant();

                        // Dynamic Lt not supported yet
                        assert_eq!(lhs_taint, ConstantTaint::Pure);
                        assert_eq!(rhs_taint, ConstantTaint::Pure);
                        new_instructions.push(instruction);
                    }
                    OpCode::Store(ptr, _) => {
                        let ptr_taint = function_taint
                            .get_value_taint(ptr)
                            .toplevel_taint()
                            .expect_constant();
                        // writes to dynamic ptr not supported
                        assert_eq!(ptr_taint, ConstantTaint::Pure);
                        assert_eq!(block_taint, None); // TODO: support conditional writes
                        new_instructions.push(instruction);
                    }
                    OpCode::Load(_, ptr) => {
                        let ptr_taint = function_taint
                            .get_value_taint(ptr)
                            .toplevel_taint()
                            .expect_constant();
                        // reads from dynamic ptr not supported
                        assert_eq!(ptr_taint, ConstantTaint::Pure);
                        new_instructions.push(instruction);
                    }
                    OpCode::ArrayGet(_, arr, idx) => {
                        let arr_taint = function_taint
                            .get_value_taint(arr)
                            .toplevel_taint()
                            .expect_constant();
                        let idx_taint = function_taint
                            .get_value_taint(idx)
                            .toplevel_taint()
                            .expect_constant();
                        // dynamic array access not supported
                        assert_eq!(arr_taint, ConstantTaint::Pure);
                        assert_eq!(idx_taint, ConstantTaint::Pure);
                        new_instructions.push(instruction);
                    }
                    OpCode::Alloc(_, _)
                    | OpCode::FieldConst(_, _)
                    | OpCode::BConst(_, _)
                    | OpCode::UConst(_, _) => {
                        new_instructions.push(instruction);
                    }

                    OpCode::Call(ret, tgt, mut args) => {
                        match block_taint {
                            Some(arg) => {
                                args.push(arg);
                            }
                            None => {}
                        }
                        new_instructions.push(OpCode::Call(ret, tgt, args));
                    }

                    _ => {
                        panic!("Unhandled instruction {:?}", instruction);
                    }
                }
            }

            match block.get_terminator().cloned() {
                Some(Terminator::JmpIf(cond, if_true, if_false)) => {
                    let cond_taint = function_taint
                        .get_value_taint(cond)
                        .toplevel_taint()
                        .expect_constant();
                    match cond_taint {
                        ConstantTaint::Pure => {}
                        ConstantTaint::Witness => {
                            block.set_terminator(Terminator::Jmp(if_true, vec![]));
                            let child_block_taint = match block_taint {
                                Some(tnt) => {
                                    let result_val = function.fresh_value();
                                    new_instructions.push(OpCode::Mul(result_val, tnt, cond));
                                    let result = function.fresh_value();
                                    new_instructions.push(OpCode::WriteWitness(result, result_val));
                                    new_instructions.push(OpCode::Constrain(tnt, cond, result));
                                    result
                                }
                                None => cond,
                            };
                            let body = cfg.get_if_body(block_id);
                            for block_id in body {
                                block_taint_vars.insert(block_id, Some(child_block_taint));
                            }

                            let merge = cfg.get_merge_point(block_id);

                            if merge == function.get_entry_id() {
                                panic!(
                                    "TODO: jump back into entry not supported yet. Is it even possible?"
                                )
                            }

                            let jumps = cfg.get_jumps_into_merge_from_branch(if_true, merge);
                            if jumps.len() != 1 {
                                panic!("TODO: handle multiple jumps into merge");
                            }
                            let out_true_block = jumps[0];

                            // We remove the parameters from the merge block – they will be un-phi-fied
                            let merge_params = function.get_block_mut(merge).take_parameters();

                            for (_, typ) in &merge_params {
                                match typ {
                                    Type::Array(_, _) => {
                                        panic!("TODO: Witness array not supported yet")
                                    }
                                    Type::Ref(_) => {
                                        panic!("TODO: Witness ref not supported yet")
                                    }
                                    _ => {}
                                }
                            }

                            let args_passed_from_lhs = match function
                                .get_block_mut(out_true_block)
                                .take_terminator()
                            {
                                Some(Terminator::Jmp(_, args)) => args,
                                _ => panic!(
                                    "Impossible – out jump must be a JMP, otherwise the join point wouldn't be a join point"
                                ),
                            };

                            // Jump straight to the false block
                            function
                                .get_block_mut(out_true_block)
                                .set_terminator(Terminator::Jmp(if_false, vec![]));

                            let jumps = cfg.get_jumps_into_merge_from_branch(if_false, merge);
                            if jumps.len() != 1 {
                                panic!("TODO: handle multiple jumps into merge");
                            }
                            let out_false_block = jumps[0];
                            let args_passed_from_rhs = match function
                                .get_block_mut(out_false_block)
                                .take_terminator()
                            {
                                Some(Terminator::Jmp(_, args)) => args,
                                _ => panic!(
                                    "Impossible – out jump must be a JMP, otherwise the join point wouldn't be a join point"
                                ),
                            };

                            let mut merger_block = function.add_block();
                            function
                                .get_block_mut(out_false_block)
                                .set_terminator(Terminator::Jmp(merger_block, vec![]));
                            function
                                .get_block_mut(merger_block)
                                .set_terminator(Terminator::Jmp(merge, vec![]));

                            if args_passed_from_lhs.len() > 0 {
                                // The naive solution is to witnesize the result and assert
                                // res = lhs * cond + rhs * (cond - 1)
                                // but this is 2 non-constant muls.
                                // Instead, we notice that:
                                // res = (lhs - rhs) * cond + rhs
                                // this way we only need to witnessize the first term and return the
                                // linear combination.

                                let const_neg_1 =
                                    function.push_field_const(merger_block, -ark_bn254::Fr::ONE);

                                for ((res, _), (lhs, rhs)) in merge_params.iter().zip(
                                    args_passed_from_lhs.iter().zip(args_passed_from_rhs.iter()),
                                ) {
                                    let neg_rhs = function.push_mul(merger_block, *rhs, const_neg_1);
                                    let lhs_rhs = function.push_add(merger_block, *lhs, neg_rhs);
                                    let mul_cond = function.push_mul(merger_block, lhs_rhs, cond);
                                    let mul_cond_wit = function.push_witness_write(merger_block, mul_cond);
                                    function.push_constrain(merger_block, lhs_rhs, cond, mul_cond_wit);
                                    function.get_block_mut(merger_block).push_instruction(OpCode::Add(*res, mul_cond_wit, *rhs));
                                }

                            }
                        }
                    }
                }
                _ => {}
            };

            block.put_instructions(new_instructions);
            // TODO: Control flow!
            function.put_block(block_id, block);
        }
    }
}
