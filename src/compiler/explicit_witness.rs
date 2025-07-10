use std::collections::HashMap;

use crate::compiler::{
    flow_analysis::FlowAnalysis,
    ssa::{BlockId, Function, FunctionId, OpCode, SSA, Type, ValueId},
    taint_analysis::{ConstantTaint, FunctionTaint, Taint, TaintAnalysis},
};

use ark_bn254::Fr;
use ark_ff::Field;

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
        let cfg_taint_param = if matches!(
            function_taint.cfg_taint,
            Taint::Constant(ConstantTaint::Witness)
        ) {
            Some(function.add_parameter(function.get_entry_id(), Type::Bool))
        } else {
            None
        };

        for block_id in flow_analysis.get_blocks_bfs(function_id) {
            let mut block = function.take_block(block_id);
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

                    _ => {
                        panic!("Unhandled instruction {:?}", instruction);
                    }
                }
            }

            block.put_instructions(new_instructions);
            // TODO: Control flow!
            function.put_block(block_id, block);
        }
    }
}
