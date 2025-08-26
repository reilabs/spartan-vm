use std::collections::HashMap;

use crate::compiler::{
    flow_analysis::FlowAnalysis,
    ir::r#type::{Empty, Type, TypeExpr},
    ssa::{BinaryArithOpKind, Block, Function, FunctionId, OpCode, SSA, Terminator},
    taint_analysis::{ConstantTaint, FunctionTaint, Taint, TaintAnalysis, TaintType},
};

pub struct UntaintControlFlow {}

impl UntaintControlFlow {
    pub fn new() -> Self {
        Self {}
    }

    pub fn run(
        &mut self,
        ssa: SSA<Empty>,
        taint_analysis: &TaintAnalysis,
        flow_analysis: &FlowAnalysis,
    ) -> SSA<ConstantTaint> {
        let (mut result_ssa, functions) = ssa.prepare_rebuild::<ConstantTaint>();

        for (function_id, function) in functions.into_iter() {
            let function_taint = taint_analysis.get_function_taint(function_id);
            let new_function =
                self.run_function(function_id, function, function_taint, flow_analysis);
            result_ssa.put_function(function_id, new_function);
        }
        result_ssa
    }

    fn run_function(
        &mut self,
        function_id: FunctionId,
        function: Function<Empty>,
        function_taint: &FunctionTaint,
        flow_analysis: &FlowAnalysis,
    ) -> Function<ConstantTaint> {
        let cfg = flow_analysis.get_function_cfg(function_id);

        let (mut function, blocks, returns) = function.prepare_rebuild::<ConstantTaint>();

        for (block_id, mut block) in blocks.into_iter() {
            let mut new_block = Block::empty();

            let mut new_parameters = Vec::new();
            for (value_id, typ) in block.take_parameters() {
                let taint = function_taint.get_value_taint(value_id);
                new_parameters.push((value_id, self.typify_taint(typ, taint)));
            }
            new_block.put_parameters(new_parameters);

            let mut new_instructions = Vec::<OpCode<ConstantTaint>>::new();
            for instruction in block.take_instructions() {
                let new = match instruction {
                    OpCode::BinaryArithOp(kind, r, l, h) => OpCode::BinaryArithOp(kind, r, l, h),
                    OpCode::Cmp(kind, r, l, h) => OpCode::Cmp(kind, r, l, h),
                    OpCode::Store(r, l) => OpCode::Store(r, l),
                    OpCode::Load(r, l) => OpCode::Load(r, l),
                    OpCode::ArrayGet(r, l, h) => OpCode::ArrayGet(r, l, h),
                    OpCode::ArraySet(r, l, h, j) => OpCode::ArraySet(r, l, h, j),
                    OpCode::Alloc(r, l, _) => {
                        let r_taint = function_taint.get_value_taint(r);
                        let child = r_taint.child_taint_type().unwrap();
                        let child_typ = self.typify_taint(l, &child);
                        let self_taint = r_taint.toplevel_taint().expect_constant();
                        OpCode::Alloc(r, child_typ, self_taint)
                    }
                    OpCode::Call(r, l, h) => OpCode::Call(r, l, h),
                    OpCode::AssertEq(r, l) => OpCode::AssertEq(r, l),
                    OpCode::AssertR1C(r, l, h) => OpCode::AssertR1C(r, l, h),
                    OpCode::Select(r, l, h, j) => OpCode::Select(r, l, h, j),
                    OpCode::WriteWitness(r, l, _) => {
                        OpCode::WriteWitness(r, l, ConstantTaint::Witness)
                    }
                    OpCode::FreshWitness(r, tp) => {
                        let taint = function_taint.get_value_taint(r);
                        let new_tp = self.typify_taint(tp, taint);
                        OpCode::FreshWitness(r, new_tp)
                    }
                    OpCode::Constrain(a, b, c) => OpCode::Constrain(a, b, c),
                    OpCode::NextDCoeff(a) => OpCode::NextDCoeff(a),
                    OpCode::BumpD(a, b, c) => OpCode::BumpD(a, b, c),
                    OpCode::MkSeq(r, l, stp, tp) => {
                        let r_taint = function_taint
                            .get_value_taint(r)
                            .child_taint_type()
                            .unwrap();
                        OpCode::MkSeq(r, l, stp, self.typify_taint(tp, &r_taint))
                    }
                    OpCode::Cast(r, l, t) => OpCode::Cast(r, l, t),
                    OpCode::Truncate(r, l, out_bits, in_bits) => {
                        OpCode::Truncate(r, l, out_bits, in_bits)
                    }
                    OpCode::Not(r, l) => OpCode::Not(r, l),
                    OpCode::ToBits(r, l, e, s) => OpCode::ToBits(r, l, e, s),
                    OpCode::MemOp(kind, value) => OpCode::MemOp(kind, value),
                    OpCode::BoxField(r, l, c) => OpCode::BoxField(
                        r,
                        l,
                        function_taint
                            .get_value_taint(r)
                            .toplevel_taint()
                            .expect_constant(),
                    ),
                    OpCode::UnboxField(r, l) => OpCode::UnboxField(r, l),
                    OpCode::MulConst(r, l, c) => OpCode::MulConst(r, l, c),
                };
                new_instructions.push(new);
            }
            new_block.put_instructions(new_instructions);

            new_block.set_terminator(block.take_terminator().unwrap());

            function.put_block(block_id, new_block);
        }

        for (ret, ret_taint) in returns.into_iter().zip(function_taint.returns_taint.iter()) {
            let ret_typ = self.typify_taint(ret, ret_taint);
            function.add_return_type(ret_typ);
        }

        let cfg_taint_param = if matches!(
            function_taint.cfg_taint,
            Taint::Constant(ConstantTaint::Witness)
        ) {
            Some(
                function.add_parameter(function.get_entry_id(), Type::u(1, ConstantTaint::Witness)),
            )
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
                    OpCode::BinaryArithOp(_, _, _, _)
                    | OpCode::Cmp(_, _, _, _)
                    | OpCode::MkSeq(_, _, _, _)
                    | OpCode::Cast(_, _, _)
                    | OpCode::Truncate(_, _, _, _)
                    | OpCode::Not(_, _)
                    | OpCode::ToBits(_, _, _, _) => {
                        new_instructions.push(instruction);
                    }
                    OpCode::AssertEq(_, _) => {
                        assert_eq!(block_taint, None); // TODO: support conditional asserts
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
                    OpCode::ArraySet(_, arr, idx, _) => {
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
                    OpCode::Alloc(_, _, _) => {
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
                                    new_instructions.push(OpCode::BinaryArithOp(
                                        BinaryArithOpKind::And,
                                        result_val,
                                        tnt,
                                        cond,
                                    ));
                                    result_val
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
                                    Type {
                                        expr: TypeExpr::Array(_, _),
                                        ..
                                    } => {
                                        panic!("TODO: Witness array not supported yet")
                                    }
                                    Type {
                                        expr: TypeExpr::Ref(_),
                                        ..
                                    } => {
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

                            let merger_block = function.add_block();
                            function
                                .get_block_mut(out_false_block)
                                .set_terminator(Terminator::Jmp(merger_block, vec![]));
                            function
                                .get_block_mut(merger_block)
                                .set_terminator(Terminator::Jmp(merge, vec![]));

                            if args_passed_from_lhs.len() > 0 {
                                for ((res, _), (lhs, rhs)) in merge_params.iter().zip(
                                    args_passed_from_lhs.iter().zip(args_passed_from_rhs.iter()),
                                ) {
                                    function
                                        .get_block_mut(merger_block)
                                        .push_instruction(OpCode::Select(*res, cond, *lhs, *rhs));
                                }
                            }
                        }
                    }
                }
                _ => {}
            };

            block.put_instructions(new_instructions);
            function.put_block(block_id, block);
        }

        function
    }

    fn typify_taint(&self, typ: Type<Empty>, taint: &TaintType) -> Type<ConstantTaint> {
        match (typ.expr, taint) {
            (TypeExpr::Field, TaintType::Primitive(taint)) => Type {
                expr: TypeExpr::Field,
                annotation: taint.expect_constant(),
            },
            (TypeExpr::U(size), TaintType::Primitive(taint)) => Type {
                expr: TypeExpr::U(size),
                annotation: taint.expect_constant(),
            },
            (TypeExpr::Array(inner, size), TaintType::NestedImmutable(top, inner_taint)) => Type {
                expr: TypeExpr::Array(
                    Box::new(self.typify_taint(*inner, inner_taint.as_ref())),
                    size,
                ),
                annotation: top.expect_constant(),
            },
            (TypeExpr::Slice(inner), TaintType::NestedImmutable(top, inner_taint)) => Type {
                expr: TypeExpr::Slice(Box::new(self.typify_taint(*inner, inner_taint.as_ref()))),
                annotation: top.expect_constant(),
            },
            (TypeExpr::Ref(inner), TaintType::NestedMutable(top, inner_taint)) => Type {
                expr: TypeExpr::Ref(Box::new(self.typify_taint(*inner, inner_taint.as_ref()))),
                annotation: top.expect_constant(),
            },
            (tp, taint) => panic!("Unexpected type {:?} with taint {:?}", tp, taint),
        }
    }
}
