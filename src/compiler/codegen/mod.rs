use std::collections::HashMap;

use crate::{
    compiler::{
        analysis::types::{FunctionTypeInfo, TypeInfo},
        flow_analysis::{CFG, FlowAnalysis},
        ir::r#type::{Type, TypeExpr},
        ssa::{
            self, BinaryArithOpKind, Block, BlockId, CmpKind, Const, Function, FunctionId, MemOp, SSA, Terminator, ValueId
        },
        taint_analysis::ConstantTaint,
    },
    vm::bytecode,
};

struct FrameLayouter {
    next_free: usize,
    variables: HashMap<ValueId, usize>,
}

impl FrameLayouter {
    fn new() -> Self {
        Self {
            next_free: 2,
            variables: HashMap::new(),
        }
    }

    fn get_value(&mut self, value: ValueId) -> bytecode::FramePosition {
        bytecode::FramePosition(self.variables[&value])
    }

    fn alloc_value(&mut self, value: ValueId, tp: &Type<ConstantTaint>) -> bytecode::FramePosition {
        self.variables.insert(value, self.next_free);
        let r = self.next_free;
        self.next_free += self.type_size(&tp);
        bytecode::FramePosition(r)
    }

    fn alloc_u64(&mut self, value: ValueId, size: usize) -> bytecode::FramePosition {
        assert!(size <= 64);
        self.variables.insert(value, self.next_free);
        let r = self.next_free;
        self.next_free += 1;
        bytecode::FramePosition(r)
    }

    fn alloc_field(&mut self, value: ValueId) -> bytecode::FramePosition {
        self.variables.insert(value, self.next_free);
        let r = self.next_free;
        self.next_free += bytecode::LIMBS;
        bytecode::FramePosition(r)
    }

    fn alloc_ptr(&mut self, value: ValueId) -> bytecode::FramePosition {
        self.variables.insert(value, self.next_free);
        let r = self.next_free;
        self.next_free += 1;
        bytecode::FramePosition(r)
    }

    fn type_size(&self, tp: &Type<ConstantTaint>) -> usize {
        match tp.expr {
            TypeExpr::Field => bytecode::LIMBS,
            TypeExpr::U(bits) => {
                assert!(bits <= 64);
                1
            }
            TypeExpr::Array(_, _) => 1, // Ptr
            TypeExpr::Slice(_) => 1,    // Ptr
            _ => todo!(),
        }
    }

    // This method needs to ensure contiguous storage!
    fn alloc_many_contiguous(
        &mut self,
        values: Vec<(ValueId, &Type<ConstantTaint>)>,
    ) -> bytecode::FramePosition {
        let r = self.next_free;
        for (value, tp) in values {
            self.alloc_value(value, tp);
        }
        bytecode::FramePosition(r)
    }
}

struct EmitterState {
    code: Vec<bytecode::OpCode>,
    block_entrances: HashMap<BlockId, usize>,
    block_exits: HashMap<BlockId, usize>,
}

impl EmitterState {
    fn new() -> Self {
        Self {
            code: Vec::new(),
            block_entrances: HashMap::new(),
            block_exits: HashMap::new(),
        }
    }

    fn push_op(&mut self, op: bytecode::OpCode) {
        self.code.push(op);
    }

    fn enter_block(&mut self, block: BlockId) {
        self.block_entrances.insert(block, self.code.len());
    }

    fn exit_block(&mut self, block: BlockId) {
        self.block_exits.insert(block, self.code.len());
    }
}

pub struct CodeGen {}

impl CodeGen {
    pub fn new() -> Self {
        Self {}
    }

    pub fn run(
        &self,
        ssa: &SSA<ConstantTaint>,
        cfg: &FlowAnalysis,
        type_info: &TypeInfo<ConstantTaint>,
    ) -> bytecode::Program {
        let function = ssa.get_main();
        let function = self.run_function(
            function,
            cfg.get_function_cfg(ssa.get_main_id()),
            type_info.get_function(ssa.get_main_id()),
        );

        let mut functions = vec![function];

        let mut function_ids = HashMap::new();
        function_ids.insert(ssa.get_main_id(), 0);

        let mut cur_fn_begin = functions[0].code.len();

        for (function_id, function) in ssa.iter_functions() {
            if *function_id == ssa.get_main_id() {
                continue;
            }
            let function = self.run_function(
                function,
                cfg.get_function_cfg(*function_id),
                type_info.get_function(*function_id),
            );
            function_ids.insert(*function_id, cur_fn_begin);
            cur_fn_begin += function.code.len();
            functions.push(function);
        }

        for function in functions.iter_mut() {
            for op in function.code.iter_mut() {
                match op {
                    bytecode::OpCode::Call(target, _, _) => {
                        target.0 =
                            *function_ids.get(&FunctionId(target.0 as u64)).unwrap() as isize;
                    }
                    _ => {}
                }
            }
        }

        bytecode::Program {
            functions: functions,
        }
    }

    fn run_function(
        &self,
        function: &Function<ConstantTaint>,
        cfg: &CFG,
        type_info: &FunctionTypeInfo<ConstantTaint>,
    ) -> bytecode::Function {
        let mut layouter = FrameLayouter::new();
        let entry = function.get_entry();
        let mut emitter = EmitterState::new();

        // Entry block params need to be allocated at the beginning of the frame (after return address and return data pointer)
        for (param, tp) in entry.get_parameters() {
            layouter.alloc_value(*param, tp);
        }

        // Consts get dumped in the first block
        for (val, constant) in function.iter_consts() {
            match constant {
                Const::U(u, v) => emitter.push_op(bytecode::OpCode::Const(
                    layouter.alloc_u64(*val, *u),
                    *v as u64,
                )),
                Const::Field(v) => {
                    let start = layouter.alloc_field(*val);
                    for i in 0..bytecode::LIMBS {
                        // pushing in montgomery form
                        emitter.push_op(bytecode::OpCode::Const(start.offset(i as isize), v.0.0[i]))
                    }
                }
            }
        }

        self.run_block_body(
            function,
            function.get_entry_id(),
            entry,
            type_info,
            &mut layouter,
            &mut emitter,
        );

        for block_id in cfg.get_domination_pre_order() {
            if block_id == function.get_entry_id() {
                continue;
            }
            let block = function.get_block(block_id);
            for (param, tp) in block.get_parameters() {
                layouter.alloc_value(*param, tp);
            }
            self.run_block_body(
                function,
                block_id,
                block,
                type_info,
                &mut layouter,
                &mut emitter,
            );
        }

        for (block_id, block) in function.get_blocks() {
            let mut block_exit_start: usize = emitter.block_exits[&block_id];
            match block.get_terminator().unwrap() {
                Terminator::Jmp(tgt, args) => {
                    let params = function.get_block(*tgt).get_parameters();
                    for (arg, (param, tp)) in args.iter().zip(params) {
                        emitter.code[block_exit_start] = bytecode::OpCode::Mov(
                            layouter.get_value(*param),
                            layouter.get_value(*arg),
                            layouter.type_size(tp),
                        );
                        block_exit_start += 1;
                    }
                    emitter.code[block_exit_start] = bytecode::OpCode::Jmp(bytecode::JumpTarget(
                        *emitter.block_entrances.get(&tgt).unwrap() as isize,
                    ));
                    block_exit_start += 1;
                }
                Terminator::JmpIf(cond, if_t, if_f) => {
                    emitter.code[block_exit_start] = bytecode::OpCode::JmpIf(
                        layouter.get_value(*cond),
                        bytecode::JumpTarget(*emitter.block_entrances.get(&if_t).unwrap() as isize),
                        bytecode::JumpTarget(*emitter.block_entrances.get(&if_f).unwrap() as isize),
                    );
                    block_exit_start += 1;
                }
                Terminator::Return(_) => {
                    // Nothing to do, returns are correct right away
                }
            }
        }

        bytecode::Function {
            name: function.get_name().to_string(),
            frame_size: layouter.next_free,
            code: emitter.code,
        }
    }

    fn run_block_body(
        &self,
        function: &Function<ConstantTaint>,
        block_id: BlockId,
        block: &Block<ConstantTaint>,
        type_info: &FunctionTypeInfo<ConstantTaint>,
        layouter: &mut FrameLayouter,
        emitter: &mut EmitterState,
    ) {
        emitter.enter_block(block_id);
        for instruction in block.get_instructions() {
            match instruction {
                ssa::OpCode::BinaryArithOp(BinaryArithOpKind::Add, val, op1, op2) => {
                    match &type_info.get_value_type(*val).expr {
                        TypeExpr::Field => {
                            let result = layouter.alloc_field(*val);
                            emitter.push_op(bytecode::OpCode::AddF(
                                result,
                                layouter.get_value(*op1),
                                layouter.get_value(*op2),
                            ));
                        }
                        TypeExpr::U(bits) => {
                            let result = layouter.alloc_u64(*val, *bits);
                            emitter.push_op(bytecode::OpCode::AddU(
                                *bits,
                                result,
                                layouter.get_value(*op1),
                                layouter.get_value(*op2),
                            ));
                        }
                        t => panic!("Unsupported type for addition: {:?}", t),
                    }
                }
                ssa::OpCode::BinaryArithOp(BinaryArithOpKind::Sub, val, op1, op2) => {
                    match &type_info.get_value_type(*val).expr {
                        TypeExpr::Field => {
                            let result = layouter.alloc_field(*val);
                            emitter.push_op(bytecode::OpCode::SubF(
                                result,
                                layouter.get_value(*op1),
                                layouter.get_value(*op2),
                            ));
                        }
                        TypeExpr::U(bits) => {
                            let result = layouter.alloc_u64(*val, *bits);
                            emitter.push_op(bytecode::OpCode::SubU(
                                *bits,
                                result,
                                layouter.get_value(*op1),
                                layouter.get_value(*op2),
                            ));
                        }
                        t => panic!("Unsupported type for addition: {:?}", t),
                    }
                }
                ssa::OpCode::BinaryArithOp(BinaryArithOpKind::Div, val, op1, op2) => {
                    match &type_info.get_value_type(*val).expr {
                        TypeExpr::Field => {
                            let result = layouter.alloc_field(*val);
                            emitter.push_op(bytecode::OpCode::DivF(
                                result,
                                layouter.get_value(*op1),
                                layouter.get_value(*op2),
                            ));
                        }
                        TypeExpr::U(bits) => {
                            let result = layouter.alloc_u64(*val, *bits);
                            emitter.push_op(bytecode::OpCode::DivU(
                                *bits,
                                result,
                                layouter.get_value(*op1),
                                layouter.get_value(*op2),
                            ));
                        }
                        t => panic!("Unsupported type for addition: {:?}", t),
                    }
                }
                ssa::OpCode::BinaryArithOp(BinaryArithOpKind::Mul, val, op1, op2) => {
                    match &type_info.get_value_type(*val).expr {
                        TypeExpr::Field => {
                            let result = layouter.alloc_field(*val);
                            emitter.push_op(bytecode::OpCode::MulF(
                                result,
                                layouter.get_value(*op1),
                                layouter.get_value(*op2),
                            ));
                        }
                        TypeExpr::U(bits) => {
                            let result = layouter.alloc_u64(*val, *bits);
                            emitter.push_op(bytecode::OpCode::MulU(
                                *bits,
                                result,
                                layouter.get_value(*op1),
                                layouter.get_value(*op2),
                            ));
                        }
                        t => panic!("Unsupported type for multiplication: {:?}", t),
                    }
                }
                ssa::OpCode::BinaryArithOp(BinaryArithOpKind::And, val, op1, op2) => {
                    match &type_info.get_value_type(*val).expr {
                        TypeExpr::Field => {
                            panic!("Unsupported: field and");
                            // let result = layouter.alloc_field(*val);
                            // emitter.push_op(bytecode::OpCode::MulF(
                            //     result,
                            //     layouter.get_value(*op1),
                            //     layouter.get_value(*op2),
                            // ));
                        }
                        TypeExpr::U(bits) => {
                            let result = layouter.alloc_u64(*val, *bits);
                            emitter.push_op(bytecode::OpCode::AndU(
                                *bits,
                                result,
                                layouter.get_value(*op1),
                                layouter.get_value(*op2),
                            ));
                        }
                        t => panic!("Unsupported type for multiplication: {:?}", t),
                    }
                }
                ssa::OpCode::Cmp(CmpKind::Lt, val, op1, op2) => {
                    match &type_info.get_value_type(*val).expr {
                        TypeExpr::U(bits) => {
                            let result = layouter.alloc_u64(*val, *bits);
                            emitter.push_op(bytecode::OpCode::LtU(
                                *bits,
                                result,
                                layouter.get_value(*op1),
                                layouter.get_value(*op2),
                            ));
                        }
                        t => panic!("Unsupported type for comparison: {:?}", t),
                    }
                }
                ssa::OpCode::Cmp(CmpKind::Eq, val, op1, op2) => {
                    match &type_info.get_value_type(*val).expr {
                        TypeExpr::U(bits) => {
                            let result = layouter.alloc_u64(*val, *bits);
                            emitter.push_op(bytecode::OpCode::EqU(
                                *bits,
                                result,
                                layouter.get_value(*op1),
                                layouter.get_value(*op2),
                            ));
                        }
                        t => panic!("Unsupported type for comparison: {:?}", t),
                    }
                }
                ssa::OpCode::Truncate(val, op, to_bits, from_bits) => {
                    let result = layouter.alloc_u64(*val, 64);
                    assert!(*to_bits <= 64);
                    let in_type = type_info.get_value_type(*op);
                    if in_type.is_field() {
                        emitter.push_op(bytecode::OpCode::TruncateFToU(
                            result,
                            layouter.get_value(*op),
                            *to_bits,
                        ));
                    } else {
                        assert!(*from_bits <= 64);
                        emitter.push_op(bytecode::OpCode::TruncateUToU(
                            result,
                            layouter.get_value(*op),
                            *to_bits,
                        ))
                    }
                }
                ssa::OpCode::Cast(r, v, tgt) => {
                    let result = layouter.alloc_value(*r, &type_info.get_value_type(*r));
                    // TODO: Implement this, it _will_ break
                }
                ssa::OpCode::Not(r, v) => {
                    let result = layouter.alloc_value(*r, &type_info.get_value_type(*r));
                    emitter.push_op(bytecode::OpCode::Not(
                        result,
                        layouter.get_value(*v),
                    ));
                }
                ssa::OpCode::Constrain(a, b, c) => {
                    let a_type = type_info.get_value_type(*a);
                    let b_type = type_info.get_value_type(*b);
                    let c_type = type_info.get_value_type(*c);
                    if !a_type.is_field() || !b_type.is_field() || !c_type.is_field() {
                        panic!(
                            "Unsupported type for constrain: {:?}, {:?}, {:?}",
                            a_type, b_type, c_type
                        );
                    }
                    emitter.push_op(bytecode::OpCode::ConstraintR1C(
                        layouter.get_value(*a),
                        layouter.get_value(*b),
                        layouter.get_value(*c),
                    ));
                }
                ssa::OpCode::WriteWitness(None, v, _) => {
                    emitter.push_op(bytecode::OpCode::WriteWitness(layouter.get_value(*v)));
                }
                ssa::OpCode::ArrayGet(r, arr, idx) => {
                    let res = layouter.alloc_value(*r, &type_info.get_value_type(*r));
                    emitter.push_op(bytecode::OpCode::ArrayGet(
                        res,
                        layouter.get_value(*arr),
                        layouter.get_value(*idx),
                        layouter.type_size(&type_info.get_value_type(*arr).get_array_element()),
                    ));
                }
                ssa::OpCode::ArraySet(r, arr, idx, val) => {
                    let res = layouter.alloc_value(*r, &type_info.get_value_type(*r));
                    emitter.push_op(bytecode::OpCode::ArraySet(
                        res,
                        layouter.get_value(*arr),
                        layouter.get_value(*idx),
                        layouter.get_value(*val),
                        layouter.type_size(&type_info.get_value_type(*arr).get_array_element()),
                    ));
                }
                ssa::OpCode::MkSeq(r, vals, _, eltype) => {
                    let res = layouter.alloc_value(*r, &type_info.get_value_type(*r));
                    let args = vals
                        .iter()
                        .map(|a| layouter.get_value(*a))
                        .collect::<Vec<_>>();
                    emitter.push_op(bytecode::OpCode::MkArray(
                        res,
                        layouter.type_size(eltype),
                        args,
                    ));
                }

                ssa::OpCode::Call(r, fnid, params) => {
                    let r = layouter.alloc_many_contiguous(
                        r.iter()
                            .map(|a| (*a, type_info.get_value_type(*a)))
                            .collect(),
                    );
                    let args = params
                        .iter()
                        .map(|a| {
                            (
                                layouter.type_size(&type_info.get_value_type(*a)),
                                layouter.get_value(*a),
                            )
                        })
                        .collect::<Vec<_>>();
                    emitter.push_op(bytecode::OpCode::Call(
                        bytecode::JumpTarget(fnid.0 as isize),
                        args,
                        r,
                    ));
                }
                ssa::OpCode::MemOp(MemOp::Drop, r) => {
                    emitter.push_op(bytecode::OpCode::Drop(layouter.get_value(*r)));
                }
                ssa::OpCode::MemOp(MemOp::Bump(size), r) => {
                    emitter.push_op(bytecode::OpCode::IncRC(*size, layouter.get_value(*r)));
                }
                ssa::OpCode::AssertEq(_, _) => {
                    // TODO: Implement this
                }
                ssa::OpCode::ToBits(r, _, _, _) => {
                    // This will bite me soon
                    _ = layouter.alloc_value(*r, &type_info.get_value_type(*r));
                }
                other => panic!("Unsupported instruction: {:?}", other),
            }
        }
        emitter.exit_block(block_id);
        match block.get_terminator().unwrap() {
            Terminator::Jmp(_, params) => {
                emitter.push_op(bytecode::OpCode::Nop);
                for i in 0..params.len() {
                    emitter.push_op(bytecode::OpCode::Nop);
                }
            }
            Terminator::JmpIf(_, _, _) => {
                emitter.push_op(bytecode::OpCode::Nop);
            }
            Terminator::Return(params) => {
                let mut offset = 0;
                for param in params {
                    let size = layouter.type_size(&type_info.get_value_type(*param));
                    emitter.push_op(bytecode::OpCode::WritePtr(
                        bytecode::FramePosition::return_data_ptr(),
                        offset,
                        layouter.get_value(*param),
                        size,
                    ));
                    offset += size as isize;
                }
                emitter.push_op(bytecode::OpCode::Return);
            }
        }
    }
}
