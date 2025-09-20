use std::collections::HashMap;

use crate::{
    compiler::{
        analysis::types::{FunctionTypeInfo, TypeInfo},
        flow_analysis::{CFG, FlowAnalysis},
        ir::r#type::{Type, TypeExpr},
        ssa::{
            self, BinaryArithOpKind, Block, BlockId, CmpKind, Const, DMatrix, Function, FunctionId,
            MemOp, SSA, Terminator, ValueId,
        },
        taint_analysis::ConstantTaint,
    },
    vm::{self, bytecode},
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
            TypeExpr::BoxedField => 1,  // Ptr
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

        let mut cur_fun_off = 0;
        for function in functions.iter_mut() {
            for op in function.code.iter_mut() {
                match op {
                    bytecode::OpCode::Call { func, .. } => {
                        func.0 = *function_ids.get(&FunctionId(func.0 as u64)).unwrap() as isize;
                    }
                    bytecode::OpCode::Jmp { target } => {
                        target.0 += cur_fun_off as isize;
                    }
                    bytecode::OpCode::JmpIf { if_t, if_f, .. } => {
                        if_t.0 += cur_fun_off as isize;
                        if_f.0 += cur_fun_off as isize;
                    }
                    _ => {}
                }
            }
            cur_fun_off += function.code.len();
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
                Const::U(u, v) => emitter.push_op(bytecode::OpCode::MovConst {
                    res: layouter.alloc_u64(*val, *u),
                    val: *v as u64,
                }),
                Const::Field(v) => {
                    let start = layouter.alloc_field(*val);
                    for i in 0..bytecode::LIMBS {
                        // pushing in montgomery form
                        emitter.push_op(bytecode::OpCode::MovConst {
                            res: start.offset(i as isize),
                            val: v.0.0[i],
                        })
                    }
                }
                Const::BoxedField(v) => {
                    emitter.push_op(bytecode::OpCode::BoxedFieldAlloc {
                        res: layouter.alloc_ptr(*val),
                        data: *v,
                    });
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
                        emitter.code[block_exit_start] = bytecode::OpCode::MovFrame {
                            size: layouter.type_size(tp),
                            target: layouter.get_value(*param),
                            source: layouter.get_value(*arg),
                        };
                        block_exit_start += 1;
                    }
                    emitter.code[block_exit_start] = bytecode::OpCode::Jmp {
                        target: bytecode::JumpTarget(
                            *emitter.block_entrances.get(&tgt).unwrap() as isize
                        ),
                    };
                    block_exit_start += 1;
                }
                Terminator::JmpIf(cond, if_t, if_f) => {
                    emitter.code[block_exit_start] = bytecode::OpCode::JmpIf {
                        cond: layouter.get_value(*cond),
                        if_t: bytecode::JumpTarget(
                            *emitter.block_entrances.get(&if_t).unwrap() as isize
                        ),
                        if_f: bytecode::JumpTarget(
                            *emitter.block_entrances.get(&if_f).unwrap() as isize
                        ),
                    };
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
                            emitter.push_op(bytecode::OpCode::AddField {
                                res: result,
                                a: layouter.get_value(*op1),
                                b: layouter.get_value(*op2),
                            });
                        }
                        TypeExpr::U(bits) => {
                            let result = layouter.alloc_u64(*val, *bits);
                            emitter.push_op(bytecode::OpCode::AddU64 {
                                res: result,
                                a: layouter.get_value(*op1),
                                b: layouter.get_value(*op2),
                            });
                        }
                        t => panic!("Unsupported type for addition: {:?}", t),
                    }
                }
                ssa::OpCode::BinaryArithOp(BinaryArithOpKind::Sub, val, op1, op2) => {
                    match &type_info.get_value_type(*val).expr {
                        TypeExpr::Field => {
                            let result = layouter.alloc_field(*val);
                            emitter.push_op(bytecode::OpCode::SubField {
                                res: result,
                                a: layouter.get_value(*op1),
                                b: layouter.get_value(*op2),
                            });
                        }
                        TypeExpr::U(bits) => {
                            let result = layouter.alloc_u64(*val, *bits);
                            emitter.push_op(bytecode::OpCode::SubU64 {
                                res: result,
                                a: layouter.get_value(*op1),
                                b: layouter.get_value(*op2),
                            });
                        }
                        t => panic!("Unsupported type for addition: {:?}", t),
                    }
                }
                ssa::OpCode::BinaryArithOp(BinaryArithOpKind::Div, val, op1, op2) => {
                    match &type_info.get_value_type(*val).expr {
                        TypeExpr::Field => {
                            let result = layouter.alloc_field(*val);
                            emitter.push_op(bytecode::OpCode::DivField {
                                res: result,
                                a: layouter.get_value(*op1),
                                b: layouter.get_value(*op2),
                            });
                        }
                        TypeExpr::U(bits) => {
                            let result = layouter.alloc_u64(*val, *bits);
                            emitter.push_op(bytecode::OpCode::DivU64 {
                                res: result,
                                a: layouter.get_value(*op1),
                                b: layouter.get_value(*op2),
                            });
                        }
                        t => panic!("Unsupported type for addition: {:?}", t),
                    }
                }
                ssa::OpCode::BinaryArithOp(BinaryArithOpKind::Mul, val, op1, op2) => {
                    match &type_info.get_value_type(*val).expr {
                        TypeExpr::Field => {
                            let result = layouter.alloc_field(*val);
                            emitter.push_op(bytecode::OpCode::MulField {
                                res: result,
                                a: layouter.get_value(*op1),
                                b: layouter.get_value(*op2),
                            });
                        }
                        TypeExpr::U(bits) => {
                            let result = layouter.alloc_u64(*val, *bits);
                            emitter.push_op(bytecode::OpCode::MulU64 {
                                res: result,
                                a: layouter.get_value(*op1),
                                b: layouter.get_value(*op2),
                            });
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
                            emitter.push_op(bytecode::OpCode::AndU64 {
                                res: result,
                                a: layouter.get_value(*op1),
                                b: layouter.get_value(*op2),
                            });
                        }
                        t => panic!("Unsupported type for multiplication: {:?}", t),
                    }
                }
                ssa::OpCode::Cmp(CmpKind::Lt, val, op1, op2) => {
                    match &type_info.get_value_type(*val).expr {
                        TypeExpr::U(bits) => {
                            let result = layouter.alloc_u64(*val, *bits);
                            emitter.push_op(bytecode::OpCode::LtU64 {
                                res: result,
                                a: layouter.get_value(*op1),
                                b: layouter.get_value(*op2),
                            });
                        }
                        t => panic!("Unsupported type for comparison: {:?}", t),
                    }
                }
                ssa::OpCode::Cmp(CmpKind::Eq, val, op1, op2) => {
                    match &type_info.get_value_type(*val).expr {
                        TypeExpr::U(bits) => {
                            let result = layouter.alloc_u64(*val, *bits);
                            emitter.push_op(bytecode::OpCode::EqU64 {
                                res: result,
                                a: layouter.get_value(*op1),
                                b: layouter.get_value(*op2),
                            });
                        }
                        t => panic!("Unsupported type for comparison: {:?}", t),
                    }
                }
                ssa::OpCode::Truncate(val, op, to_bits, from_bits) => {
                    let result = layouter.alloc_u64(*val, 64);
                    assert!(*to_bits <= 64);
                    let in_type = type_info.get_value_type(*op);
                    if in_type.is_field() {
                        emitter.push_op(bytecode::OpCode::TruncateFToU {
                            res: result,
                            a: layouter.get_value(*op),
                            to_bits: *to_bits as u64,
                        });
                    } else {
                        assert!(*from_bits <= 64);
                        emitter.push_op(bytecode::OpCode::TruncateU64 {
                            res: result,
                            a: layouter.get_value(*op),
                            to_bits: *to_bits as u64,
                        });
                    }
                }
                ssa::OpCode::Cast(r, v, tgt) => {
                    let result = layouter.alloc_value(*r, &type_info.get_value_type(*r));
                    let l_type = type_info.get_value_type(*v);
                    let r_type = type_info.get_value_type(*r);
                    match (&l_type.expr, &r_type.expr) {
                        (TypeExpr::U(_), TypeExpr::U(_)) => {
                            emitter.push_op(bytecode::OpCode::MovFrame {
                                target: result,
                                source: layouter.get_value(*v),
                                size: layouter.type_size(&l_type),
                            })
                        }
                        (TypeExpr::Field, TypeExpr::U(_)) => {
                            emitter.push_op(bytecode::OpCode::CastFieldToU64 {
                                res: result,
                                a: layouter.get_value(*v),
                            });
                        }
                        (TypeExpr::U(_), TypeExpr::Field) => {
                            emitter.push_op(bytecode::OpCode::CastU64ToField {
                                res: result,
                                a: layouter.get_value(*v),
                            });
                        }
                        _ => panic!("Unsupported cast: {:?} -> {:?}", l_type, r_type),
                    }
                    // TODO: Implement this, it _will_ break
                }
                ssa::OpCode::Not(r, v) => {
                    let result = layouter.alloc_value(*r, &type_info.get_value_type(*r));
                    emitter.push_op(bytecode::OpCode::NotU64 {
                        res: result,
                        a: layouter.get_value(*v),
                    });
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
                    emitter.push_op(bytecode::OpCode::R1C {
                        a: layouter.get_value(*a),
                        b: layouter.get_value(*b),
                        c: layouter.get_value(*c),
                    });
                }
                ssa::OpCode::WriteWitness(None, v, _) => {
                    emitter.push_op(bytecode::OpCode::WriteWitness {
                        val: layouter.get_value(*v),
                    });
                }
                ssa::OpCode::ArrayGet(r, arr, idx) => {
                    let res = layouter.alloc_value(*r, &type_info.get_value_type(*r));
                    emitter.push_op(bytecode::OpCode::ArrayGet {
                        res,
                        array: layouter.get_value(*arr),
                        index: layouter.get_value(*idx),
                        stride: layouter
                            .type_size(&type_info.get_value_type(*arr).get_array_element()),
                    });
                }
                ssa::OpCode::ArraySet(r, arr, idx, val) => {
                    let res = layouter.alloc_value(*r, &type_info.get_value_type(*r));
                    emitter.push_op(bytecode::OpCode::ArraySet {
                        res,
                        array: layouter.get_value(*arr),
                        index: layouter.get_value(*idx),
                        source: layouter.get_value(*val),
                        stride: layouter
                            .type_size(&type_info.get_value_type(*arr).get_array_element()),
                    });
                }
                ssa::OpCode::MkSeq(r, vals, _, eltype) => {
                    let res = layouter.alloc_value(*r, &type_info.get_value_type(*r));
                    let args = vals
                        .iter()
                        .map(|a| layouter.get_value(*a))
                        .collect::<Vec<_>>();
                    let is_ptr = eltype.is_ref()
                        || eltype.is_slice()
                        || eltype.is_array()
                        || eltype.is_boxed_field();
                    let stride = layouter.type_size(eltype);
                    emitter.push_op(bytecode::OpCode::ArrayAlloc {
                        res,
                        stride: layouter.type_size(eltype),
                        meta: vm::array::BoxedLayout::array(args.len() * stride, is_ptr),
                        items: args,
                    });
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
                    emitter.push_op(bytecode::OpCode::Call {
                        func: bytecode::JumpTarget(fnid.0 as isize),
                        args: args,
                        ret: r,
                    });
                }
                ssa::OpCode::MemOp(MemOp::Drop, r) => {
                    // assert!(type_info.get_value_type(*r).is_array_or_slice());
                    emitter.push_op(bytecode::OpCode::DecRc {
                        array: layouter.get_value(*r),
                    });
                }
                ssa::OpCode::MemOp(MemOp::Bump(size), r) => {
                    // assert!(type_info.get_value_type(*r).is_array_or_slice());
                    emitter.push_op(bytecode::OpCode::IncRc {
                        array: layouter.get_value(*r),
                        amount: *size as u64,
                    });
                }
                ssa::OpCode::AssertEq(_, _) => {
                    // TODO: Implement this
                }
                ssa::OpCode::ToBits(r, _, _, _) => {
                    // This will bite me soon
                    _ = layouter.alloc_value(*r, &type_info.get_value_type(*r));
                }
                // ssa::OpCode::ConstraintDerivative(a, b, c) => {
                //     emitter.push_op(bytecode::OpCode::ConstraintDerivative {
                //         a: layouter.get_value(*a),
                //         b: layouter.get_value(*b),
                //         c: layouter.get_value(*c),
                //     });
                // }
                ssa::OpCode::NextDCoeff(out) => {
                    let v = layouter.alloc_field(*out);
                    emitter.push_op(bytecode::OpCode::NextDCoeff { v });
                }
                ssa::OpCode::BumpD(m, var, coeff) => {
                    let v = layouter.get_value(*var);
                    let coeff = layouter.get_value(*coeff);
                    emitter.push_op(match m {
                        DMatrix::A => bytecode::OpCode::BumpDa { v, coeff },
                        DMatrix::B => bytecode::OpCode::BumpDb { v, coeff },
                        DMatrix::C => bytecode::OpCode::BumpDc { v, coeff },
                    });
                }
                ssa::OpCode::FreshWitness(r, tp) => {
                    assert!(matches!(tp.expr, TypeExpr::BoxedField));
                    emitter.push_op(bytecode::OpCode::FreshWitness {
                        res: layouter.alloc_ptr(*r),
                    });
                }
                other => panic!("Unsupported instruction: {:?}", other),
            }
        }
        emitter.exit_block(block_id);
        match block.get_terminator().unwrap() {
            Terminator::Jmp(_, params) => {
                emitter.push_op(bytecode::OpCode::Nop {});
                for i in 0..params.len() {
                    emitter.push_op(bytecode::OpCode::Nop {});
                }
            }
            Terminator::JmpIf(_, _, _) => {
                emitter.push_op(bytecode::OpCode::Nop {});
            }
            Terminator::Return(params) => {
                let mut offset = 0;
                for param in params {
                    let size = layouter.type_size(&type_info.get_value_type(*param));
                    emitter.push_op(bytecode::OpCode::WritePtr {
                        ptr: bytecode::FramePosition::return_data_ptr(),
                        offset,
                        src: layouter.get_value(*param),
                        size,
                    });
                    offset += size as isize;
                }
                emitter.push_op(bytecode::OpCode::Ret {});
            }
        }
    }
}
