use itertools::Itertools;
use noirc_evaluator::ssa::ir::basic_block::BasicBlockId;
use noirc_evaluator::ssa::ir::instruction::{BinaryOp, Instruction};
use noirc_evaluator::ssa::ssa_gen::Ssa;
use std::collections::HashMap;

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
struct ValueId(u64);
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
struct BlockId(u64);
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
struct FunctionId(u64);

enum Value {
    Instruction { typ: Type },
    Constant { value: ark_bn254::Fr, typ: Type },
    Param { typ: Type}
}

#[derive(Debug, Clone)]
struct Type {
    expr: TyExpr,
    level: Option<Level>,
}
#[derive(Debug, Clone)]
enum TyExpr {
    Field,
    U(usize),
    I(usize),
    Array(Box<Type>, usize),
}
#[derive(Debug, Clone)]

enum Level {
    Witness,
    Runtime,
}

pub struct SSA {
    functions: HashMap<FunctionId, Function>,
    main_id: FunctionId,
}

impl SSA {
    pub fn from_noir(nr_ssa: Ssa) -> Self {
        let mut current_fn_id = 0_u64;
        let mut fn_mapping: HashMap<noirc_evaluator::ssa::ir::function::FunctionId, FunctionId> =
            HashMap::new();
        for (nr_id, _) in &nr_ssa.functions {
            let id = FunctionId(current_fn_id);
            current_fn_id += 1;
            fn_mapping.insert(nr_id.clone(), id);
        }

        let mut functions = HashMap::<FunctionId, Function>::new();

        for (nr_id, func) in nr_ssa.functions {
            functions.insert(fn_mapping[&nr_id], Function::from_noir(func, &fn_mapping));
        }

        let main_id = fn_mapping[&nr_ssa.main_id];
        SSA { functions, main_id }
    }

    pub fn to_string(&self) -> String {
        println!("Entry point: {}", self.main_id.0);
        self.functions
            .iter()
            .map(|(fn_id, func)| func.to_string(*fn_id))
            .join("\n\n")
    }
}

impl Function {
    fn from_noir(
        nr_fn: noirc_evaluator::ssa::ir::function::Function,
        fn_mapping: &HashMap<noirc_evaluator::ssa::ir::function::FunctionId, FunctionId>,
    ) -> Function {
        let mut current_block_id = 0_u64;
        let mut block_mapping: HashMap<BasicBlockId, BlockId> = HashMap::new();
        for (nr_id, _) in nr_fn.dfg.blocks.iter() {
            let id = BlockId(current_block_id);
            current_block_id += 1;
            block_mapping.insert(nr_id.clone(), id);
        }

        let mut blocks = HashMap::<BlockId, Block>::new();
        for (nr_id, block) in nr_fn.dfg.blocks.iter() {
            blocks.insert(
                block_mapping[&nr_id],
                Block {
                    parameters: block
                        .parameters
                        .iter()
                        .map(|v| ValueId(v.to_u32() as u64))
                        .collect(),
                    instructions: block
                        .instructions
                        .iter()
                        .map(|i| {
                            let outputs = nr_fn.dfg.results[i].clone();
                            let outputs = outputs
                                .to_vec()
                                .iter()
                                .map(|v| ValueId(v.to_u32() as u64))
                                .collect();
                            OpCode::from_noir(&nr_fn.dfg.instructions[i.clone()], outputs)
                        })
                        .collect(),
                    terminator: block.terminator.clone().map(|t| Terminator::from_noir(&t)),
                },
            );
        }
        let entry = block_mapping[&nr_fn.entry_block];

        let params = blocks[&entry].parameters.clone();
        blocks.get_mut(&entry).unwrap().parameters = vec![];
        Function {
            value_types: HashMap::new(),
            entry_block: entry,
            inputs: params,
            blocks,
        }
    }

    pub fn to_string(&self, id: FunctionId) -> String {
        let params = self
            .inputs
            .iter()
            .map(|v| format!("_{}", v.0))
            .join(", ");
        let header = format!("fn_{}({}) {{", id.0, params);
        let blocks = self
            .blocks
            .iter()
            .map(|(id, block)| block.to_string(id.clone()))
            .join("\n");
        let footer = "}".to_string();
        format!("{}\n{}\n{}", header, blocks, footer)
    }
}

impl OpCode {
    fn from_noir(instruction: &Instruction, results: Vec<ValueId>) -> Self {
        match instruction {
            Instruction::Binary(bin) => match bin.operator {
                BinaryOp::Eq => OpCode::Eq(
                    results[0],
                    ValueId(bin.lhs.to_u32() as u64),
                    ValueId(bin.rhs.to_u32() as u64),
                ),
                _ => {
                    panic!(
                        "Unsupported binary operation in SSA conversion: {:?}",
                        bin.operator
                    );
                }
            },
            Instruction::Constrain(a, b, _) => {
                OpCode::AssertEq(ValueId(a.to_u32() as u64), ValueId(b.to_u32() as u64))
            }
            _ => {
                panic!(
                    "Unsupported instruction type in SSA conversion: {:?}",
                    instruction
                );
            }
        }
    }
}

impl Terminator {
    fn from_noir(
        terminator: &noirc_evaluator::ssa::ir::instruction::TerminatorInstruction,
    ) -> Self {
        match terminator {
            noirc_evaluator::ssa::ir::instruction::TerminatorInstruction::Jmp {
                destination,
                arguments,
                ..
            } => Terminator::Jmp(
                BlockId(destination.to_u32() as u64),
                arguments
                    .iter()
                    .map(|v| ValueId(v.to_u32() as u64))
                    .collect(),
            ),
            noirc_evaluator::ssa::ir::instruction::TerminatorInstruction::Return {
                return_values,
                ..
            } => Terminator::Return(
                return_values
                    .iter()
                    .map(|v| ValueId(v.to_u32() as u64))
                    .collect(),
            ),
            // noirc_evaluator::ssa::ir::instruction::TerminatorInstruction::JmpIf(
            //     cond,
            //     true_block,
            //     false_block,
            // ) => Terminator::JmpIf(
            //     ValueId(cond.to_u32() as u64),
            //     BlockId(true_block.to_u32() as u64),
            //     BlockId(false_block.to_u32() as u64),
            // ),
            // noirc_evaluator::ssa::ir::instruction::TerminatorInstruction::Return(values) => {
            //     Terminator::Return(
            //         values
            //             .into_iter()
            //             .map(|v| ValueId(v.to_u32() as u64))
            //             .collect(),
            //     )
            // }
            _ => {
                panic!(
                    "Unsupported terminator type in SSA conversion: {:?}",
                    terminator
                );
            }
        }
    }
}

struct Function {
    values: HashMap<ValueId, Value>,
    entry_block: BlockId,
    inputs: Vec<ValueId>,
    blocks: HashMap<BlockId, Block>,
}

struct Block {
    parameters: Vec<ValueId>,
    instructions: Vec<OpCode>,
    terminator: Option<Terminator>,
}

impl Block {
    fn to_string(&self, id: BlockId) -> String {
        let params = self.parameters.iter().map(|v| v.0).join(", ");
        let instructions = self
            .instructions
            .iter()
            .map(|i| format!("    {}", i.to_string()))
            .join("\n");
        let terminator = match &self.terminator {
            Some(t) => format!("    {}", t.to_string()),
            None => "".to_string(),
        };
        format!(
            "  block_{}({}) {{\n{}\n{}\n  }}",
            id.0, params, instructions, terminator
        )
    }
}
#[derive(Debug, Clone)]

enum OpCode {
    Eq(ValueId, ValueId, ValueId),           // _1 = _2 == _3
    Add(ValueId, ValueId, ValueId),          // _1 = _2 + _3
    Lt(ValueId, ValueId, ValueId),           // _1 = _2 < _3
    Alloc(ValueId, Type),                    // _1 = alloc(Type)
    Store(ValueId, ValueId),                 // *_1 = _2
    Load(ValueId, ValueId),                  // _1 = *_2
    AssertEq(ValueId, ValueId),              // assert _1 == _2
    Call(ValueId, FunctionId, Vec<ValueId>), // _1 = call function(_2, _3, ...)
    ArrayGet(ValueId, ValueId, ValueId),     // _1 = _2[_3]
}

impl OpCode {
    pub fn to_string(&self) -> String {
        match self {
            OpCode::Eq(result, lhs, rhs) => format!("_{} = _{} == _{}", result.0, lhs.0, rhs.0),
            OpCode::Add(result, lhs, rhs) => format!("_{} = _{} + _{}", result.0, lhs.0, rhs.0),
            OpCode::Lt(result, lhs, rhs) => format!("_{} = _{} < _{}", result.0, lhs.0, rhs.0),
            OpCode::Alloc(result, typ) => format!("_{} = alloc({:?})", result.0, typ),
            OpCode::Store(ptr, value) => format!("*_{} = _{}", ptr.0, value.0),
            OpCode::Load(result, ptr) => format!("_{} = *_{}", result.0, ptr.0),
            OpCode::AssertEq(lhs, rhs) => format!("assert _{} == _{}", lhs.0, rhs.0),
            OpCode::Call(result, fn_id, args) => {
                let args_str = args.iter().map(|v| format!("_{}", v.0)).join(", ");
                format!("_{} = call {}({})", result.0, fn_id.0, args_str)
            }
            OpCode::ArrayGet(result, array, index) => {
                format!("_{} = _{}[_{}]", result.0, array.0, index.0)
            }
        }
    }
}
#[derive(Debug, Clone)]
enum Terminator {
    Jmp(BlockId, Vec<ValueId>),
    JmpIf(ValueId, BlockId, BlockId),
    Return(Vec<ValueId>),
}

impl Terminator {
    pub fn to_string(&self) -> String {
        match self {
            Terminator::Jmp(block_id, args) => {
                let args_str = args.iter().map(|v| format!("_{}", v.0)).join(", ");
                format!("jmp {}({})", block_id.0, args_str)
            }
            Terminator::JmpIf(cond, true_block, false_block) => format!(
                "jmp_if _{} to {}, else to {}",
                cond.0, true_block.0, false_block.0
            ),
            Terminator::Return(values) => {
                let values_str = values.iter().map(|v| format!("_{}", v.0)).join(", ");
                format!("return {}", values_str)
            }
        }
    }
}