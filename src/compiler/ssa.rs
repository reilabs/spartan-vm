use crate::compiler::{
    flow_analysis::{CFG, FlowAnalysis},
    ir::r#type::{CommutativeMonoid, Empty, Type},
    ssa_gen::SsaConverter,
};
use core::panic;
use itertools::Itertools;
use std::{collections::HashMap, fmt::Display};

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct ValueId(pub u64);
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct BlockId(pub u64);
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct FunctionId(pub u64);

pub trait SsaAnnotator {
    fn annotate_value(&self, _function_id: FunctionId, _value_id: ValueId) -> String {
        "".to_string()
    }
    fn annotate_function(&self, _function_id: FunctionId) -> String {
        "".to_string()
    }
    fn annotate_block(&self, _function_id: FunctionId, _block_id: BlockId) -> String {
        "".to_string()
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct DefaultSsaAnnotator;
impl SsaAnnotator for DefaultSsaAnnotator {}

struct LocalFunctionAnnotator<'a> {
    function_id: FunctionId,
    annotator: &'a dyn SsaAnnotator,
}

impl<'a> LocalFunctionAnnotator<'a> {
    pub fn new(function_id: FunctionId, annotator: &'a dyn SsaAnnotator) -> Self {
        Self {
            function_id,
            annotator,
        }
    }

    pub fn annotate_value(&self, value_id: ValueId) -> String {
        self.annotator.annotate_value(self.function_id, value_id)
    }
}

pub struct SSA<V> {
    functions: HashMap<FunctionId, Function<V>>,
    main_id: FunctionId,
    next_function_id: u64,
}

impl<V> SSA<V>
where
    V: Clone,
{
    pub fn new() -> Self {
        let main_function = Function::empty("main".to_string());
        let main_id = FunctionId(0_u64);
        let mut functions = HashMap::new();
        functions.insert(main_id, main_function);
        SSA {
            functions,
            main_id,
            next_function_id: 1,
        }
    }

    pub fn prepare_rebuild<V2>(self) -> (SSA<V2>, HashMap<FunctionId, Function<V>>) {
        (
            SSA {
                functions: HashMap::new(),
                main_id: self.main_id,
                next_function_id: self.next_function_id,
            },
            self.functions,
        )
    }

    pub fn insert_function(&mut self, function: Function<V>) -> FunctionId {
        let new_id = FunctionId(self.next_function_id);
        self.next_function_id += 1;
        self.functions.insert(new_id, function);
        new_id
    }

    pub fn set_entry_point(&mut self, id: FunctionId) {
        self.main_id = id;
    }

    pub fn get_main_id(&self) -> FunctionId {
        self.main_id
    }

    pub fn get_main_mut(&mut self) -> &mut Function<V> {
        self.functions
            .get_mut(&self.main_id)
            .expect("Main function should exist")
    }

    pub fn get_main(&self) -> &Function<V> {
        self.functions
            .get(&self.main_id)
            .expect("Main function should exist")
    }

    pub fn get_function(&self, id: FunctionId) -> &Function<V> {
        self.functions.get(&id).expect("Function should exist")
    }

    pub fn get_function_mut(&mut self, id: FunctionId) -> &mut Function<V> {
        self.functions.get_mut(&id).expect("Function should exist")
    }

    pub fn take_function(&mut self, id: FunctionId) -> Function<V> {
        self.functions.remove(&id).expect("Function should exist")
    }

    pub fn put_function(&mut self, id: FunctionId, function: Function<V>) {
        self.functions.insert(id, function);
    }

    pub fn add_function(&mut self, name: String) -> FunctionId {
        let new_id = FunctionId(self.next_function_id);
        self.next_function_id += 1;
        let function = Function::empty(name);
        self.functions.insert(new_id, function);
        new_id
    }

    pub fn iter_functions(&self) -> impl Iterator<Item = (&FunctionId, &Function<V>)> {
        self.functions.iter()
    }

    pub fn iter_functions_mut(&mut self) -> impl Iterator<Item = (&FunctionId, &mut Function<V>)> {
        self.functions.iter_mut()
    }

    pub fn get_function_ids(&self) -> impl Iterator<Item = FunctionId> {
        self.functions.keys().copied()
    }
}

impl SSA<Empty> {
    pub fn from_noir(noir_ssa: &noirc_evaluator::ssa::ssa_gen::Ssa) -> SSA<Empty> {
        let mut converter = SsaConverter::new();
        converter.convert_noir_ssa(noir_ssa)
    }
}

impl<V: Display + Clone> SSA<V> {
    pub fn to_string(&self, value_annotator: &dyn SsaAnnotator) -> String {
        self.functions
            .iter()
            .sorted_by_key(|(fn_id, _)| fn_id.0)
            .map(|(fn_id, func)| func.to_string(self, *fn_id, value_annotator))
            .join("\n\n")
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Const {
    U(usize, u128),
    Field(ark_bn254::Fr),
}

#[derive(Clone)]
pub struct Function<V> {
    entry_block: BlockId,
    blocks: HashMap<BlockId, Block<V>>,
    name: String,
    returns: Vec<Type<V>>,
    next_block: u64,
    next_value: u64,
    consts: HashMap<ValueId, Const>,
    consts_to_val: HashMap<Const, ValueId>,
}

impl<V: Display + Clone> Function<V> {
    pub fn to_string(
        &self,
        ssa: &SSA<V>,
        id: FunctionId,
        value_annotator: &dyn SsaAnnotator,
    ) -> String {
        let header = format!(
            "fn {}@{}(block {}) -> {} [{}] {{",
            self.name,
            id.0,
            self.entry_block.0,
            self.returns.iter().map(|t| format!("{}", t)).join(", "),
            value_annotator.annotate_function(id)
        );
        let consts = self
            .consts
            .iter()
            .map(|(id, const_)| format!("  v{} = {:?}", id.0, const_))
            .join("\n");
        let blocks = self
            .blocks
            .iter()
            .sorted_by_key(|(bid, _)| bid.0)
            .map(|(bid, block)| block.to_string(ssa, id, *bid, value_annotator))
            .join("\n");
        let footer = "}".to_string();
        format!("{}\n{}\n{}\n{}", header, consts, blocks, footer)
    }
}

impl<V: Clone> Function<V> {
    pub fn empty(name: String) -> Self {
        let entry = Block::empty();
        let entry_id = BlockId(0);
        let mut blocks = HashMap::new();
        blocks.insert(entry_id, entry);
        Function {
            entry_block: BlockId(0),
            blocks,
            name,
            next_block: 1,
            returns: Vec::new(),
            next_value: 0,
            consts: HashMap::new(),
            consts_to_val: HashMap::new(),
        }
    }

    pub fn prepare_rebuild<V2>(self) -> (Function<V2>, HashMap<BlockId, Block<V>>, Vec<Type<V>>) {
        (
            Function {
                entry_block: self.entry_block,
                blocks: HashMap::new(),
                next_block: self.next_block,
                name: self.name,
                returns: vec![],
                next_value: self.next_value,
                consts: self.consts,
                consts_to_val: self.consts_to_val,
            },
            self.blocks,
            self.returns,
        )
    }

    pub fn get_name(&self) -> &str {
        &self.name
    }

    pub fn set_name(&mut self, name: String) {
        self.name = name;
    }

    pub fn get_var_num_bound(&self) -> usize {
        return self.next_value as usize;
    }

    pub fn get_entry_mut(&mut self) -> &mut Block<V> {
        self.blocks
            .get_mut(&self.entry_block)
            .expect("Entry block should exist")
    }

    pub fn get_entry(&self) -> &Block<V> {
        self.blocks
            .get(&self.entry_block)
            .expect("Entry block should exist")
    }

    pub fn get_entry_id(&self) -> BlockId {
        self.entry_block
    }

    pub fn get_block(&self, id: BlockId) -> &Block<V> {
        self.blocks.get(&id).expect("Block should exist")
    }

    pub fn get_block_mut(&mut self, id: BlockId) -> &mut Block<V> {
        self.blocks.get_mut(&id).expect("Block should exist")
    }

    pub fn take_block(&mut self, id: BlockId) -> Block<V> {
        self.blocks.remove(&id).expect("Block should exist")
    }

    pub fn put_block(&mut self, id: BlockId, block: Block<V>) {
        self.blocks.insert(id, block);
    }

    pub fn add_block(&mut self) -> BlockId {
        let new_id = BlockId(self.next_block);
        self.next_block += 1;
        let block = Block::empty();
        self.blocks.insert(new_id, block);
        new_id
    }

    pub fn add_return_type(&mut self, typ: Type<V>) {
        self.returns.push(typ);
    }

    pub fn get_param_types(&self) -> Vec<Type<V>> {
        self.get_entry()
            .parameters
            .iter()
            .map(|(_, typ)| typ.clone())
            .collect()
    }

    pub fn iter_consts(&self) -> impl Iterator<Item = (&ValueId, &Const)> {
        self.consts.iter()
    }

    pub fn get_returns(&self) -> &[Type<V>] {
        &self.returns
    }

    pub fn get_blocks(&self) -> impl Iterator<Item = (&BlockId, &Block<V>)> {
        self.blocks.iter()
    }

    pub fn add_parameter(&mut self, block_id: BlockId, typ: Type<V>) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .parameters
            .push((value_id, typ));
        value_id
    }

    fn push_const(&mut self, value: Const) -> ValueId {
        if let Some(existing_id) = self.consts_to_val.get(&value) {
            return *existing_id;
        }
        let value_id: ValueId = ValueId(self.next_value);
        self.next_value += 1;
        self.consts.insert(value_id, value.clone());
        self.consts_to_val.insert(value.clone(), value_id);
        value_id
    }

    pub fn push_u_const(&mut self, size: usize, value: u128) -> ValueId {
        self.push_const(Const::U(size, value))
    }

    pub fn push_field_const(&mut self, value: ark_bn254::Fr) -> ValueId {
        self.push_const(Const::Field(value))
    }
    pub fn push_eq(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Cmp(CmpKind::Eq, value_id, lhs, rhs));
        value_id
    }
    pub fn push_add(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::BinaryArithOp(
                BinaryArithOpKind::Add,
                value_id,
                lhs,
                rhs,
            ));
        value_id
    }
    pub fn push_mul(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::BinaryArithOp(
                BinaryArithOpKind::Mul,
                value_id,
                lhs,
                rhs,
            ));
        value_id
    }

    pub fn push_div(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::BinaryArithOp(
                BinaryArithOpKind::Div,
                value_id,
                lhs,
                rhs,
            ));
        value_id
    }
    pub fn push_sub(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::BinaryArithOp(
                BinaryArithOpKind::Sub,
                value_id,
                lhs,
                rhs,
            ));
        value_id
    }
    pub fn push_lt(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Cmp(CmpKind::Lt, value_id, lhs, rhs));
        value_id
    }
    pub fn push_alloc(&mut self, block_id: BlockId, typ: Type<V>, annotation: V) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Alloc(value_id, typ, annotation));
        value_id
    }
    pub fn push_store(&mut self, block_id: BlockId, ptr: ValueId, value: ValueId) {
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Store(ptr, value));
    }
    pub fn push_load(&mut self, block_id: BlockId, ptr: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Load(value_id, ptr));
        value_id
    }
    pub fn push_assert_eq(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) {
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::AssertEq(lhs, rhs));
    }

    pub fn push_and(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::BinaryArithOp(
                BinaryArithOpKind::And,
                value_id,
                lhs,
                rhs,
            ));
        value_id
    }

    pub fn push_select(
        &mut self,
        block_id: BlockId,
        cond: ValueId,
        then: ValueId,
        otherwise: ValueId,
    ) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Select(value_id, cond, then, otherwise));
        value_id
    }

    pub fn push_call(
        &mut self,
        block_id: BlockId,
        fn_id: FunctionId,
        args: Vec<ValueId>,
        return_size: usize,
    ) -> Vec<ValueId> {
        let mut return_values = Vec::new();
        for _ in 0..return_size {
            let value_id = ValueId(self.next_value);
            self.next_value += 1;
            return_values.push(value_id);
        }
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Call(return_values.clone(), fn_id, args));
        return_values
    }

    pub fn push_array_get(&mut self, block_id: BlockId, array: ValueId, index: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::ArrayGet(value_id, array, index));
        value_id
    }

    pub fn push_array_set(
        &mut self,
        block_id: BlockId,
        array: ValueId,
        index: ValueId,
        element: ValueId,
    ) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::ArraySet(value_id, array, index, element));
        value_id
    }

    pub fn push_mk_array(
        &mut self,
        block_id: BlockId,
        elements: Vec<ValueId>,
        stp: SeqType,
        typ: Type<V>,
    ) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::MkSeq(value_id, elements, stp, typ));
        value_id
    }

    pub fn push_cast(&mut self, block_id: BlockId, value: ValueId, target: CastTarget) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Cast(value_id, value, target));
        value_id
    }

    pub fn push_truncate(
        &mut self,
        block_id: BlockId,
        value: ValueId,
        out_bit_size: usize,
        in_bit_size: usize,
    ) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Truncate(value_id, value, out_bit_size, in_bit_size));
        value_id
    }

    pub fn push_not(&mut self, block_id: BlockId, value: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Not(value_id, value));
        value_id
    }

    pub fn push_to_bits(
        &mut self,
        block_id: BlockId,
        value: ValueId,
        endianness: Endianness,
        output_size: usize,
    ) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::ToBits(value_id, value, endianness, output_size));
        value_id
    }

    pub fn push_mem_op(&mut self, block_id: BlockId, value: ValueId, kind: MemOp) {
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::MemOp(kind, value));
    }

    // pub fn push_constrain(&mut self, block_id: BlockId, a: ValueId, b: ValueId, c: ValueId) {
    //     self.blocks
    //         .get_mut(&block_id)
    //         .unwrap()
    //         .instructions
    //         .push(OpCode::Constrain(a, b, c));
    // }

    // pub fn push_witness_write(&mut self, block_id: BlockId, value: ValueId) -> ValueId {
    //     let value_id = ValueId(self.next_value);
    //     self.next_value += 1;
    //     self.blocks
    //         .get_mut(&block_id)
    //         .unwrap()
    //         .instructions
    //         .push(OpCode::WriteWitness(value_id, value));
    //     value_id
    // }

    pub fn terminate_block_with_jmp_if(
        &mut self,
        block_id: BlockId,
        condition: ValueId,
        then_destination: BlockId,
        else_destination: BlockId,
    ) {
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .set_terminator(Terminator::JmpIf(
                condition,
                then_destination,
                else_destination,
            ));
    }

    pub fn terminate_block_with_return(&mut self, block_id: BlockId, return_values: Vec<ValueId>) {
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .set_terminator(Terminator::Return(return_values));
    }

    pub fn terminate_block_with_jmp(
        &mut self,
        block_id: BlockId,
        destination: BlockId,
        arguments: Vec<ValueId>,
    ) {
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .set_terminator(Terminator::Jmp(destination, arguments));
    }

    pub fn get_blocks_mut(&mut self) -> impl Iterator<Item = (&BlockId, &mut Block<V>)> {
        self.blocks.iter_mut()
    }

    pub fn take_blocks(&mut self) -> HashMap<BlockId, Block<V>> {
        std::mem::take(&mut self.blocks)
    }

    pub fn put_blocks(&mut self, blocks: HashMap<BlockId, Block<V>>) {
        self.blocks = blocks;
    }

    pub fn fresh_value(&mut self) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        value_id
    }

    pub fn remove_const(&mut self, value_id: ValueId) {
        let v = self.consts.remove(&value_id);
        self.consts_to_val.remove(&v.unwrap());
    }

    pub fn take_returns(&mut self) -> Vec<Type<V>> {
        std::mem::take(&mut self.returns)
    }

    pub fn code_size(&self) -> usize {
        self.blocks
            .values()
            .map(|b| {
                b.instructions
                    .iter()
                    .map(|i| i.get_inputs().count() + 1)
                    .sum::<usize>()
            })
            .sum()
    }
}

#[derive(Clone)]
pub struct Block<V> {
    parameters: Vec<(ValueId, Type<V>)>,
    instructions: Vec<OpCode<V>>,
    terminator: Option<Terminator>,
}

impl<V: Display + Clone> Block<V> {
    pub fn to_string(
        &self,
        ssa: &SSA<V>,
        func_id: FunctionId,
        id: BlockId,
        value_annotator: &dyn SsaAnnotator,
    ) -> String {
        let params = self
            .parameters
            .iter()
            .map(|v| {
                let annotation = value_annotator.annotate_value(func_id, v.0);
                let annotation = if annotation.is_empty() {
                    "".to_string()
                } else {
                    format!(" [{}]", annotation)
                };
                format!("v{} : {}{}", v.0.0, v.1.to_string(), annotation)
            })
            .join(", ");
        let local_annotator = LocalFunctionAnnotator::new(func_id, value_annotator);
        let instructions = self
            .instructions
            .iter()
            .map(|i| format!("    {}", i.to_string(ssa, &local_annotator)))
            .join("\n");
        let terminator = match &self.terminator {
            Some(t) => format!("    {}", t.to_string()),
            None => "".to_string(),
        };
        let block_annotation = value_annotator.annotate_block(func_id, id);
        let block_annotation = if block_annotation.is_empty() {
            "".to_string()
        } else {
            format!(" [{}]", block_annotation)
        };
        format!(
            "  block_{}({}){} {{\n{}\n{}\n  }}",
            id.0, params, block_annotation, instructions, terminator
        )
    }
}

impl<V> Block<V> {
    pub fn empty() -> Self {
        Block {
            parameters: Vec::new(),
            instructions: Vec::new(),
            terminator: None,
        }
    }

    pub fn take_instructions(&mut self) -> Vec<OpCode<V>> {
        std::mem::take(&mut self.instructions)
    }

    pub fn put_instructions(&mut self, instructions: Vec<OpCode<V>>) {
        self.instructions = instructions;
    }

    pub fn push_instruction(&mut self, instruction: OpCode<V>) {
        self.instructions.push(instruction);
    }

    pub fn set_terminator(&mut self, terminator: Terminator) {
        self.terminator = Some(terminator);
    }

    pub fn get_parameters(&self) -> impl Iterator<Item = &(ValueId, Type<V>)> {
        self.parameters.iter()
    }

    pub fn take_parameters(&mut self) -> Vec<(ValueId, Type<V>)> {
        std::mem::take(&mut self.parameters)
    }

    pub fn put_parameters(&mut self, parameters: Vec<(ValueId, Type<V>)>) {
        self.parameters = parameters;
    }

    pub fn get_parameter_values(&self) -> impl Iterator<Item = &ValueId> {
        self.parameters.iter().map(|(id, _)| id)
    }

    pub fn get_instruction(&self, i: usize) -> &OpCode<V> {
        &self.instructions[i]
    }

    pub fn get_instructions(&self) -> impl DoubleEndedIterator<Item = &OpCode<V>> {
        self.instructions.iter()
    }

    pub fn get_instructions_mut(&mut self) -> impl Iterator<Item = &mut OpCode<V>> {
        self.instructions.iter_mut()
    }

    pub fn get_terminator(&self) -> Option<&Terminator> {
        self.terminator.as_ref()
    }

    pub fn get_terminator_mut(&mut self) -> &mut Terminator {
        self.terminator.as_mut().unwrap()
    }

    pub fn take_terminator(&mut self) -> Option<Terminator> {
        std::mem::take(&mut self.terminator)
    }

    pub fn has_parameters(&self) -> bool {
        self.parameters.len() > 0
    }
}

#[derive(Debug, Clone, Copy)]
pub enum BinaryArithOpKind {
    Add,
    Mul,
    Div,
    Sub,
    And,
}

#[derive(Debug, Clone, Copy)]
pub enum CmpKind {
    Lt,
    Eq,
}

#[derive(Debug, Clone, Copy)]
pub enum SeqType {
    Array(usize),
    Slice,
}

#[derive(Debug, Clone, Copy)]
pub enum CastTarget {
    Field,
    U(usize),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Endianness {
    Big,
    Little,
}

impl Display for CastTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CastTarget::Field => write!(f, "Field"),
            CastTarget::U(size) => write!(f, "u{}", size),
        }
    }
}

impl Display for Endianness {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Endianness::Big => write!(f, "big"),
            Endianness::Little => write!(f, "little"),
        }
    }
}

impl Display for SeqType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SeqType::Array(len) => write!(f, "Array[{}]", len),
            SeqType::Slice => write!(f, "Slice"),
        }
    }
}

impl SeqType {
    pub fn of<V: CommutativeMonoid>(&self, t: Type<V>) -> Type<V> {
        match self {
            SeqType::Array(len) => Type::array_of(t, *len, V::empty()),
            SeqType::Slice => Type::slice_of(t, V::empty()),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum MemOp {
    Bump(usize),
    Drop,
}

#[derive(Debug, Clone)]
pub enum OpCode<V> {
    Cmp(CmpKind, ValueId, ValueId, ValueId), // _1 = _2 `cmp` _3
    BinaryArithOp(BinaryArithOpKind, ValueId, ValueId, ValueId), // _1 = _2 `op` _3
    Cast(ValueId, ValueId, CastTarget),      // _1 = cast _2 to _3
    Truncate(ValueId, ValueId, usize, usize), // _1 = truncate _2 from _4 bits to _3 bits
    Not(ValueId, ValueId),                   // _1 = ~_2 (bitwise negation)
    MkSeq(ValueId, Vec<ValueId>, SeqType, Type<V>), // _1 = [_2, _3, ...]: seqType<type>
    Alloc(ValueId, Type<V>, V),              // _1 = alloc(Type)
    Store(ValueId, ValueId),                 // *_1 = _2
    Load(ValueId, ValueId),                  // _1 = *_2
    AssertEq(ValueId, ValueId),              // assert _1 == _2
    AssertR1C(ValueId, ValueId, ValueId),    // assert _1 * _2 - _3 == 0
    Call(Vec<ValueId>, FunctionId, Vec<ValueId>), // _1, ... = call function(_2, _3, ...)
    ArrayGet(ValueId, ValueId, ValueId),     // _1 = _2[_3]
    ArraySet(ValueId, ValueId, ValueId, ValueId), // _1 = _2[_3] = _4
    Select(ValueId, ValueId, ValueId, ValueId), // _1 = _2 ? _3 : _4
    ToBits(ValueId, ValueId, Endianness, usize), // _1 = to_bits _2 (endianness, output_size)
    MemOp(MemOp, ValueId),                       // mem_op(kind, _2)

    // Phase 2
    WriteWitness(Option<ValueId>, ValueId, V), // _1 = as_witness(_2)
    Constrain(ValueId, ValueId, ValueId),      // assert(_1 * _2 - _3 == 0)
}

impl<V: Display + Clone> OpCode<V> {
    fn to_string(&self, ssa: &SSA<V>, value_annotator: &LocalFunctionAnnotator) -> String {
        fn annotate(value_annotator: &LocalFunctionAnnotator, value: ValueId) -> String {
            let annotation = value_annotator.annotate_value(value);
            if annotation.is_empty() {
                "".to_string()
            } else {
                format!("[{}]", annotation)
            }
        }
        match self {
            OpCode::Cmp(kind, result, lhs, rhs) => {
                let op_str = match kind {
                    CmpKind::Lt => "<",
                    CmpKind::Eq => "==",
                };
                format!(
                    "v{}{} = v{} {} v{}",
                    result.0,
                    annotate(value_annotator, *result),
                    lhs.0,
                    op_str,
                    rhs.0
                )
            }
            OpCode::BinaryArithOp(kind, result, lhs, rhs) => {
                let op_str = match kind {
                    BinaryArithOpKind::Add => "+",
                    BinaryArithOpKind::Sub => "-",
                    BinaryArithOpKind::Mul => "*",
                    BinaryArithOpKind::Div => "/",
                    BinaryArithOpKind::And => "&",
                };
                format!(
                    "v{}{} = v{} {} v{}",
                    result.0,
                    annotate(value_annotator, *result),
                    lhs.0,
                    op_str,
                    rhs.0
                )
            }
            OpCode::Alloc(result, typ, annotation) => format!(
                "v{}{} = alloc({} as {})",
                result.0,
                annotate(value_annotator, *result),
                typ,
                annotation
            ),
            OpCode::Store(ptr, value) => format!(
                "*v{}{} = v{}",
                ptr.0,
                annotate(value_annotator, *ptr),
                value.0
            ),
            OpCode::Load(result, ptr) => {
                format!(
                    "v{}{} = *v{}",
                    result.0,
                    annotate(value_annotator, *result),
                    ptr.0
                )
            }
            OpCode::AssertEq(lhs, rhs) => format!("assert v{} == v{}", lhs.0, rhs.0),
            OpCode::AssertR1C(lhs, rhs, cond) => {
                format!("assert v{} * v{} - v{} == 0", lhs.0, rhs.0, cond.0)
            }
            OpCode::Call(result, fn_id, args) => {
                let args_str = args.iter().map(|v| format!("v{}", v.0)).join(", ");
                let result_str = result
                    .iter()
                    .map(|v| format!("v{}{}", v.0, annotate(value_annotator, *v)))
                    .join(", ");
                format!(
                    "{} = call {}@{}({})",
                    result_str,
                    ssa.get_function(*fn_id).get_name(),
                    fn_id.0,
                    args_str
                )
            }
            OpCode::ArrayGet(result, array, index) => {
                format!(
                    "v{}{} = v{}[v{}]",
                    result.0,
                    annotate(value_annotator, *result),
                    array.0,
                    index.0
                )
            }
            OpCode::ArraySet(result, array, index, element) => {
                format!(
                    "v{}{} = (v{}[v{}] = v{})",
                    result.0,
                    annotate(value_annotator, *result),
                    array.0,
                    index.0,
                    element.0
                )
            }
            OpCode::Select(result, cond, then, otherwise) => {
                format!(
                    "v{}{} = v{} ? v{} : v{}",
                    result.0,
                    annotate(value_annotator, *result),
                    cond.0,
                    then.0,
                    otherwise.0
                )
            }
            OpCode::WriteWitness(result, value, _annotation) => {
                let r_str = if let Some(result) = result {
                    format!("v{}{} = ", result.0, annotate(value_annotator, *result))
                } else {
                    "".to_string()
                };
                format!("{}write_witness(v{})", r_str, value.0)
            }
            OpCode::Constrain(a, b, c) => {
                format!("constrain_r1c(v{} * v{} - v{} == 0)", a.0, b.0, c.0)
            }
            OpCode::MkSeq(result, values, seq_type, typ) => {
                let values_str = values.iter().map(|v| format!("v{}", v.0)).join(", ");
                format!(
                    "v{}{} = [{}] : {} of {}",
                    result.0,
                    annotate(value_annotator, *result),
                    values_str,
                    seq_type,
                    typ
                )
            }
            OpCode::Cast(result, value, target) => {
                format!(
                    "v{}{} = cast v{} to {}",
                    result.0,
                    annotate(value_annotator, *result),
                    value.0,
                    target
                )
            }
            OpCode::Truncate(result, value, out_bits, in_bits) => {
                format!(
                    "v{}{} = truncate v{} from {} bits to {} bits",
                    result.0,
                    annotate(value_annotator, *result),
                    value.0,
                    in_bits,
                    out_bits
                )
            }
            OpCode::Not(result, value) => {
                format!(
                    "v{}{} = ~v{}",
                    result.0,
                    annotate(value_annotator, *result),
                    value.0
                )
            }
            OpCode::ToBits(result, value, endianness, output_size) => {
                format!(
                    "v{}{} = to_bits v{} (endianness: {}, size: {})",
                    result.0,
                    annotate(value_annotator, *result),
                    value.0,
                    endianness,
                    output_size
                )
            }
            OpCode::MemOp(kind, value) => {
                let name = match kind {
                    MemOp::Bump(n) => format!("inc_rc[+{}]", n),
                    MemOp::Drop => "drop".to_string(),
                };
                format!("{}(v{})", name, value.0)
            }
        }
    }
}

impl<V> OpCode<V> {
    pub fn get_operands_mut(&mut self) -> impl Iterator<Item = &mut ValueId> {
        match self {
            Self::Alloc(r, _, _) | Self::MemOp(_, r) => vec![r].into_iter(),
            Self::Cmp(_, a, b, c) | Self::BinaryArithOp(_, a, b, c) | Self::ArrayGet(a, b, c) => {
                vec![a, b, c].into_iter()
            }
            Self::Cast(a, b, _) => vec![a, b].into_iter(),
            Self::Truncate(a, b, _, _) => vec![a, b].into_iter(),
            Self::ArraySet(a, b, c, d) => vec![a, b, c, d].into_iter(),
            Self::AssertR1C(a, b, c) | Self::Constrain(a, b, c) => vec![a, b, c].into_iter(),
            Self::Store(a, b) | Self::Load(a, b) | Self::AssertEq(a, b) => vec![a, b].into_iter(),
            Self::WriteWitness(a, b, _) => {
                let mut ret_vec = a.iter_mut().collect::<Vec<_>>();
                ret_vec.push(b);
                ret_vec.into_iter()
            }
            Self::Call(r, _, a) => {
                let mut ret_vec = r.iter_mut().collect::<Vec<_>>();
                let args_vec = a.iter_mut().collect::<Vec<_>>();
                ret_vec.extend(args_vec);
                ret_vec.into_iter()
            }
            Self::MkSeq(r, inputs, _, _) => {
                let mut ret_vec = vec![r];
                ret_vec.extend(inputs);
                ret_vec.into_iter()
            }
            Self::Select(a, b, c, d) => vec![a, b, c, d].into_iter(),
            Self::Not(r, v) => vec![r, v].into_iter(),
            Self::ToBits(r, v, _, _) => vec![r, v].into_iter(),
        }
    }

    pub fn get_inputs_mut(&mut self) -> impl Iterator<Item = &mut ValueId> {
        match self {
            Self::Alloc(_, _, _) => vec![].into_iter(),
            Self::Cmp(_, _, b, c) | Self::BinaryArithOp(_, _, b, c) | Self::ArrayGet(_, b, c) => {
                vec![b, c].into_iter()
            }
            Self::ArraySet(_, b, c, d) => vec![b, c, d].into_iter(),
            Self::AssertEq(b, c) | Self::Store(b, c) => vec![b, c].into_iter(),
            Self::Load(_, c)
            | Self::WriteWitness(_, c, _)
            | Self::Cast(_, c, _)
            | Self::Truncate(_, c, _, _) => vec![c].into_iter(),
            Self::Call(_, _, a) => a.iter_mut().collect::<Vec<_>>().into_iter(),
            Self::MkSeq(_, inputs, _, _) => inputs.iter_mut().collect::<Vec<_>>().into_iter(),
            Self::Select(_, b, c, d) | Self::AssertR1C(b, c, d) | Self::Constrain(b, c, d) => {
                vec![b, c, d].into_iter()
            }
            Self::Not(_, v) => vec![v].into_iter(),
            Self::ToBits(_, v, _, _) | Self::MemOp(_, v) => vec![v].into_iter(),
        }
    }

    pub fn get_inputs(&self) -> impl Iterator<Item = &ValueId> {
        match self {
            Self::Alloc(_, _, _) => vec![].into_iter(),
            Self::Cmp(_, _, b, c) | Self::BinaryArithOp(_, _, b, c) | Self::ArrayGet(_, b, c) => {
                vec![b, c].into_iter()
            }
            Self::ArraySet(_, b, c, d) => vec![b, c, d].into_iter(),
            Self::AssertEq(b, c) | Self::Store(b, c) => vec![b, c].into_iter(),
            Self::Load(_, c)
            | Self::WriteWitness(_, c, _)
            | Self::Cast(_, c, _)
            | Self::Truncate(_, c, _, _) => vec![c].into_iter(),
            Self::Call(_, _, a) => a.iter().collect::<Vec<_>>().into_iter(),
            Self::MkSeq(_, inputs, _, _) => inputs.iter().collect::<Vec<_>>().into_iter(),
            Self::Select(_, b, c, d) | Self::AssertR1C(b, c, d) | Self::Constrain(b, c, d) => {
                vec![b, c, d].into_iter()
            }
            Self::Not(_, v) => vec![v].into_iter(),
            Self::ToBits(_, v, _, _) | Self::MemOp(_, v) => vec![v].into_iter(),
        }
    }

    pub fn get_results(&self) -> impl Iterator<Item = &ValueId> {
        match self {
            Self::Alloc(r, _, _)
            | Self::Cmp(_, r, _, _)
            | Self::BinaryArithOp(_, r, _, _)
            | Self::ArrayGet(r, _, _)
            | Self::ArraySet(r, _, _, _)
            | Self::Load(r, _)
            | Self::MkSeq(r, _, _, _)
            | Self::Select(r, _, _, _)
            | Self::Cast(r, _, _)
            | Self::Truncate(r, _, _, _) => vec![r].into_iter(),
            Self::WriteWitness(r, _, _) => {
                let ret_vec = r.iter().collect::<Vec<_>>();
                ret_vec.into_iter()
            }
            Self::Call(r, _, _) => r.iter().collect::<Vec<_>>().into_iter(),
            Self::Constrain { .. }
            | Self::MemOp(_, _)
            | Self::Store(_, _)
            | Self::AssertEq(_, _)
            | Self::AssertR1C(_, _, _) => vec![].into_iter(),
            Self::Not(r, _) => vec![r].into_iter(),
            Self::ToBits(r, _, _, _) => vec![r].into_iter(),
        }
    }
}
#[derive(Debug, Clone)]
pub enum Terminator {
    Jmp(BlockId, Vec<ValueId>),
    JmpIf(ValueId, BlockId, BlockId),
    Return(Vec<ValueId>),
}

impl Terminator {
    pub fn to_string(&self) -> String {
        match self {
            Terminator::Jmp(block_id, args) => {
                let args_str = args.iter().map(|v| format!("v{}", v.0)).join(", ");
                format!("jmp block_{}({})", block_id.0, args_str)
            }
            Terminator::JmpIf(cond, true_block, false_block) => {
                format!(
                    "jmp_if v{} to block_{}, else to block_{}",
                    cond.0, true_block.0, false_block.0
                )
            }
            Terminator::Return(values) => {
                let values_str = values.iter().map(|v| format!("v{}", v.0)).join(", ");
                format!("return {}", values_str)
            }
        }
    }
}
