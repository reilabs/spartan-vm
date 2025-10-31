use crate::compiler::{
    ir::r#type::{CommutativeMonoid, Empty, Type},
    ssa_gen::SsaConverter,
};
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

#[derive(Clone)]
pub enum GlobalDef {
    Const(Const),
    Array(Vec<usize>, Type<Empty>),
}

#[derive(Clone)]
pub struct SSA<V> {
    functions: HashMap<FunctionId, Function<V>>,
    globals: Vec<GlobalDef>,
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
            globals: Vec::new(),
            main_id,
            next_function_id: 1,
        }
    }

    pub fn prepare_rebuild<V2>(self) -> (SSA<V2>, HashMap<FunctionId, Function<V>>) {
        (
            SSA {
                functions: HashMap::new(),
                globals: self.globals,
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

    pub fn set_globals(&mut self, globals: Vec<GlobalDef>) {
        self.globals = globals;
    }

    pub fn get_globals(&self) -> &[GlobalDef] {
        &self.globals
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
    BoxedField(ark_bn254::Fr),
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

    pub fn iter_consts_mut(&mut self) -> impl Iterator<Item = (&ValueId, &mut Const)> {
        self.consts.iter_mut()
    }

    pub fn iter_returns_mut(&mut self) -> impl Iterator<Item = &mut Type<V>> {
        self.returns.iter_mut()
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
            .push(OpCode::Cmp {
                kind: CmpKind::Eq,
                result: value_id,
                lhs: lhs,
                rhs: rhs,
            });
        value_id
    }
    pub fn push_add(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::BinaryArithOp {
                kind: BinaryArithOpKind::Add,
                result: value_id,
                lhs: lhs,
                rhs: rhs,
            });
        value_id
    }
    pub fn push_mul(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::BinaryArithOp {
                kind: BinaryArithOpKind::Mul,
                result: value_id,
                lhs: lhs,
                rhs: rhs,
            });
        value_id
    }

    pub fn push_div(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::BinaryArithOp {
                kind: BinaryArithOpKind::Div,
                result: value_id,
                lhs: lhs,
                rhs: rhs,
            });
        value_id
    }
    pub fn push_sub(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::BinaryArithOp {
                kind: BinaryArithOpKind::Sub,
                result: value_id,
                lhs: lhs,
                rhs: rhs,
            });
        value_id
    }
    pub fn push_lt(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Cmp {
                kind: CmpKind::Lt,
                result: value_id,
                lhs: lhs,
                rhs: rhs,
            });
        value_id
    }
    pub fn push_alloc(&mut self, block_id: BlockId, typ: Type<V>, annotation: V) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Alloc {
                result: value_id,
                elem_type: typ,
                result_annotation: annotation,
            });
        value_id
    }
    pub fn push_store(&mut self, block_id: BlockId, ptr: ValueId, value: ValueId) {
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Store {
                ptr: ptr,
                value: value,
            });
    }
    pub fn push_load(&mut self, block_id: BlockId, ptr: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Load {
                result: value_id,
                ptr: ptr,
            });
        value_id
    }
    pub fn push_assert_eq(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) {
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::AssertEq { lhs: lhs, rhs: rhs });
    }

    pub fn push_and(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::BinaryArithOp {
                kind: BinaryArithOpKind::And,
                result: value_id,
                lhs: lhs,
                rhs: rhs,
            });
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
            .push(OpCode::Select {
                result: value_id,
                cond: cond,
                if_t: then,
                if_f: otherwise,
            });
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
            .push(OpCode::Call {
                results: return_values.clone(),
                function: fn_id,
                args: args,
            });
        return_values
    }

    pub fn push_array_get(&mut self, block_id: BlockId, array: ValueId, index: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::ArrayGet {
                result: value_id,
                array: array,
                index: index,
            });
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
            .push(OpCode::ArraySet {
                result: value_id,
                array: array,
                index: index,
                value: element,
            });
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
            .push(OpCode::MkSeq {
                result: value_id,
                elems: elements,
                seq_type: stp,
                elem_type: typ,
            });
        value_id
    }

    pub fn push_cast(&mut self, block_id: BlockId, value: ValueId, target: CastTarget) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Cast {
                result: value_id,
                value: value,
                target: target,
            });
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
            .push(OpCode::Truncate {
                result: value_id,
                value: value,
                to_bits: out_bit_size,
                from_bits: in_bit_size,
            });
        value_id
    }

    pub fn push_not(&mut self, block_id: BlockId, value: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Not {
                result: value_id,
                value: value,
            });
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
            .push(OpCode::ToBits {
                result: value_id,
                value: value,
                endianness: endianness,
                count: output_size,
            });
        value_id
    }

    pub fn push_to_radix(
        &mut self,
        block_id: BlockId,
        value: ValueId,
        radix: Radix<ValueId>,
        endianness: Endianness,
        output_size: usize,
    ) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::ToRadix {
                result: value_id,
                value: value,
                radix,
                endianness: endianness,
                count: output_size,
            });
        value_id
    }

    pub fn push_rangecheck(&mut self, block_id: BlockId, value: ValueId, max_bits: usize) {
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Rangecheck {
                value: value,
                max_bits: max_bits,
            });
    }

    pub fn push_mem_op(&mut self, block_id: BlockId, value: ValueId, kind: MemOp) {
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::MemOp {
                kind: kind,
                value: value,
            });
    }

    pub fn push_read_global(&mut self, block_id: BlockId, index: u64, typ: Type<V>) -> ValueId {
        let value = self.fresh_value();
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::ReadGlobal {
                result: value,
                offset: index,
                result_type: typ,
            });
        value
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
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

#[derive(Debug, Clone, Copy)]
pub enum DMatrix {
    A,
    B,
    C,
}

#[derive(Debug, Clone, Copy)]
pub enum LookupTarget<V> {
    Rangecheck(u8),
    DynRangecheck(V),
    Array(V),
}

#[derive(Debug, Clone, Copy)]
pub enum Radix<V> {
    Bytes,
    Dyn(V),
}

#[derive(Debug, Clone)]
pub enum OpCode<V> {
    Cmp {
        kind: CmpKind,
        result: ValueId,
        lhs: ValueId,
        rhs: ValueId,
    },
    BinaryArithOp {
        kind: BinaryArithOpKind,
        result: ValueId,
        lhs: ValueId,
        rhs: ValueId,
    },
    Cast {
        result: ValueId,
        value: ValueId,
        target: CastTarget,
    },
    Truncate {
        result: ValueId,
        value: ValueId,
        to_bits: usize,
        from_bits: usize,
    },
    Not {
        result: ValueId,
        value: ValueId,
    },
    MkSeq {
        result: ValueId,
        elems: Vec<ValueId>,
        seq_type: SeqType,
        elem_type: Type<V>,
    },
    Alloc {
        result: ValueId,
        elem_type: Type<V>,
        result_annotation: V,
    },
    Store {
        ptr: ValueId,
        value: ValueId,
    },
    Load {
        result: ValueId,
        ptr: ValueId,
    },
    AssertEq {
        lhs: ValueId,
        rhs: ValueId,
    },
    AssertR1C {
        a: ValueId,
        b: ValueId,
        c: ValueId,
    },
    Call {
        results: Vec<ValueId>,
        function: FunctionId,
        args: Vec<ValueId>,
    },
    ArrayGet {
        result: ValueId,
        array: ValueId,
        index: ValueId,
    },
    ArraySet {
        result: ValueId,
        array: ValueId,
        index: ValueId,
        value: ValueId,
    },
    Select {
        result: ValueId,
        cond: ValueId,
        if_t: ValueId,
        if_f: ValueId,
    },
    ToBits {
        result: ValueId,
        value: ValueId,
        endianness: Endianness,
        count: usize,
    },
    ToRadix {
        result: ValueId,
        value: ValueId,
        radix: Radix<ValueId>,
        endianness: Endianness,
        count: usize,
    },
    MemOp {
        kind: MemOp,
        value: ValueId,
    },
    WriteWitness {
        result: Option<ValueId>,
        value: ValueId,
        witness_annotation: V,
    }, // TODO: split into two variants, the current structure is weird.
    FreshWitness {
        result: ValueId,
        result_type: Type<V>,
    },
    NextDCoeff {
        result: ValueId,
    },
    BumpD {
        matrix: DMatrix,
        variable: ValueId,
        sensitivity: ValueId,
    },
    Constrain {
        a: ValueId,
        b: ValueId,
        c: ValueId,
    },
    Lookup {
        target: LookupTarget<ValueId>,
        keys: Vec<ValueId>,
        results: Vec<ValueId>,
    },
    DLookup {
        target: LookupTarget<ValueId>,
        keys: Vec<ValueId>,
        results: Vec<ValueId>,
    },
    BoxField {
        result: ValueId,
        value: ValueId,
        result_annotation: V,
    },
    UnboxField {
        result: ValueId,
        value: ValueId,
    },
    MulConst {
        result: ValueId,
        const_val: ValueId,
        var: ValueId,
    },
    Rangecheck {
        value: ValueId,
        max_bits: usize,
    },
    ReadGlobal {
        result: ValueId,
        offset: u64,
        result_type: Type<V>,
    },
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
            OpCode::Cmp {
                kind,
                result,
                lhs,
                rhs,
            } => {
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
            OpCode::BinaryArithOp {
                kind,
                result,
                lhs,
                rhs,
            } => {
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
            OpCode::Alloc {
                result,
                elem_type: typ,
                result_annotation: annotation,
            } => format!(
                "v{}{} = alloc({} as {})",
                result.0,
                annotate(value_annotator, *result),
                typ,
                annotation
            ),
            OpCode::Store { ptr, value } => format!(
                "*v{}{} = v{}",
                ptr.0,
                annotate(value_annotator, *ptr),
                value.0
            ),
            OpCode::Load { result, ptr } => {
                format!(
                    "v{}{} = *v{}",
                    result.0,
                    annotate(value_annotator, *result),
                    ptr.0
                )
            }
            OpCode::AssertEq { lhs, rhs } => format!("assert v{} == v{}", lhs.0, rhs.0),
            OpCode::AssertR1C {
                a: lhs,
                b: rhs,
                c: cond,
            } => {
                format!("assert v{} * v{} - v{} == 0", lhs.0, rhs.0, cond.0)
            }
            OpCode::Call {
                results: result,
                function: fn_id,
                args,
            } => {
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
            OpCode::ArrayGet {
                result,
                array,
                index,
            } => {
                format!(
                    "v{}{} = v{}[v{}]",
                    result.0,
                    annotate(value_annotator, *result),
                    array.0,
                    index.0
                )
            }
            OpCode::ArraySet {
                result,
                array,
                index,
                value: element,
            } => {
                format!(
                    "v{}{} = (v{}[v{}] = v{})",
                    result.0,
                    annotate(value_annotator, *result),
                    array.0,
                    index.0,
                    element.0
                )
            }
            OpCode::Select {
                result,
                cond,
                if_t: then,
                if_f: otherwise,
            } => {
                format!(
                    "v{}{} = v{} ? v{} : v{}",
                    result.0,
                    annotate(value_annotator, *result),
                    cond.0,
                    then.0,
                    otherwise.0
                )
            }
            OpCode::WriteWitness {
                result,
                value,
                witness_annotation: _annotation,
            } => {
                let r_str = if let Some(result) = result {
                    format!("v{}{} = ", result.0, annotate(value_annotator, *result))
                } else {
                    "".to_string()
                };
                format!("{}write_witness(v{})", r_str, value.0)
            }
            OpCode::FreshWitness {
                result,
                result_type: typ,
            } => {
                format!(
                    "v{}{} = fresh_witness(): {}",
                    result.0,
                    annotate(value_annotator, *result),
                    typ
                )
            }
            OpCode::Constrain { a, b, c } => {
                format!("constrain_r1c(v{} * v{} - v{} == 0)", a.0, b.0, c.0)
            }
            OpCode::Lookup {
                target,
                keys,
                results,
            } => {
                let keys_str = keys.iter().map(|v| format!("v{}", v.0)).join(", ");
                let results_str = results.iter().map(|v| format!("v{}", v.0)).join(", ");
                let target_str = match target {
                    LookupTarget::Rangecheck(n) => format!("rngchk({})", n),
                    LookupTarget::DynRangecheck(v) => format!("rngchk(_ < v{})", v.0),
                    LookupTarget::Array(arr) => format!("v{}", arr.0),
                };
                format!(
                    "constrain_lookup({}, ({}) => ({}))",
                    target_str, keys_str, results_str
                )
            }
            OpCode::NextDCoeff { result } => {
                format!(
                    "v{}{} = next_d_coeff()",
                    result.0,
                    annotate(value_annotator, *result)
                )
            }
            OpCode::BumpD {
                matrix,
                variable: result,
                sensitivity: value,
            } => {
                let matrix_str = match matrix {
                    DMatrix::A => "A",
                    DMatrix::B => "B",
                    DMatrix::C => "C",
                };
                format!("∂{} / ∂v{} += v{}", matrix_str, result.0, value.0)
            }
            OpCode::DLookup {
                target,
                keys,
                results,
            } => {
                let keys_str = keys.iter().map(|v| format!("v{}", v.0)).join(", ");
                let results_str = results.iter().map(|v| format!("v{}", v.0)).join(", ");
                let target_str = match target {
                    LookupTarget::Rangecheck(n) => format!("rngchk({})", n),
                    LookupTarget::DynRangecheck(v) => format!("rngchk(_ < v{})", v.0),
                    LookupTarget::Array(arr) => format!("v{}", arr.0),
                };
                format!(
                    "∂lookup({}, ({}) => ({}))",
                    target_str, keys_str, results_str
                )
            }
            OpCode::MkSeq {
                result,
                elems: values,
                seq_type,
                elem_type: typ,
            } => {
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
            OpCode::Cast {
                result,
                value,
                target,
            } => {
                format!(
                    "v{}{} = cast v{} to {}",
                    result.0,
                    annotate(value_annotator, *result),
                    value.0,
                    target
                )
            }
            OpCode::Truncate {
                result,
                value,
                to_bits: out_bits,
                from_bits: in_bits,
            } => {
                format!(
                    "v{}{} = truncate v{} from {} bits to {} bits",
                    result.0,
                    annotate(value_annotator, *result),
                    value.0,
                    in_bits,
                    out_bits
                )
            }
            OpCode::Not { result, value } => {
                format!(
                    "v{}{} = ~v{}",
                    result.0,
                    annotate(value_annotator, *result),
                    value.0
                )
            }
            OpCode::ToBits {
                result,
                value,
                endianness,
                count: output_size,
            } => {
                format!(
                    "v{}{} = to_bits v{} (endianness: {}, size: {})",
                    result.0,
                    annotate(value_annotator, *result),
                    value.0,
                    endianness,
                    output_size
                )
            }
            OpCode::ToRadix {
                result,
                value,
                radix,
                endianness,
                count: output_size,
            } => {
                let radix_str = match radix {
                    Radix::Bytes => "bytes".to_string(),
                    Radix::Dyn(radix) => format!("v{}", radix.0),
                };
                format!(
                    "v{}{} = to_radix v{} {} (endianness: {}, size: {})",
                    result.0,
                    annotate(value_annotator, *result),
                    value.0,
                    radix_str,
                    endianness,
                    output_size
                )
            }
            OpCode::MemOp { kind, value } => {
                let name = match kind {
                    MemOp::Bump(n) => format!("inc_rc[+{}]", n),
                    MemOp::Drop => "drop".to_string(),
                };
                format!("{}(v{})", name, value.0)
            }
            OpCode::BoxField {
                result,
                value,
                result_annotation: annotation,
            } => {
                format!(
                    "v{}{} = box_field(v{}) as {}",
                    result.0,
                    annotate(value_annotator, *result),
                    value.0,
                    annotation
                )
            }
            OpCode::UnboxField { result, value } => {
                format!(
                    "v{}{} = unbox_field(v{})",
                    result.0,
                    annotate(value_annotator, *result),
                    value.0
                )
            }
            OpCode::MulConst {
                result,
                const_val: constant,
                var,
            } => {
                format!(
                    "v{}{} = mul_const(v{}, v{})",
                    result.0,
                    annotate(value_annotator, *result),
                    constant.0,
                    var.0
                )
            }
            OpCode::Rangecheck {
                value: val,
                max_bits,
            } => {
                format!("rangecheck(v{}, {})", val.0, max_bits)
            }
            OpCode::ReadGlobal {
                result,
                offset: index,
                result_type: typ,
            } => {
                format!(
                    "v{}{} = read_global(g{}, {})",
                    result.0,
                    annotate(value_annotator, *result),
                    index,
                    typ
                )
            }
        }
    }
}

impl<V> OpCode<V> {
    pub fn get_operands_mut(&mut self) -> impl Iterator<Item = &mut ValueId> {
        match self {
            Self::Alloc {
                result: r,
                elem_type: _,
                result_annotation: _,
            }
            | Self::MemOp { kind: _, value: r }
            | Self::FreshWitness {
                result: r,
                result_type: _,
            }
            | Self::NextDCoeff { result: r } => vec![r].into_iter(),
            Self::Cmp {
                kind: _,
                result: a,
                lhs: b,
                rhs: c,
            }
            | Self::BinaryArithOp {
                kind: _,
                result: a,
                lhs: b,
                rhs: c,
            }
            | Self::ArrayGet {
                result: a,
                array: b,
                index: c,
            }
            | Self::MulConst {
                result: a,
                const_val: b,
                var: c,
            } => vec![a, b, c].into_iter(),
            Self::Cast {
                result: a,
                value: b,
                target: _,
            }
            | Self::BoxField {
                result: a,
                value: b,
                result_annotation: _,
            }
            | Self::UnboxField {
                result: a,
                value: b,
            } => vec![a, b].into_iter(),
            Self::Truncate {
                result: a,
                value: b,
                to_bits: _,
                from_bits: _,
            } => vec![a, b].into_iter(),
            Self::ArraySet {
                result: a,
                array: b,
                index: c,
                value: d,
            } => vec![a, b, c, d].into_iter(),
            Self::AssertR1C { a, b, c } | Self::Constrain { a, b, c } => vec![a, b, c].into_iter(),
            Self::Store { ptr: a, value: b }
            | Self::Load { result: a, ptr: b }
            | Self::AssertEq { lhs: a, rhs: b }
            | Self::BumpD {
                matrix: _,
                variable: a,
                sensitivity: b,
            } => vec![a, b].into_iter(),
            Self::WriteWitness {
                result: a,
                value: b,
                witness_annotation: _,
            } => {
                let mut ret_vec = a.iter_mut().collect::<Vec<_>>();
                ret_vec.push(b);
                ret_vec.into_iter()
            }
            Self::Call {
                results: r,
                function: _,
                args: a,
            } => {
                let mut ret_vec = r.iter_mut().collect::<Vec<_>>();
                let args_vec = a.iter_mut().collect::<Vec<_>>();
                ret_vec.extend(args_vec);
                ret_vec.into_iter()
            }
            Self::Lookup {
                target,
                keys,
                results,
            }
            | Self::DLookup {
                target,
                keys,
                results,
            } => {
                let mut ret_vec = vec![];
                match target {
                    LookupTarget::Rangecheck(_) => {}
                    LookupTarget::DynRangecheck(v) => {
                        ret_vec.push(v);
                    }
                    LookupTarget::Array(arr) => {
                        ret_vec.push(arr);
                    }
                }
                ret_vec.extend(keys);
                ret_vec.extend(results);
                ret_vec.into_iter()
            }
            Self::MkSeq {
                result: r,
                elems: inputs,
                seq_type: _,
                elem_type: _,
            } => {
                let mut ret_vec = vec![r];
                ret_vec.extend(inputs);
                ret_vec.into_iter()
            }
            Self::Select {
                result: a,
                cond: b,
                if_t: c,
                if_f: d,
            } => vec![a, b, c, d].into_iter(),
            Self::Not {
                result: r,
                value: v,
            } => vec![r, v].into_iter(),
            Self::ToBits {
                result: r,
                value: v,
                endianness: _,
                count: _,
            } => vec![r, v].into_iter(),
            Self::ToRadix {
                result: r,
                value: v,
                radix,
                endianness: _,
                count: _,
            } => {
                let mut ret_vec = vec![r, v];
                match radix {
                    Radix::Bytes => {}
                    Radix::Dyn(radix) => {
                        ret_vec.push(radix);
                    }
                }
                ret_vec.into_iter()
            }
            Self::Rangecheck {
                value: val,
                max_bits: _,
            } => vec![val].into_iter(),
            Self::ReadGlobal {
                result: r,
                offset: _,
                result_type: _,
            } => vec![r].into_iter(),
        }
    }

    pub fn get_inputs_mut(&mut self) -> impl Iterator<Item = &mut ValueId> {
        match self {
            Self::Alloc {
                result: _,
                elem_type: _,
                result_annotation: _,
            }
            | Self::FreshWitness {
                result: _,
                result_type: _,
            }
            | Self::NextDCoeff { result: _ } => vec![].into_iter(),
            Self::Cmp {
                kind: _,
                result: _,
                lhs: b,
                rhs: c,
            }
            | Self::BinaryArithOp {
                kind: _,
                result: _,
                lhs: b,
                rhs: c,
            }
            | Self::ArrayGet {
                result: _,
                array: b,
                index: c,
            }
            | Self::MulConst {
                result: _,
                const_val: b,
                var: c,
            } => vec![b, c].into_iter(),
            Self::ArraySet {
                result: _,
                array: b,
                index: c,
                value: d,
            } => vec![b, c, d].into_iter(),
            Self::AssertEq { lhs: b, rhs: c }
            | Self::Store { ptr: b, value: c }
            | Self::BumpD {
                matrix: _,
                variable: b,
                sensitivity: c,
            } => vec![b, c].into_iter(),
            Self::Load { result: _, ptr: c }
            | Self::WriteWitness {
                result: _,
                value: c,
                witness_annotation: _,
            }
            | Self::Cast {
                result: _,
                value: c,
                target: _,
            }
            | Self::BoxField {
                result: _,
                value: c,
                result_annotation: _,
            }
            | Self::UnboxField {
                result: _,
                value: c,
            }
            | Self::Truncate {
                result: _,
                value: c,
                to_bits: _,
                from_bits: _,
            } => vec![c].into_iter(),
            Self::Call {
                results: _,
                function: _,
                args: a,
            } => a.iter_mut().collect::<Vec<_>>().into_iter(),
            Self::MkSeq {
                result: _,
                elems: inputs,
                seq_type: _,
                elem_type: _,
            } => inputs.iter_mut().collect::<Vec<_>>().into_iter(),
            Self::Select {
                result: _,
                cond: b,
                if_t: c,
                if_f: d,
            }
            | Self::AssertR1C { a: b, b: c, c: d }
            | Self::Constrain { a: b, b: c, c: d } => vec![b, c, d].into_iter(),
            Self::Not {
                result: _,
                value: v,
            } => vec![v].into_iter(),
            Self::ToBits {
                result: _,
                value: v,
                endianness: _,
                count: _,
            } => vec![v].into_iter(),
            Self::ToRadix {
                result: _,
                value: v,
                radix,
                endianness: _,
                count: _,
            } => {
                let mut ret_vec = vec![v];
                match radix {
                    Radix::Bytes => {}
                    Radix::Dyn(radix) => {
                        ret_vec.push(radix);
                    }
                }
                ret_vec.into_iter()
            }
            Self::MemOp { kind: _, value: v } => vec![v].into_iter(),
            Self::Rangecheck {
                value: val,
                max_bits: _,
            } => vec![val].into_iter(),
            Self::ReadGlobal {
                result: _,
                offset: _,
                result_type: _,
            } => vec![].into_iter(),
            Self::Lookup {
                target,
                keys,
                results,
            }
            | Self::DLookup {
                target,
                keys,
                results,
            } => {
                let mut ret_vec = vec![];
                match target {
                    LookupTarget::Rangecheck(_) => {}
                    LookupTarget::DynRangecheck(v) => {
                        ret_vec.push(v);
                    }
                    LookupTarget::Array(arr) => {
                        ret_vec.push(arr);
                    }
                }
                ret_vec.extend(keys);
                ret_vec.extend(results);
                ret_vec.into_iter()
            }
        }
    }

    pub fn get_inputs(&self) -> impl Iterator<Item = &ValueId> {
        match self {
            Self::Alloc {
                result: _,
                elem_type: _,
                result_annotation: _,
            }
            | Self::FreshWitness {
                result: _,
                result_type: _,
            }
            | Self::NextDCoeff { result: _ } => vec![].into_iter(),
            Self::Cmp {
                kind: _,
                result: _,
                lhs: b,
                rhs: c,
            }
            | Self::BinaryArithOp {
                kind: _,
                result: _,
                lhs: b,
                rhs: c,
            }
            | Self::ArrayGet {
                result: _,
                array: b,
                index: c,
            } => vec![b, c].into_iter(),
            Self::ArraySet {
                result: _,
                array: b,
                index: c,
                value: d,
            } => vec![b, c, d].into_iter(),
            Self::AssertEq { lhs: b, rhs: c }
            | Self::Store { ptr: b, value: c }
            | Self::BumpD {
                matrix: _,
                variable: b,
                sensitivity: c,
            }
            | Self::MulConst {
                result: _,
                const_val: b,
                var: c,
            } => vec![b, c].into_iter(),
            Self::Load { result: _, ptr: c }
            | Self::WriteWitness {
                result: _,
                value: c,
                witness_annotation: _,
            }
            | Self::Cast {
                result: _,
                value: c,
                target: _,
            }
            | Self::BoxField {
                result: _,
                value: c,
                result_annotation: _,
            }
            | Self::UnboxField {
                result: _,
                value: c,
            }
            | Self::Truncate {
                result: _,
                value: c,
                to_bits: _,
                from_bits: _,
            } => vec![c].into_iter(),
            Self::Call {
                results: _,
                function: _,
                args: a,
            } => a.iter().collect::<Vec<_>>().into_iter(),
            Self::MkSeq {
                result: _,
                elems: inputs,
                seq_type: _,
                elem_type: _,
            } => inputs.iter().collect::<Vec<_>>().into_iter(),
            Self::Select {
                result: _,
                cond: b,
                if_t: c,
                if_f: d,
            }
            | Self::AssertR1C { a: b, b: c, c: d }
            | Self::Constrain { a: b, b: c, c: d } => vec![b, c, d].into_iter(),
            Self::Not {
                result: _,
                value: v,
            } => vec![v].into_iter(),
            Self::ToBits {
                result: _,
                value: v,
                endianness: _,
                count: _,
            } => vec![v].into_iter(),
            Self::ToRadix {
                result: _,
                value: v,
                radix,
                endianness: _,
                count: _,
            } => {
                let mut ret_vec = vec![v];
                match radix {
                    Radix::Bytes => {}
                    Radix::Dyn(radix) => {
                        ret_vec.push(radix);
                    }
                }
                ret_vec.into_iter()
            }
            Self::MemOp { kind: _, value: v } => vec![v].into_iter(),
            Self::Rangecheck {
                value: val,
                max_bits: _,
            } => vec![val].into_iter(),
            Self::ReadGlobal {
                result: _,
                offset: _,
                result_type: _,
            } => vec![].into_iter(),
            Self::Lookup {
                target,
                keys,
                results,
            }
            | Self::DLookup {
                target,
                keys,
                results,
            } => {
                let mut ret_vec = vec![];
                match target {
                    LookupTarget::Rangecheck(_) => {}
                    LookupTarget::DynRangecheck(v) => {
                        ret_vec.push(v);
                    }
                    LookupTarget::Array(arr) => {
                        ret_vec.push(arr);
                    }
                }
                ret_vec.extend(keys);
                ret_vec.extend(results);
                ret_vec.into_iter()
            }
        }
    }

    pub fn get_results(&self) -> impl Iterator<Item = &ValueId> {
        match self {
            Self::Alloc {
                result: r,
                elem_type: _,
                result_annotation: _,
            }
            | Self::FreshWitness {
                result: r,
                result_type: _,
            }
            | Self::Cmp {
                kind: _,
                result: r,
                lhs: _,
                rhs: _,
            }
            | Self::BinaryArithOp {
                kind: _,
                result: r,
                lhs: _,
                rhs: _,
            }
            | Self::ArrayGet {
                result: r,
                array: _,
                index: _,
            }
            | Self::ArraySet {
                result: r,
                array: _,
                index: _,
                value: _,
            }
            | Self::Load { result: r, ptr: _ }
            | Self::MkSeq {
                result: r,
                elems: _,
                seq_type: _,
                elem_type: _,
            }
            | Self::Select {
                result: r,
                cond: _,
                if_t: _,
                if_f: _,
            }
            | Self::Cast {
                result: r,
                value: _,
                target: _,
            }
            | Self::Truncate {
                result: r,
                value: _,
                to_bits: _,
                from_bits: _,
            }
            | Self::MulConst {
                result: r,
                const_val: _,
                var: _,
            }
            | Self::BoxField {
                result: r,
                value: _,
                result_annotation: _,
            }
            | Self::UnboxField {
                result: r,
                value: _,
            }
            | Self::NextDCoeff { result: r } => vec![r].into_iter(),
            Self::WriteWitness {
                result: r,
                value: _,
                witness_annotation: _,
            } => {
                let ret_vec = r.iter().collect::<Vec<_>>();
                ret_vec.into_iter()
            }
            Self::Call {
                results: r,
                function: _,
                args: _,
            } => r.iter().collect::<Vec<_>>().into_iter(),
            Self::Constrain { .. }
            | Self::BumpD {
                matrix: _,
                variable: _,
                sensitivity: _,
            }
            | Self::MemOp { kind: _, value: _ }
            | Self::Store { ptr: _, value: _ }
            | Self::AssertEq { lhs: _, rhs: _ }
            | Self::AssertR1C { a: _, b: _, c: _ }
            | Self::Rangecheck {
                value: _,
                max_bits: _,
            } => vec![].into_iter(),
            Self::Not {
                result: r,
                value: _,
            } => vec![r].into_iter(),
            Self::ToBits {
                result: r,
                value: _,
                endianness: _,
                count: _,
            } => vec![r].into_iter(),
            Self::ToRadix {
                result: r,
                value: _,
                radix: _,
                endianness: _,
                count: _,
            } => vec![r].into_iter(),
            Self::ReadGlobal {
                result: r,
                offset: _,
                result_type: _,
            } => vec![r].into_iter(),
            Self::Lookup { .. } | Self::DLookup { .. } => vec![].into_iter(),
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
