use crate::compiler::ssa_gen::SsaConverter;
use itertools::Itertools;
use core::panic;
use std::{collections::HashMap, rc::Rc};

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct ValueId(pub u64);
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct BlockId(pub u64);
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct FunctionId(pub u64);

pub trait SsaAnnotator {
    fn annotate_value(&self, function_id: FunctionId, value_id: ValueId) -> String {
        "".to_string()
    }
    fn annotate_function(&self, function_id: FunctionId) -> String {
        "".to_string()
    }
    fn annotate_block(&self, function_id: FunctionId, block_id: BlockId) -> String {
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Type {
    Bool,
    Field,
    U32,
    Array(Box<Type>, usize),
    Ref(Box<Type>),
}

impl Type {
    pub fn bool() -> Self {
        Type::Bool
    }

    pub fn field() -> Self {
        Type::Field
    }

    pub fn u32() -> Self {
        Type::U32
    }

    pub fn array_of(self, size: usize) -> Self {
        Type::Array(Box::new(self), size)
    }

    pub fn ref_of(self) -> Self {
        Type::Ref(Box::new(self))
    }

    pub fn to_string(&self) -> String {
        match self {
            Type::Bool => "bool".to_string(),
            Type::Field => "Field".to_string(),
            Type::U32 => "u32".to_string(),
            Type::Array(typ, size) => format!("Array<{}, {}>", typ.to_string(), size),
            Type::Ref(typ) => format!("Ref<{}>", typ.to_string()),
        }
    }

    pub fn is_compatible(&self, other: &Type) -> bool {
        self == other || (self.is_numeric() && other.is_numeric())
    }

    pub fn is_numeric(&self) -> bool {
        matches!(self, Type::U32 | Type::Field | Type::Bool)
    }

    pub fn is_ref_of(&self, other: &Type) -> bool {
        matches!(self, Type::Ref(inner) if inner.as_ref() == other)
    }

    pub fn get_arithmetic_result_type(&self, other: &Type) -> Type {
        match (self, other) {
            (Type::Field, _) | (_, Type::Field) => Type::Field,
            (Type::U32, _) | (_, Type::U32) => Type::U32,
            (Type::Bool, _) | (_, Type::Bool) => Type::Bool,
            _ => panic!("Cannot perform arithmetic on types {:?} and {:?}", self, other),
        }
    }

    pub fn is_array(&self) -> bool {
        matches!(self, Type::Array(_, _))
    }

    pub fn get_refered(&self) -> Type {
        match self {
            Type::Ref(inner) => *inner.clone(),
            _ => panic!("Type is not a reference"),
        }
    }

    pub fn get_array_element(&self) -> Type {
        match self {
            Type::Array(inner, _) => *inner.clone(),
            _ => panic!("Type is not an array"),
        }
    }

    pub fn is_u32(&self) -> bool {
        matches!(self, Type::U32)
    }

    pub fn has_eq(&self) -> bool {
        matches!(self, Type::Field | Type::U32 | Type::Bool)
    }

    pub fn is_ref(&self) -> bool {
        matches!(self, Type::Ref(_))
    }

    pub fn get_pointed(&self) -> Type {
        match self {
            Type::Ref(inner) => *inner.clone(),
            _ => panic!("Type is not a reference"),
        }
    }
}

pub struct SSA {
    functions: HashMap<FunctionId, Function>,
    main_id: FunctionId,
    next_function_id: u64,
}

impl SSA {
    pub fn to_string(&self, value_annotator: &dyn SsaAnnotator) -> String {
        println!("Entry point: {}", self.main_id.0);
        self.functions
            .iter()
            .sorted_by_key(|(fn_id, _)| fn_id.0)
            .map(|(fn_id, func)| func.to_string(*fn_id, value_annotator))
            .join("\n\n")
    }

    pub fn new() -> Self {
        let main_function = Function::empty();
        let main_id = FunctionId(0_u64);
        let mut functions = HashMap::new();
        functions.insert(main_id, main_function);
        SSA {
            functions,
            main_id,
            next_function_id: 1,
        }
    }

    pub fn insert_function(&mut self, function: Function) -> FunctionId {
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

    pub fn get_main_mut(&mut self) -> &mut Function {
        self.functions
            .get_mut(&self.main_id)
            .expect("Main function should exist")
    }

    pub fn get_main(&self) -> &Function {
        self.functions
            .get(&self.main_id)
            .expect("Main function should exist")
    }

    pub fn get_function(&self, id: FunctionId) -> &Function {
        self.functions.get(&id).expect("Function should exist")
    }

    pub fn get_function_mut(&mut self, id: FunctionId) -> &mut Function {
        self.functions.get_mut(&id).expect("Function should exist")
    }

    pub fn take_function(&mut self, id: FunctionId) -> Function {
        self.functions.remove(&id).expect("Function should exist")
    }

    pub fn put_function(&mut self, id: FunctionId, function: Function) {
        self.functions.insert(id, function);
    }

    pub fn add_function(&mut self) -> FunctionId {
        let new_id = FunctionId(self.next_function_id);
        self.next_function_id += 1;
        let function = Function::empty();
        self.functions.insert(new_id, function);
        new_id
    }

    pub fn typecheck(&mut self) {
        let function_types = self
            .functions
            .iter()
            .map(|(id, func)| (*id, (func.get_param_types(), func.returns.clone())))
            .collect::<HashMap<_, _>>();

        for (fid, function) in self.functions.iter_mut() {
            if let Err(err) = function.typecheck(&function_types) {
                panic!("Typecheck failed for function {}: {}", fid.0, err);
            }
        }
    }

    pub fn iter_functions(&self) -> impl Iterator<Item = (&FunctionId, &Function)> {
        self.functions.iter()
    }

    pub fn iter_functions_mut(&mut self) -> impl Iterator<Item = (&FunctionId, &mut Function)> {
        self.functions.iter_mut()
    }

    pub fn from_noir(noir_ssa: &noirc_evaluator::ssa::ssa_gen::Ssa) -> Self {
        let mut converter = SsaConverter::new();
        converter.convert_noir_ssa(noir_ssa)
    }

    pub fn get_function_ids(&self) -> impl Iterator<Item = FunctionId> {
        self.functions.keys().copied()
    }
}

#[derive(Clone)]
pub struct Function {
    entry_block: BlockId,
    blocks: HashMap<BlockId, Block>,
    returns: Vec<Type>,
    next_block: u64,
    value_info: HashMap<ValueId, Type>,
    next_value: u64,
}

impl Function {
    pub fn to_string(&self, id: FunctionId, value_annotator: &dyn SsaAnnotator) -> String {
        let header = format!(
            "fn_{}@block_{} -> {} [{}] {{",
            id.0,
            self.entry_block.0,
            self.returns.iter().map(|t| t.to_string()).join(", "),
            value_annotator.annotate_function(id)
        );
        let blocks = self
            .blocks
            .iter()
            .sorted_by_key(|(bid, _)| bid.0)
            .map(|(bid, block)| block.to_string(id, *bid, value_annotator))
            .join("\n");
        let footer = "}".to_string();
        format!("{}\n{}\n{}", header, blocks, footer)
    }

    pub fn empty() -> Self {
        let entry = Block::empty();
        let entry_id = BlockId(0);
        let mut blocks = HashMap::new();
        blocks.insert(entry_id, entry);
        Function {
            entry_block: BlockId(0),
            blocks,
            next_block: 1,
            returns: Vec::new(),
            value_info: HashMap::new(),
            next_value: 0,
        }
    }

    pub fn unsafe_empty() -> Self {
        Function {
            entry_block: BlockId(0),
            blocks: HashMap::new(),
            next_block: 0,
            returns: Vec::new(),
            value_info: HashMap::new(),
            next_value: 0,
        }
    }

    pub fn get_entry_mut(&mut self) -> &mut Block {
        self.blocks
            .get_mut(&self.entry_block)
            .expect("Entry block should exist")
    }

    pub fn get_entry(&self) -> &Block {
        self.blocks
            .get(&self.entry_block)
            .expect("Entry block should exist")
    }

    pub fn get_entry_id(&self) -> BlockId {
        self.entry_block
    }

    pub fn get_block(&self, id: BlockId) -> &Block {
        self.blocks.get(&id).expect("Block should exist")
    }

    pub fn get_block_mut(&mut self, id: BlockId) -> &mut Block {
        self.blocks.get_mut(&id).expect("Block should exist")
    }

    pub fn take_block(&mut self, id: BlockId) -> Block {
        self.blocks.remove(&id).expect("Block should exist")
    }

    pub fn put_block(&mut self, id: BlockId, block: Block) {
        self.blocks.insert(id, block);
    }

    pub fn add_block(&mut self) -> BlockId {
        let new_id = BlockId(self.next_block);
        self.next_block += 1;
        let block = Block::empty();
        self.blocks.insert(new_id, block);
        new_id
    }

    pub fn add_return_type(&mut self, typ: Type) {
        self.returns.push(typ);
    }

    pub fn get_param_types(&self) -> Vec<Type> {
        self.get_entry()
            .parameters
            .iter()
            .map(|(_, typ)| typ.clone())
            .collect()
    }

    fn typecheck(
        &mut self,
        function_types: &HashMap<FunctionId, (Vec<Type>, Vec<Type>)>,
    ) -> Result<(), String> {
        let block_input_types = self
            .blocks
            .iter()
            .map(|(id, block)| {
                (
                    *id,
                    block
                        .parameters
                        .iter()
                        .map(|(_, typ)| typ.clone())
                        .collect::<Vec<_>>(),
                )
            })
            .collect::<HashMap<_, _>>();

        for block in self.blocks.values() {
            for instruction in block.get_instructions() {
                instruction.typecheck(&mut self.value_info, function_types)?;
            }
        }

        for block in self.blocks.values() {
            if let Some(terminator) = block.get_terminator() {
                terminator.typecheck(&block_input_types, &self.value_info, &self.returns)?;
            }
        }

        Ok(())
    }

    pub fn get_returns(&self) -> &[Type] {
        &self.returns
    }

    pub fn get_blocks(&self) -> impl Iterator<Item = (&BlockId, &Block)> {
        self.blocks.iter()
    }

    pub fn get_value_type(&self, value: ValueId) -> Option<&Type> {
        self.value_info.get(&value)
    }

    pub fn add_parameter(&mut self, block_id: BlockId, typ: Type) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.value_info.insert(value_id, typ.clone());
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .parameters
            .push((value_id, typ));
        value_id
    }
    pub fn push_bool_const(&mut self, block_id: BlockId, value: bool) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.value_info.insert(value_id, Type::Bool);
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::BConst(value_id, value));
        value_id
    }
    pub fn push_u32_const(&mut self, block_id: BlockId, value: u32) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.value_info.insert(value_id, Type::U32);
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::UConst(value_id, value));
        value_id
    }
    pub fn push_field_const(&mut self, block_id: BlockId, value: ark_bn254::Fr) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.value_info.insert(value_id, Type::Field);
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::FieldConst(value_id, value));
        value_id
    }
    pub fn push_eq(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.value_info.insert(value_id, Type::Bool);
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Eq(value_id, lhs, rhs));
        value_id
    }
    pub fn push_add(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        if let Some(lhs_type) = self.value_info.get(&lhs) {
            self.value_info.insert(value_id, lhs_type.clone());
        }
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Add(value_id, lhs, rhs));
        value_id
    }
    pub fn push_mul(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.value_info.insert(value_id, Type::Field);
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Mul(value_id, lhs, rhs));
        value_id
    }
    pub fn push_lt(&mut self, block_id: BlockId, lhs: ValueId, rhs: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.value_info.insert(value_id, Type::Bool);
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Lt(value_id, lhs, rhs));
        value_id
    }
    pub fn push_alloc(&mut self, block_id: BlockId, typ: Type) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.value_info
            .insert(value_id, Type::Ref(Box::new(typ.clone())));
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Alloc(value_id, typ));
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
        if let Some(ptr_type) = self.value_info.get(&ptr) {
            if let Type::Ref(ref_type) = ptr_type {
                self.value_info.insert(value_id, *ref_type.clone());
            }
        }
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
            self.value_info.insert(value_id, Type::Field); // TODO: use actual return type
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
        if let Some(array_type) = self.value_info.get(&array) {
            if let Type::Array(element_type, _) = array_type {
                self.value_info.insert(value_id, *element_type.clone());
            }
        }
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::ArrayGet(value_id, array, index));
        value_id
    }

    pub fn push_constrain(&mut self, block_id: BlockId, a: ValueId, b: ValueId, c: ValueId) {
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::Constrain(a, b, c));
    }

    pub fn push_witness_write(&mut self, block_id: BlockId, value: ValueId) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        self.blocks
            .get_mut(&block_id)
            .unwrap()
            .instructions
            .push(OpCode::WriteWitness(value_id, value));
        value_id
    }

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

    pub fn get_blocks_mut(&mut self) -> impl Iterator<Item = (&BlockId, &mut Block)> {
        self.blocks.iter_mut()
    }

    pub fn fresh_value(&mut self) -> ValueId {
        let value_id = ValueId(self.next_value);
        self.next_value += 1;
        value_id
    }
}

#[derive(Clone)]
pub struct Block {
    parameters: Vec<(ValueId, Type)>,
    instructions: Vec<OpCode>,
    terminator: Option<Terminator>,
}

impl Block {
    fn to_string(
        &self,
        func_id: FunctionId,
        id: BlockId,
        value_annotator: &dyn SsaAnnotator,
    ) -> String {
        let params = self
            .parameters
            .iter()
            .map(|v| {
                format!(
                    "v{} : {} [{}]",
                    v.0.0,
                    v.1.to_string(),
                    value_annotator.annotate_value(func_id, v.0)
                )
            })
            .join(", ");
        let local_annotator = LocalFunctionAnnotator::new(func_id, value_annotator);
        let instructions = self
            .instructions
            .iter()
            .map(|i| format!("    {}", i.to_string(&local_annotator)))
            .join("\n");
        let terminator = match &self.terminator {
            Some(t) => format!("    {}", t.to_string()),
            None => "".to_string(),
        };
        format!(
            "  block_{}({}) [{}] {{\n{}\n{}\n  }}",
            id.0,
            params,
            value_annotator.annotate_block(func_id, id),
            instructions,
            terminator
        )
    }

    pub fn empty() -> Self {
        Block {
            parameters: Vec::new(),
            instructions: Vec::new(),
            terminator: None,
        }
    }

    pub fn take_instructions(&mut self) -> Vec<OpCode> {
        std::mem::take(&mut self.instructions)
    }

    pub fn put_instructions(&mut self, instructions: Vec<OpCode>) {
        self.instructions = instructions;
    }

    pub fn push_instruction(&mut self, instruction: OpCode) {
        self.instructions.push(instruction);
    }

    pub fn set_terminator(&mut self, terminator: Terminator) {
        self.terminator = Some(terminator);
    }

    pub fn get_parameters(&self) -> impl Iterator<Item = &(ValueId, Type)> {
        self.parameters.iter()
    }

    pub fn take_parameters(&mut self) -> Vec<(ValueId, Type)> {
        std::mem::take(&mut self.parameters)
    }

    pub fn get_parameter_values(&self) -> impl Iterator<Item = &ValueId> {
        self.parameters.iter().map(|(id, _)| id)
    }

    pub fn get_instructions(&self) -> impl Iterator<Item = &OpCode> {
        self.instructions.iter()
    }

    pub fn get_instructions_mut(&mut self) -> impl Iterator<Item = &mut OpCode> {
        self.instructions.iter_mut()
    }

    pub fn get_terminator(&self) -> Option<&Terminator> {
        self.terminator.as_ref()
    }

    pub fn take_terminator(&mut self) -> Option<Terminator> {
        std::mem::take(&mut self.terminator)
    }
}

#[derive(Debug, Clone)]
pub enum OpCode {
    FieldConst(ValueId, ark_bn254::Fr),           // _1 = constant(_2)
    BConst(ValueId, bool),                        // _1 = constant(_2)
    UConst(ValueId, u32),                         // _1 = constant(_2)
    Eq(ValueId, ValueId, ValueId),                // _1 = _2 == _3
    Add(ValueId, ValueId, ValueId),               // _1 = _2 + _3
    Mul(ValueId, ValueId, ValueId),               // _1 = _2 * _3
    Lt(ValueId, ValueId, ValueId),                // _1 = _2 < _3
    Alloc(ValueId, Type),                         // _1 = alloc(Type)
    Store(ValueId, ValueId),                      // *_1 = _2
    Load(ValueId, ValueId),                       // _1 = *_2
    AssertEq(ValueId, ValueId),                   // assert _1 == _2
    Call(Vec<ValueId>, FunctionId, Vec<ValueId>), // _1, ... = call function(_2, _3, ...)
    ArrayGet(ValueId, ValueId, ValueId),          // _1 = _2[_3]

    // Phase 2
    WriteWitness(ValueId, ValueId), // _1 = as_witness(_2)
    // IncA(ValueId, ValueId, ValueId), // a += _2(pure) * _3(witness); _1 = a
    // IncB(ValueId, ValueId, ValueId), // b += _2(pure) * _3(witness); _1 = b
    // IncC(ValueId, ValueId, ValueId), // c += _2(pure) * _3(witness); _1 = c
    // SealConstraint,
    Constrain(ValueId, ValueId, ValueId), // assert(_1 * _2 - _3 == 0)
}

impl OpCode {
    pub fn to_string(&self, value_annotator: &LocalFunctionAnnotator) -> String {
        match self {
            OpCode::FieldConst(result, value) => {
                format!(
                    "v{}[{}] = constant({}:Field)",
                    result.0,
                    value_annotator.annotate_value(*result),
                    value
                )
            }
            OpCode::UConst(result, value) => format!(
                "v{}[{}] = constant({}:u32)",
                result.0,
                value_annotator.annotate_value(*result),
                value
            ),
            OpCode::BConst(result, value) => format!(
                "v{}[{}] = constant({}:bool)",
                result.0,
                value_annotator.annotate_value(*result),
                value
            ),
            OpCode::Eq(result, lhs, rhs) => format!(
                "v{}[{}] = v{} == v{}",
                result.0,
                value_annotator.annotate_value(*result),
                lhs.0,
                rhs.0
            ),
            OpCode::Add(result, lhs, rhs) => format!(
                "v{}[{}] = v{} + v{}",
                result.0,
                value_annotator.annotate_value(*result),
                lhs.0,
                rhs.0
            ),
            OpCode::Mul(result, lhs, rhs) => format!(
                "v{}[{}] = v{} * v{}",
                result.0,
                value_annotator.annotate_value(*result),
                lhs.0,
                rhs.0
            ),
            OpCode::Lt(result, lhs, rhs) => format!(
                "v{}[{}] = v{} < v{}",
                result.0,
                value_annotator.annotate_value(*result),
                lhs.0,
                rhs.0
            ),
            OpCode::Alloc(result, typ) => format!(
                "v{}[{}] = alloc({})",
                result.0,
                value_annotator.annotate_value(*result),
                typ.to_string()
            ),
            OpCode::Store(ptr, value) => format!("*v{} = v{}", ptr.0, value.0),
            OpCode::Load(result, ptr) => {
                format!(
                    "v{}[{}] = *v{}",
                    result.0,
                    value_annotator.annotate_value(*result),
                    ptr.0
                )
            }
            OpCode::AssertEq(lhs, rhs) => format!("assert v{} == v{}", lhs.0, rhs.0),
            OpCode::Call(result, fn_id, args) => {
                let args_str = args.iter().map(|v| format!("v{}", v.0)).join(", ");
                let result_str = result
                    .iter()
                    .map(|v| format!("v{}[{}]", v.0, value_annotator.annotate_value(*v)))
                    .join(", ");
                format!("{} = call {}({})", result_str, fn_id.0, args_str)
            }
            OpCode::ArrayGet(result, array, index) => {
                format!(
                    "v{}[{}] = v{}[v{}]",
                    result.0,
                    value_annotator.annotate_value(*result),
                    array.0,
                    index.0
                )
            }
            OpCode::WriteWitness(result, value) => {
                format!(
                    "v{}[{}] = witness(v{})",
                    result.0,
                    value_annotator.annotate_value(*result),
                    value.0
                )
            }
            // OpCode::IncA(result, coeff, witness) => {
            //     format!(
            //         "v{}[{}] = inc_a(v{}, v{})",
            //         result.0,
            //         value_annotator.annotate_value(*result),
            //         coeff.0,
            //         witness.0
            //     )
            // }
            // OpCode::IncB(result, coeff, witness) => {
            //     format!(
            //         "v{}[{}] = inc_b(v{}, v{})",
            //         result.0,
            //         value_annotator.annotate_value(*result),
            //         coeff.0,
            //         witness.0
            //     )
            // }
            // OpCode::IncC(result, coeff, witness) => {
            //     format!(
            //         "v{}[{}] = inc_c(v{}, v{})",
            //         result.0,
            //         value_annotator.annotate_value(*result),
            //         coeff.0,
            //         witness.0
            //     )
            // }
            // OpCode::SealConstraint => "seal_constraint".to_string(),
            OpCode::Constrain(a, b, c) => {
                format!("constrain_r1c(v{} * v{} - v{} == 0)", a.0, b.0, c.0)
            }
        }
    }

    pub fn typecheck(
        &self,
        type_assignments: &mut HashMap<ValueId, Type>,
        function_types: &HashMap<FunctionId, (Vec<Type>, Vec<Type>)>,
    ) -> Result<(), String> {
        match self {
            Self::FieldConst(result, _) => {
                type_assignments.insert(*result, Type::field());
                Ok(())
            }
            Self::BConst(result, _) => {
                type_assignments.insert(*result, Type::bool());
                Ok(())
            }
            Self::UConst(result, _) => {
                type_assignments.insert(*result, Type::u32());
                Ok(())
            }
            Self::Eq(result, lhs, rhs) => {
                let lhs_type = type_assignments.get(lhs).ok_or_else(|| {
                    format!(
                        "Left-hand side value {:?} not found in type assignments",
                        lhs
                    )
                })?;
                let rhs_type = type_assignments.get(rhs).ok_or_else(|| {
                    format!(
                        "Right-hand side value {:?} not found in type assignments",
                        rhs
                    )
                })?;
                if lhs_type != rhs_type && !lhs_type.is_numeric() && !rhs_type.is_numeric() {
                    return Err(format!(
                        "Type mismatch in equality: {:?} ({}) != {:?} ({})",
                        lhs,
                        lhs_type.to_string(),
                        rhs,
                        rhs_type.to_string()
                    ));
                }
                type_assignments.insert(*result, Type::bool());
                Ok(())
            }
            Self::Add(result, lhs, rhs) => {
                let lhs_type = type_assignments.get(lhs).ok_or_else(|| {
                    format!(
                        "Left-hand side value {:?} not found in type assignments",
                        lhs
                    )
                })?;
                let rhs_type = type_assignments.get(rhs).ok_or_else(|| {
                    format!(
                        "Right-hand side value {:?} not found in type assignments",
                        rhs
                    )
                })?;
                if !lhs_type.is_numeric() || !rhs_type.is_numeric() {
                    return Err(format!(
                        "Type mismatch in addition: {:?} ({}) + {:?} ({})",
                        lhs,
                        lhs_type.to_string(),
                        rhs,
                        rhs_type.to_string()
                    ));
                }
                type_assignments.insert(*result, lhs_type.get_arithmetic_result_type(rhs_type));
                Ok(())
            }
            Self::Mul(result, lhs, rhs) => {
                let lhs_type = type_assignments.get(lhs).ok_or_else(|| {
                    format!(
                        "Left-hand side value {:?} not found in type assignments",
                        lhs
                    )
                })?;
                let rhs_type = type_assignments.get(rhs).ok_or_else(|| {
                    format!(
                        "Right-hand side value {:?} not found in type assignments",
                        rhs
                    )
                })?;
                if !lhs_type.is_numeric() || !rhs_type.is_numeric() {
                    return Err(format!(
                        "Type mismatch in multiplication: {:?} ({}) * {:?} ({})",
                        lhs,
                        lhs_type.to_string(),
                        rhs,
                        rhs_type.to_string()
                    ));
                }
                type_assignments.insert(*result, lhs_type.get_arithmetic_result_type(rhs_type));
                Ok(())
            }
            Self::Lt(result, lhs, rhs) => {
                let lhs_type = type_assignments.get(lhs).ok_or_else(|| {
                    format!(
                        "Left-hand side value {:?} not found in type assignments",
                        lhs
                    )
                })?;
                let rhs_type = type_assignments.get(rhs).ok_or_else(|| {
                    format!(
                        "Right-hand side value {:?} not found in type assignments",
                        rhs
                    )
                })?;
                if !lhs_type.is_numeric() || !rhs_type.is_numeric() {
                    return Err(format!(
                        "Type mismatch in less than: {:?} ({}) < {:?} ({})",
                        lhs,
                        lhs_type.to_string(),
                        rhs,
                        rhs_type.to_string()
                    ));
                }
                type_assignments.insert(*result, Type::bool());
                Ok(())
            }
            Self::Alloc(result, typ) => {
                type_assignments.insert(*result, typ.clone().ref_of());
                Ok(())
            }
            Self::Store(ptr, value) => {
                let ptr_type = type_assignments.get(ptr).ok_or_else(|| {
                    format!("Pointer value {:?} not found in type assignments", ptr)
                })?;
                let value_type = type_assignments.get(value).ok_or_else(|| {
                    format!("Value to store {:?} not found in type assignments", value)
                })?;
                if !ptr_type.is_ref_of(value_type) {
                    return Err(format!(
                        "Type mismatch in store: pointer type {} does not match value type {}",
                        ptr_type.to_string(),
                        value_type.to_string()
                    ));
                }
                Ok(())
            }
            Self::Load(result, ptr) => {
                let ptr_type = type_assignments.get(ptr).ok_or_else(|| {
                    format!("Pointer value {:?} not found in type assignments", ptr)
                })?;
                if !ptr_type.is_ref() {
                    return Err(format!(
                        "Load operation expects a reference type, got {}",
                        ptr_type.to_string()
                    ));
                }
                type_assignments.insert(*result, ptr_type.get_refered());
                Ok(())
            }
            Self::AssertEq(lhs, rhs) => {
                let lhs_type = type_assignments.get(lhs).ok_or_else(|| {
                    format!(
                        "Left-hand side value {:?} not found in type assignments",
                        lhs
                    )
                })?;
                let rhs_type = type_assignments.get(rhs).ok_or_else(|| {
                    format!(
                        "Right-hand side value {:?} not found in type assignments",
                        rhs
                    )
                })?;
                if lhs_type != rhs_type || !lhs_type.has_eq() {
                    return Err(format!(
                        "Type mismatch in assertion: {:?} ({}) == {:?} ({})",
                        lhs,
                        lhs_type.to_string(),
                        rhs,
                        rhs_type.to_string()
                    ));
                }
                Ok(())
            }
            Self::Call(result, fn_id, args) => {
                let (param_types, return_types) = function_types
                    .get(fn_id)
                    .ok_or_else(|| format!("Function {:?} not found", fn_id))?;

                if args.len() != param_types.len() {
                    return Err(format!(
                        "Function {:?} expects {} arguments, got {}",
                        fn_id,
                        param_types.len(),
                        args.len()
                    ));
                }

                for (arg, expected_type) in args.iter().zip(param_types) {
                    let arg_type = type_assignments.get(arg).ok_or_else(|| {
                        format!("Argument value {:?} not found in type assignments", arg)
                    })?;
                    if arg_type != expected_type {
                        return Err(format!(
                            "Type mismatch for argument {:?}: expected {}, got {}",
                            arg,
                            expected_type.to_string(),
                            arg_type.to_string()
                        ));
                    }
                }

                if result.len() != return_types.len() {
                    return Err(format!(
                        "Function {:?} expects {} return values, got {}",
                        fn_id,
                        return_types.len(),
                        result.len()
                    ));
                }

                for (ret, ret_type) in result.iter().zip(return_types) {
                    type_assignments.insert(*ret, ret_type.clone());
                }
                Ok(())
            }
            Self::ArrayGet(result, array, index) => {
                let array_type = type_assignments.get(array).ok_or_else(|| {
                    format!("Array value {:?} not found in type assignments", array)
                })?;
                let index_type = type_assignments.get(index).ok_or_else(|| {
                    format!("Index value {:?} not found in type assignments", index)
                })?;

                if !array_type.is_array() {
                    return Err(format!(
                        "Array get operation expects an array type, got {}",
                        array_type.to_string()
                    ));
                }
                if !index_type.is_u32() {
                    return Err(format!(
                        "Array get operation expects an u32 index, got {}",
                        index_type.to_string()
                    ));
                }

                let element_type = array_type.get_array_element();
                type_assignments.insert(*result, element_type);
                Ok(())
            }
            Self::WriteWitness(result, value) => {
                let witness_type = type_assignments.get(value).ok_or_else(|| {
                    format!("Witness value {:?} not found in type assignments", value)
                })?;
                type_assignments.insert(*result, witness_type.clone());
                Ok(())
            }
            // Self::IncA { .. }
            // | Self::IncB { .. }
            // | Self::IncC { .. }
            // | Self::SealConstraint
            Self::Constrain { .. } => Ok(()),
        }
    }

    pub fn get_operands_mut(&mut self) -> impl Iterator<Item = &mut ValueId> {
        match self {
            Self::FieldConst(r, _)
            | Self::BConst(r, _)
            | Self::UConst(r, _)
            | Self::Alloc(r, _) => vec![r].into_iter(),
            Self::Eq(a, b, c)
            | Self::Add(a, b, c)
            | Self::Mul(a, b, c)
            | Self::Lt(a, b, c)
            | Self::ArrayGet(a, b, c)
            | Self::Constrain(a, b, c) => vec![a, b, c].into_iter(),
            Self::Store(a, b)
            | Self::Load(a, b)
            | Self::AssertEq(a, b)
            | Self::WriteWitness(a, b) => vec![a, b].into_iter(),
            Self::Call(r, _, a) => {
                let mut ret_vec = r.iter_mut().collect::<Vec<_>>();
                let args_vec = a.iter_mut().collect::<Vec<_>>();
                ret_vec.extend(args_vec);
                ret_vec.into_iter()
            }
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

    fn typecheck_jump_target(
        tgt_block: BlockId,
        inputs: &[ValueId],
        block_input_types: &HashMap<BlockId, Vec<Type>>,
        value_types: &HashMap<ValueId, Type>,
    ) -> Result<(), String> {
        let input_types = inputs
            .iter()
            .map(|v| value_types[v].clone())
            .collect::<Vec<_>>();
        let expected_types = block_input_types
            .get(&tgt_block)
            .ok_or_else(|| format!("Block {:?} not found", tgt_block))?;

        if input_types.len() != expected_types.len() {
            return Err(format!(
                "Block {:?} expects {} arguments, got {}",
                tgt_block,
                expected_types.len(),
                input_types.len()
            ));
        }

        for (input, expected) in input_types.iter().zip(expected_types) {
            if input != expected {
                return Err(format!(
                    "Type mismatch for argument. Expected {}, got {}",
                    expected.to_string(),
                    input.to_string()
                ));
            }
        }

        Ok(())
    }

    fn typecheck(
        &self,
        block_input_types: &HashMap<BlockId, Vec<Type>>,
        value_types: &HashMap<ValueId, Type>,
        returns: &[Type],
    ) -> Result<(), String> {
        match self {
            Terminator::Jmp(bid, args) => {
                Self::typecheck_jump_target(*bid, args, block_input_types, value_types)?;
            }
            Terminator::JmpIf(cond, true_block, false_block) => {
                Self::typecheck_jump_target(*true_block, &[], block_input_types, value_types)?;
                Self::typecheck_jump_target(*false_block, &[], block_input_types, value_types)?;
            }
            Terminator::Return(values) => {
                let value_types = values
                    .iter()
                    .map(|v| value_types.get(v).cloned())
                    .collect::<Option<Vec<_>>>()
                    .ok_or_else(|| "Return values not found in value types".to_string())?;
                if value_types.len() != returns.len() {
                    return Err(format!(
                        "Function expects {} return values, got {}",
                        returns.len(),
                        value_types.len()
                    ));
                }
                for (value_type, expected_type) in value_types.iter().zip(returns) {
                    if value_type != expected_type {
                        return Err(format!(
                            "Return type mismatch. Expected {}, got {}",
                            expected_type.to_string(),
                            value_type.to_string()
                        ));
                    }
                }
            }
        }
        Ok(())
    }
}
