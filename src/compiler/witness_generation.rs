use std::{cell::RefCell, collections::HashMap, fmt::Display, rc::Rc};

use crate::compiler::ssa::{BlockId, Function, FunctionId, OpCode, SSA, Terminator, Type, ValueId};
use ark_ff::{AdditiveGroup, Field, PrimeField};
use graphviz_rust::attributes::width;
use itertools::Itertools;

#[derive(Clone, Debug)]
pub enum Value {
    Fp(ark_bn254::Fr),
    Array(Vec<Value>),
    Ptr(Rc<RefCell<Value>>),
    Invalid,
}

impl Value {
    pub fn add(&self, other: &Value) -> Value {
        Self::Fp(self.expect_fp() + other.expect_fp())
    }

    pub fn expect_fp(&self) -> ark_bn254::Fr {
        match self {
            Value::Fp(c) => *c,
            _ => panic!("expected fp"),
        }
    }

    pub fn expect_u32(&self) -> u32 {
        match self {
            Value::Fp(c) => c.into_bigint().to_string().parse().unwrap(),
            _ => panic!("expected u32"),
        }
    }

    pub fn mul(&self, other: &Value) -> Value {
        Self::Fp(self.expect_fp() * other.expect_fp())
    }

    pub fn expect_ptr(&self) -> Rc<RefCell<Value>> {
        match self {
            Value::Ptr(ptr) => ptr.clone(),
            _ => panic!("expected ptr"),
        }
    }

    pub fn lt(&self, other: &Value) -> Value {
        let self_const = self.expect_fp();
        let other_const = other.expect_fp();
        if self_const < other_const {
            Value::Fp(ark_bn254::Fr::ONE)
        } else {
            Value::Fp(ark_bn254::Fr::ZERO)
        }
    }

    pub fn eq(&self, other: &Value) -> Value {
        let self_const = self.expect_fp();
        let other_const = other.expect_fp();
        if self_const == other_const {
            Value::Fp(ark_bn254::Fr::ONE)
        } else {
            Value::Fp(ark_bn254::Fr::ZERO)
        }
    }

    pub fn expect_array(&self) -> Vec<Value> {
        match self {
            Value::Array(array) => array.clone(),
            _ => panic!("expected array"),
        }
    }
}

pub struct WitnessGen {
    a: Vec<ark_bn254::Fr>,
    b: Vec<ark_bn254::Fr>,
    c: Vec<ark_bn254::Fr>,
    witness: Vec<ark_bn254::Fr>,
}

impl WitnessGen {
    pub fn new(public_witness: Vec<ark_bn254::Fr>) -> Self {
        Self {
            a: vec![],
            b: vec![],
            c: vec![],
            witness: public_witness,
        }
    }

    pub fn run(&mut self, ssa: &SSA) {
        let entry_point = ssa.get_main_id();
        let params = ssa.get_function(entry_point).get_param_types();
        let mut main_params = vec![];
        let witness = self.witness.clone();
        let mut witness_iter = witness.iter().skip(1).copied();
        for value_type in params {
            main_params.push(self.initialize_main_input(&value_type, &mut witness_iter));
        }

        self.run_function(ssa, entry_point, main_params);
    }

    pub fn get_witness(&self) -> Vec<ark_bn254::Fr> {
        self.witness.clone()
    }

    pub fn get_a(&self) -> Vec<ark_bn254::Fr> {
        self.a.clone()
    }
    pub fn get_b(&self) -> Vec<ark_bn254::Fr> {
        self.b.clone()
    }

    pub fn get_c(&self) -> Vec<ark_bn254::Fr> {
        self.c.clone()
    }

    pub fn run_function(
        &mut self,
        ssa: &SSA,
        function_id: FunctionId,
        params: Vec<Value>,
    ) -> Vec<Value> {
        let function = ssa.get_function(function_id);
        let entry_block_id = function.get_entry_id();
        let mut scope = HashMap::<ValueId, Value>::new();
        self.update_scope_with_args(&mut scope, params, &function, entry_block_id);

        let mut block_id = entry_block_id;

        loop {
            let block = function.get_block(block_id);
            for instruction in block.get_instructions() {
                match instruction {
                    OpCode::FieldConst(result, value) => {
                        scope.insert(*result, Value::Fp(*value));
                    }

                    OpCode::BConst(result, value) => {
                        scope.insert(*result, Value::Fp(ark_bn254::Fr::from(*value as u64)));
                    }

                    OpCode::UConst(result, value) => {
                        scope.insert(*result, Value::Fp(ark_bn254::Fr::from(*value as u64)));
                    }

                    OpCode::Add(result, lhs, rhs) => {
                        let lhs = scope.get(lhs).unwrap();
                        let rhs = scope.get(rhs).unwrap();
                        let r = lhs.add(rhs);
                        scope.insert(*result, r);
                    }

                    OpCode::Mul(result, lhs, rhs) => {
                        let lhs = scope.get(lhs).unwrap();
                        let rhs = scope.get(rhs).unwrap();
                        let r = lhs.mul(rhs);
                        scope.insert(*result, r);
                    }

                    OpCode::Lt(result, lhs, rhs) => {
                        let lhs = scope.get(lhs).unwrap();
                        let rhs = scope.get(rhs).unwrap();
                        let r = lhs.lt(rhs);
                        scope.insert(*result, r);
                    }

                    OpCode::Alloc(result, _) => {
                        scope.insert(*result, Value::Ptr(Rc::new(RefCell::new(Value::Invalid))));
                    }
                    OpCode::Store(ptr, value) => {
                        let ptr = scope.get(ptr).unwrap().expect_ptr();
                        let value = scope.get(value).unwrap();
                        *ptr.borrow_mut() = value.clone();
                    }
                    OpCode::Load(result, ptr) => {
                        let ptr = scope.get(ptr).unwrap().expect_ptr();
                        let value = ptr.borrow().clone();
                        scope.insert(*result, value);
                    }

                    OpCode::ArrayGet(result, array, index) => {
                        let array = scope.get(array).unwrap().expect_array();
                        let index = scope.get(index).unwrap().expect_u32();
                        let value = array[index as usize].clone();
                        scope.insert(*result, value);
                    }

                    OpCode::Eq(result, lhs, rhs) => {
                        let lhs = scope.get(lhs).unwrap();
                        let rhs = scope.get(rhs).unwrap();
                        let r = lhs.eq(rhs);
                        scope.insert(*result, r);
                    }

                    OpCode::AssertEq(_, _) => {
                        // No-op
                    }

                    OpCode::Constrain(a, b, c) => {
                        let a = scope.get(a).unwrap();
                        let b = scope.get(b).unwrap();
                        let c = scope.get(c).unwrap();
                        self.a.push(a.expect_fp());
                        self.b.push(b.expect_fp());
                        self.c.push(c.expect_fp());
                    }
                    OpCode::WriteWitness(result, v) => {
                        let v = scope.get(v).unwrap().clone();
                        scope.insert(*result, v.clone());
                        self.witness.push(v.expect_fp());
                    }

                    OpCode::Call(ret, tgt, args) => {
                        let args = args
                            .iter()
                            .map(|arg| scope.get(arg).unwrap().clone())
                            .collect();
                        let results = self.run_function(ssa, *tgt, args);
                        for (ret, result) in ret.iter().zip(results.into_iter()) {
                            scope.insert(*ret, result);
                        }
                    }

                    _ => panic!("unexpected instruction {:?}", instruction),
                }
            }

            let terminator = block.get_terminator();
            match terminator {
                Some(Terminator::Return(result)) => {
                    let results = result
                        .iter()
                        .map(|result| scope.get(result).unwrap().clone());
                    return results.collect();
                }
                Some(Terminator::Jmp(target, args)) => {
                    let args = args
                        .iter()
                        .map(|arg| scope.get(arg).unwrap().clone())
                        .collect();
                    self.update_scope_with_args(&mut scope, args, &function, *target);
                    block_id = *target;
                }
                Some(Terminator::JmpIf(cond, if_true, if_false)) => {
                    let cond = scope.get(cond).unwrap();
                    let cond = cond.expect_fp();
                    if cond == ark_bn254::Fr::ZERO {
                        block_id = *if_false;
                    } else {
                        block_id = *if_true;
                    }
                }
                None => {
                    panic!("unexpected terminator");
                }
            }
        }
    }

    fn update_scope_with_args(
        &self,
        scope: &mut HashMap<ValueId, Value>,
        args: Vec<Value>,
        function: &Function,
        block_id: BlockId,
    ) {
        let block = function.get_block(block_id);
        for (val_id, arg) in block.get_parameter_values().zip(args.into_iter()) {
            scope.insert(*val_id, arg);
        }
    }

    fn initialize_main_input(
        &mut self,
        tp: &Type,
        witness_iter: &mut impl Iterator<Item = ark_bn254::Fr>,
    ) -> Value {
        match tp {
            Type::Bool => Value::Fp(witness_iter.next().unwrap()),
            Type::U32 => Value::Fp(witness_iter.next().unwrap()),
            Type::Field => Value::Fp(witness_iter.next().unwrap()),
            Type::Array(tp, size) => {
                let mut result = vec![];
                for _ in 0..*size {
                    result.push(self.initialize_main_input(tp, witness_iter));
                }
                Value::Array(result)
            }
            _ => panic!("unexpected main params"),
        }
    }
}
