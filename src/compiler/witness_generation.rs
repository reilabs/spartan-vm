use std::{cell::RefCell, collections::HashMap, rc::Rc};

use crate::compiler::{
    ir::r#type::{Type, TypeExpr},
    ssa::{BinaryArithOpKind, BlockId, Const, CmpKind, Endianness, Function, FunctionId, OpCode, SSA, Terminator, ValueId},
};
use ark_ff::{AdditiveGroup, BigInt, BigInteger, Field, PrimeField};
use tracing::instrument;

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

    pub fn sub(&self, other: &Value) -> Value {
        Self::Fp(self.expect_fp() - other.expect_fp())
    }

    pub fn div(&self, other: &Value) -> Value {
        Self::Fp(self.expect_fp() / other.expect_fp())
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

    #[instrument(skip_all, name = "WitnessGen::run")]
    pub fn run<V: Clone>(&mut self, ssa: &SSA<V>) {
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

    pub fn run_function<V: Clone>(
        &mut self,
        ssa: &SSA<V>,
        function_id: FunctionId,
        params: Vec<Value>,
    ) -> Vec<Value> {
        let function = ssa.get_function(function_id);
        let entry_block_id = function.get_entry_id();
        let mut scope = HashMap::<ValueId, Value>::new();
        self.update_scope_with_args(&mut scope, params, &function, entry_block_id);
        for (value_id, const_) in function.iter_consts() {
            match const_ {
                Const::U(_, value) => {
                    scope.insert(*value_id, Value::Fp(ark_bn254::Fr::from(*value)))
                }
                Const::Field(value) => scope.insert(*value_id, Value::Fp(*value)),
            };
        }

        let mut block_id = entry_block_id;

        loop {
            let block = function.get_block(block_id);
            for instruction in block.get_instructions() {
                match instruction {
                    OpCode::BinaryArithOp(BinaryArithOpKind::Add, result, lhs, rhs) => {
                        let lhs = scope.get(lhs).unwrap();
                        let rhs = scope.get(rhs).unwrap();
                        let r = lhs.add(rhs);
                        scope.insert(*result, r);
                    }

                    OpCode::BinaryArithOp(BinaryArithOpKind::Mul, result, lhs, rhs) => {
                        let lhs = scope.get(lhs).unwrap();
                        let rhs = scope.get(rhs).unwrap();
                        let r = lhs.mul(rhs);
                        scope.insert(*result, r);
                    }

                    OpCode::BinaryArithOp(BinaryArithOpKind::Sub, result, lhs, rhs) => {
                        let lhs = scope.get(lhs).unwrap();
                        let rhs = scope.get(rhs).unwrap();
                        let r = lhs.sub(rhs);
                        scope.insert(*result, r);
                    }

                    OpCode::BinaryArithOp(BinaryArithOpKind::Div, result, lhs, rhs) => {
                        let lhs = scope.get(lhs).unwrap();
                        let rhs = scope.get(rhs).unwrap();
                        let r = lhs.div(rhs);
                        scope.insert(*result, r);
                    }

                    OpCode::Cmp(CmpKind::Lt, result, lhs, rhs) => {
                        let lhs = scope.get(lhs).unwrap();
                        let rhs = scope.get(rhs).unwrap();
                        let r = lhs.lt(rhs);
                        scope.insert(*result, r);
                    }

                    OpCode::Alloc(result, _, _) => {
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

                    OpCode::ArraySet(result, array, index, value) => {
                        let array = scope.get(array).unwrap().expect_array();
                        let index = scope.get(index).unwrap().expect_u32();
                        let value = scope.get(value).unwrap().clone();
                        let mut new_array = array.clone();
                        new_array[index as usize] = value;
                        scope.insert(*result, Value::Array(new_array));
                    }

                    OpCode::Cmp(CmpKind::Eq, result, lhs, rhs) => {
                        let lhs = scope.get(lhs).unwrap();
                        let rhs = scope.get(rhs).unwrap();
                        let r = lhs.eq(rhs);
                        scope.insert(*result, r);
                    }

                    OpCode::AssertEq(lhs, rhs) => {
                        let lhs = scope.get(lhs).unwrap();
                        let rhs = scope.get(rhs).unwrap();
                        assert_eq!(lhs.expect_fp(), rhs.expect_fp());
                    }

                    OpCode::AssertR1C(_, _, _) => {
                        todo!();
                    }

                    OpCode::BinaryArithOp(BinaryArithOpKind::And, r, lhs, rhs) => {
                        let lhs = scope.get(lhs).unwrap().expect_u32();
                        let rhs = scope.get(rhs).unwrap().expect_u32();
                        let res = lhs & rhs;
                        scope.insert(*r, Value::Fp(ark_bn254::Fr::from(res)));
                    }
                    OpCode::Select(res_slot, cond, a, b) => {
                        let cond = scope.get(cond).unwrap();
                        let a = scope.get(a).unwrap();
                        let b = scope.get(b).unwrap();
                        let res = if cond.expect_fp() == ark_bn254::Fr::ONE {
                            a.clone()
                        } else {
                            b.clone()
                        };
                        scope.insert(*res_slot, res);
                    }

                    OpCode::Constrain(a, b, c) => {
                        let a = scope.get(a).unwrap();
                        let b = scope.get(b).unwrap();
                        let c = scope.get(c).unwrap();
                        self.a.push(a.expect_fp());
                        self.b.push(b.expect_fp());
                        self.c.push(c.expect_fp());
                    }
                    OpCode::WriteWitness(result, v, _) => {
                        let v = scope.get(v).unwrap().clone();
                        if let Some(result) = result {
                            scope.insert(*result, v.clone());
                        }
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
                    OpCode::MkSeq(result, values, _, _) => {
                        let values = values.iter().map(|v| scope.get(v).unwrap().clone()).collect();
                        scope.insert(*result, Value::Array(values));
                    }
                    OpCode::Cast(result, value, _) => {
                        let value = scope.get(value).unwrap().clone();
                        scope.insert(*result, value);
                    }
                    OpCode::Truncate(result, value, target_bits, _) => {
                        let value = scope.get(value).unwrap().clone();
                        let new_value = value.expect_fp().into_bigint().to_bits_le().iter().take(*target_bits).cloned().collect::<Vec<_>>();
                        let new_value = Value::Fp(ark_bn254::Fr::from_bigint(BigInt::from_bits_le(&new_value)).unwrap());
                        scope.insert(*result, new_value);
                    }
                    OpCode::Not(result, value) => {
                        let value_val = scope.get(value).unwrap().clone();
                        let value_fp = value_val.expect_fp();
                        let bits = value_fp.into_bigint().to_bits_le();
                        
                        // Get the actual type width from the function
                        let bit_size = function.get_value_type(*value).unwrap().get_bit_size();
                        
                        let mut negated_bits = Vec::new();
                        for i in 0..bit_size {
                            let bit = if i < bits.len() { bits[i] } else { false };
                            negated_bits.push(!bit);
                        }
                        let new_value = Value::Fp(ark_bn254::Fr::from_bigint(BigInt::from_bits_le(&negated_bits)).unwrap());
                        scope.insert(*result, new_value);
                    }
                    OpCode::ToBits(result, value, endianness, output_size) => {
                        let value = scope.get(value).unwrap().clone();
                        let value_fp = value.expect_fp();
                        let mut bits = value_fp.into_bigint().to_bits_le();
                        
                        // Truncate or pad to the desired output size
                        if bits.len() > *output_size {
                            bits.truncate(*output_size);
                        } else {
                            while bits.len() < *output_size {
                                bits.push(false);
                            }
                        }
                        
                        // Handle endianness
                        let final_bits = match endianness {
                            Endianness::Little => bits,
                            Endianness::Big => {
                                let mut reversed = bits;
                                reversed.reverse();
                                reversed
                            }
                        };
                        
                        // Convert bits to array of field elements (0 or 1)
                        let mut bit_values = Vec::new();
                        for bit in final_bits {
                            let bit_value = if bit {
                                Value::Fp(ark_bn254::Fr::from(1u128))
                            } else {
                                Value::Fp(ark_bn254::Fr::from(0u128))
                            };
                            bit_values.push(bit_value);
                        }
                        
                        scope.insert(*result, Value::Array(bit_values));
                    }
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

    fn update_scope_with_args<V: Clone>(
        &self,
        scope: &mut HashMap<ValueId, Value>,
        args: Vec<Value>,
        function: &Function<V>,
        block_id: BlockId,
    ) {
        let block = function.get_block(block_id);
        for (val_id, arg) in block.get_parameter_values().zip(args.into_iter()) {
            scope.insert(*val_id, arg);
        }
    }

    fn initialize_main_input<V: Clone>(
        &mut self,
        tp: &Type<V>,
        witness_iter: &mut impl Iterator<Item = ark_bn254::Fr>,
    ) -> Value {
        match &tp.expr {
            TypeExpr::U(_) => Value::Fp(witness_iter.next().unwrap()),
            TypeExpr::Field => Value::Fp(witness_iter.next().unwrap()),
            TypeExpr::Array(tp, size) => {
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
