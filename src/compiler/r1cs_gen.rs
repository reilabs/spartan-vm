use std::{cell::RefCell, collections::HashMap, fmt::Display, rc::Rc};

use crate::compiler::{
    ir::r#type::{Type, TypeExpr},
    ssa::{BlockId, Const, Function, FunctionId, OpCode, SSA, Terminator, ValueId},
};
use ark_ff::{AdditiveGroup, Field, PrimeField};
use itertools::Itertools;

#[derive(Clone, Debug)]
pub enum Value {
    Const(ark_bn254::Fr),
    WitnessVar(usize),
    Add(Box<Value>, Box<Value>),
    Mul(Box<Value>, Box<Value>),
    Array(Vec<Value>),
    Ptr(Rc<RefCell<Value>>),
    Invalid,
}

impl Value {
    pub fn add(&self, other: &Value) -> Value {
        match (self, other) {
            (Value::Const(lhs), Value::Const(rhs)) => Value::Const(lhs + rhs),
            (lhs, rhs) => Value::Add(Box::new(lhs.clone()), Box::new(rhs.clone())),
        }
    }

    pub fn sub(&self, other: &Value) -> Value {
        match (self, other) {
            (Value::Const(lhs), Value::Const(rhs)) => Value::Const(lhs - rhs),
            (lhs, rhs) => {
                let neg_rhs = Value::Const(ark_bn254::Fr::from(-1)).mul(rhs);
                lhs.add(&neg_rhs)
            }
        }
    }

    pub fn expect_constant(&self) -> ark_bn254::Fr {
        match self {
            Value::Const(c) => *c,
            _ => panic!("expected constant"),
        }
    }

    pub fn expect_u32(&self) -> u32 {
        match self {
            Value::Const(c) => c.into_bigint().to_string().parse().unwrap(),
            _ => panic!("expected u32"),
        }
    }

    pub fn mul(&self, other: &Value) -> Value {
        match (self, other) {
            (Value::Const(lhs), Value::Const(rhs)) => Value::Const(lhs * rhs),
            (lhs, rhs) => Value::Mul(Box::new(lhs.clone()), Box::new(rhs.clone())),
        }
    }

    pub fn expect_ptr(&self) -> Rc<RefCell<Value>> {
        match self {
            Value::Ptr(ptr) => ptr.clone(),
            _ => panic!("expected ptr"),
        }
    }

    pub fn lt(&self, other: &Value) -> Value {
        let self_const = self.expect_constant();
        let other_const = other.expect_constant();
        if self_const < other_const {
            Value::Const(ark_bn254::Fr::ONE)
        } else {
            Value::Const(ark_bn254::Fr::ZERO)
        }
    }

    pub fn expect_array(&self) -> Vec<Value> {
        match self {
            Value::Array(array) => array.clone(),
            _ => panic!("expected array"),
        }
    }

    pub fn expect_linear_combination(&self) -> Vec<(usize, ark_bn254::Fr)> {
        let first = match self {
            Value::Const(c) => vec![(0, *c)],
            Value::Mul(l, r) => match (&**l, &**r) {
                (Value::Const(c), other) | (other, Value::Const(c)) => {
                    let mut r = other.expect_linear_combination();
                    for (_, cx) in r.iter_mut() {
                        *cx *= *c;
                    }
                    r
                }
                _ => panic!("expected linear combination, got arb mul"),
            },
            Value::Add(l, r) => {
                let mut l = l.expect_linear_combination();
                let r = r.expect_linear_combination();
                l.extend(r);
                l
            }
            Value::WitnessVar(i) => vec![(*i, ark_bn254::Fr::ONE)],
            _ => panic!("expected linear combination"),
        };
        first
            .into_iter()
            .sorted_by_key(|(i, _)| *i)
            .chunk_by(|(i, _)| *i)
            .into_iter()
            .map(|(var, coeffs)| (var, coeffs.map(|(_, c)| c).sum()))
            .filter(|(_, c)| *c != ark_bn254::Fr::ZERO)
            .collect()
    }

    pub fn eq(&self, other: &Value) -> Value {
        let self_const = self.expect_constant();
        let other_const = other.expect_constant();
        if self_const == other_const {
            Value::Const(ark_bn254::Fr::ONE)
        } else {
            Value::Const(ark_bn254::Fr::ZERO)
        }
    }
}

#[derive(Clone)]
pub struct R1C {
    pub a: Vec<(usize, ark_bn254::Fr)>,
    pub b: Vec<(usize, ark_bn254::Fr)>,
    pub c: Vec<(usize, ark_bn254::Fr)>,
}

fn field_to_string(c: ark_bn254::Fr) -> String {
    if c == -ark_bn254::Fr::ONE {
        "-1".to_string()
    } else {
        c.to_string()
    }
}

impl Display for R1C {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let a_str = self
            .a
            .iter()
            .map(|(i, c)| format!("{} * v{}", field_to_string(*c), i))
            .collect::<Vec<_>>()
            .join(" + ");
        let b_str = self
            .b
            .iter()
            .map(|(i, c)| format!("{} * v{}", field_to_string(*c), i))
            .collect::<Vec<_>>()
            .join(" + ");
        let c_str = self
            .c
            .iter()
            .map(|(i, c)| format!("{} * v{}", field_to_string(*c), i))
            .collect::<Vec<_>>()
            .join(" + ");

        write!(f, "({}) * ({}) - ({}) = 0", a_str, b_str, c_str)
    }
}

#[derive(Clone)]
pub struct R1CGen {
    result: Vec<R1C>,
    next_witness: usize,
}

impl R1CGen {
    pub fn new() -> Self {
        Self {
            result: vec![],
            next_witness: 1, // 0 is reserved for constant one
        }
    }

    pub fn verify(&self, witness: &[ark_bn254::Fr]) -> bool {
        for r1c in &self.result {
            let a = r1c
                .a
                .iter()
                .map(|(i, c)| c * &witness[*i])
                .sum::<ark_bn254::Fr>();
            let b = r1c
                .b
                .iter()
                .map(|(i, c)| c * &witness[*i])
                .sum::<ark_bn254::Fr>();
            let c = r1c
                .c
                .iter()
                .map(|(i, c)| c * &witness[*i])
                .sum::<ark_bn254::Fr>();
            let success_emoji = if a * b == c { "✅" } else { "❌" };
            println!("VERIFIER {}: a: {}, b: {}, c: {}", success_emoji, a, b, c);
        }
        return true;
    }

    pub fn run<V: Clone>(&mut self, ssa: &SSA<V>) {
        let entry_point = ssa.get_main_id();
        let params = ssa.get_function(entry_point).get_param_types();
        let mut main_params = vec![];
        for value_type in params {
            main_params.push(self.initialize_main_input(&value_type));
        }

        self.run_function(ssa, entry_point, main_params);
    }

    pub fn get_r1cs(self) -> Vec<R1C> {
        self.result
    }

    pub fn get_witness_size(&self) -> usize {
        self.next_witness
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
                Const::Bool(value) => {
                    scope.insert(*value_id, Value::Const(ark_bn254::Fr::from(*value as u64)))
                }
                Const::U32(value) => {
                    scope.insert(*value_id, Value::Const(ark_bn254::Fr::from(*value as u64)))
                }
                Const::Field(value) => scope.insert(*value_id, Value::Const(*value)),
            };
        }

        let mut block_id = entry_block_id;

        loop {
            let block = function.get_block(block_id);
            for instruction in block.get_instructions() {
                match instruction {
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

                    OpCode::AssertEq(_, _) => {
                        todo!();
                    }

                    OpCode::AssertR1C(_, _, _) => {
                        todo!();
                    }

                    OpCode::Constrain(a, b, c) => {
                        let a = scope.get(a).unwrap().expect_linear_combination();
                        let b = scope.get(b).unwrap().expect_linear_combination();
                        let c = scope.get(c).unwrap().expect_linear_combination();
                        self.result.push(R1C { a: a, b: b, c: c });
                    }
                    OpCode::WriteWitness(result, _, _) => {
                        if let Some(result) = result {
                            scope.insert(*result, Value::WitnessVar(self.next_witness()));
                        }
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

                    OpCode::Eq(result, lhs, rhs) => {
                        let lhs = scope.get(lhs).unwrap();
                        let rhs = scope.get(rhs).unwrap();
                        let r = lhs.eq(rhs);
                        scope.insert(*result, r);
                    }

                    OpCode::And(_, _, _) => {
                        todo!();
                    }
                    OpCode::Select(rslot, c, l, r) => {
                        let cond = scope.get(c).unwrap();
                        let l = scope.get(l).unwrap();
                        let r = scope.get(r).unwrap();

                        let res = cond.mul(l).add(&Value::Const(ark_bn254::Fr::ONE).sub(cond).mul(r));
                        scope.insert(*rslot, res);
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
                        .map(|arg| {
                            scope
                                .get(arg)
                                .expect(&format!("expected value {:?}", arg))
                                .clone()
                        })
                        .collect();
                    self.update_scope_with_args(&mut scope, args, &function, *target);
                    block_id = *target;
                }
                Some(Terminator::JmpIf(cond, if_true, if_false)) => {
                    let cond = scope.get(cond).unwrap();
                    let cond = cond.expect_constant();
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

    fn next_witness(&mut self) -> usize {
        let result = self.next_witness;
        self.next_witness += 1;
        result
    }

    fn initialize_main_input<V: Clone>(&mut self, tp: &Type<V>) -> Value {
        match &tp.expr {
            TypeExpr::Bool => Value::WitnessVar(self.next_witness()),
            TypeExpr::U32 => Value::WitnessVar(self.next_witness()),
            TypeExpr::Field => Value::WitnessVar(self.next_witness()),
            TypeExpr::Array(tp, size) => {
                let mut result = vec![];
                for _ in 0..*size {
                    result.push(self.initialize_main_input(tp));
                }
                Value::Array(result)
            }
            _ => panic!("unexpected main params"),
        }
    }
}
