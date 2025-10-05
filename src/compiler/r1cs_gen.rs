use std::{cell::RefCell, fmt::Display, rc::Rc};

use crate::compiler::{
    analysis::{symbolic_executor::{self, SymbolicExecutor}, types::TypeInfo},
    ir::r#type::{Type, TypeExpr},
    ssa::{BinaryArithOpKind, BlockId, CmpKind, FunctionId, MemOp, SSA},
};
use ark_ff::{AdditiveGroup, BigInt, BigInteger, Field, PrimeField};
use itertools::Itertools;
use tracing::{instrument, warn};

#[derive(Clone, Debug)]
pub enum Value {
    Const(ark_bn254::Fr),
    WitnessVar(usize),
    Arith(BinaryArithOpKind, Rc<Value>, Rc<Value>),
    Array(Rc<Vec<Value>>),
    Ptr(Rc<RefCell<Value>>),
    Invalid,
}

impl Value {
    pub fn add(&self, other: &Value) -> Value {
        match (self, other) {
            (Value::Const(lhs), Value::Const(rhs)) => Value::Const(lhs + rhs),
            (lhs, rhs) => Value::Arith(
                BinaryArithOpKind::Add,
                Rc::new(lhs.clone()),
                Rc::new(rhs.clone()),
            ),
        }
    }

    pub fn sub(&self, other: &Value) -> Value {
        match (self, other) {
            (Value::Const(lhs), Value::Const(rhs)) => Value::Const(lhs - rhs),
            (lhs, rhs) => Value::Arith(
                BinaryArithOpKind::Sub,
                Rc::new(lhs.clone()),
                Rc::new(rhs.clone()),
            ),
        }
    }

    pub fn div(&self, other: &Value) -> Value {
        match (self, other) {
            (Value::Const(lhs), Value::Const(rhs)) => Value::Const(lhs / rhs),
            (lhs, rhs) => Value::Arith(
                BinaryArithOpKind::Div,
                Rc::new(lhs.clone()),
                Rc::new(rhs.clone()),
            ),
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
            (lhs, rhs) => Value::Arith(
                BinaryArithOpKind::Mul,
                Rc::new(lhs.clone()),
                Rc::new(rhs.clone()),
            ),
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

    pub fn expect_array(&self) -> Rc<Vec<Value>> {
        match self {
            Value::Array(array) => array.clone(),
            _ => panic!("expected array"),
        }
    }

    pub fn expect_linear_combination(&self) -> Vec<(usize, ark_bn254::Fr)> {
        let first = match self {
            Value::Const(c) => vec![(0, *c)],
            Value::Arith(BinaryArithOpKind::Mul, l, r) => match (&**l, &**r) {
                (Value::Const(c), other) | (other, Value::Const(c)) => {
                    let mut r = other.expect_linear_combination();
                    for (_, cx) in r.iter_mut() {
                        *cx *= *c;
                    }
                    r
                }
                _ => panic!("expected linear combination, got arb mul"),
            },
            Value::Arith(BinaryArithOpKind::Add, l, r) => {
                let mut l = l.expect_linear_combination();
                let r = r.expect_linear_combination();
                l.extend(r);
                l
            }
            Value::Arith(BinaryArithOpKind::Sub, l, r) => {
                let mut l = l.expect_linear_combination();
                let r = r.expect_linear_combination();
                let r_negated: Vec<_> = r.iter().map(|(i, c)| (*i, -*c)).collect();
                l.extend(r_negated);
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

impl<V: Clone> symbolic_executor::Context<Value, V> for R1CGen {
    fn on_call(
        &mut self,
        _func: FunctionId,
        _params: &mut [Value],
        _param_types: &[&Type<V>],
    ) -> Option<Vec<Value>> {
        None
    }

    fn on_return(&mut self, _returns: &mut [Value], _return_types: &[Type<V>]) {}

    fn on_jmp(&mut self, _target: BlockId, _params: &mut [Value], _param_types: &[&Type<V>]) {}
}

impl<V: Clone> symbolic_executor::Value<R1CGen, V> for Value {
    fn cmp(&self, b: &Self, cmp_kind: CmpKind, _out_type: &Type<V>, _ctx: &mut R1CGen) -> Self {
        match cmp_kind {
            CmpKind::Eq => self.eq(b),
            CmpKind::Lt => self.lt(b),
        }
    }

    fn arith(
        &self,
        b: &Self,
        binary_arith_op_kind: BinaryArithOpKind,
        _out_type: &Type<V>,
        _ctx: &mut R1CGen,
    ) -> Self {
        match binary_arith_op_kind {
            BinaryArithOpKind::Add => self.add(b),
            BinaryArithOpKind::Sub => self.sub(b),
            BinaryArithOpKind::Mul => self.mul(b),
            BinaryArithOpKind::Div => self.div(b),
            BinaryArithOpKind::And => {
                let a = self.expect_u32();
                let b = b.expect_u32();
                Value::Const(ark_bn254::Fr::from(a & b))
            }
        }
    }

    fn assert_eq(&self, other: &Self, _ctx: &mut R1CGen) {
        assert_eq!(self.expect_constant(), other.expect_constant());
    }

    fn assert_r1c(a: &Self, b: &Self, c: &Self, _ctx: &mut R1CGen) {
        let a = a.expect_constant();
        let b = b.expect_constant();
        let c = c.expect_constant();
        assert!(a * b == c);
    }

    fn array_get(&self, index: &Self, _out_type: &Type<V>, _ctx: &mut R1CGen) -> Self {
        let array = self.expect_array();
        let index = index.expect_u32();
        let value = array[index as usize].clone();
        value
    }

    fn array_set(
        &self,
        index: &Self,
        value: &Self,
        _out_type: &Type<V>,
        _ctx: &mut R1CGen,
    ) -> Self {
        let array = self.expect_array();
        let index = index.expect_u32();
        let mut new_array = array.as_ref().clone();
        new_array[index as usize] = value.clone();
        Value::Array(Rc::new(new_array))
    }

    fn truncate(&self, _from: usize, to: usize, _out_type: &Type<V>, _ctx: &mut R1CGen) -> Self {
        let new_value = self
            .expect_constant()
            .into_bigint()
            .to_bits_le()
            .iter()
            .take(to)
            .cloned()
            .collect::<Vec<_>>();
        Value::Const(ark_bn254::Fr::from_bigint(BigInt::from_bits_le(&new_value)).unwrap())
    }

    fn cast(
        &self,
        _cast_target: &super::ssa::CastTarget,
        _out_type: &Type<V>,
        _ctx: &mut R1CGen,
    ) -> Self {
        self.clone()
    }

    fn constrain(a: &Self, b: &Self, c: &Self, ctx: &mut R1CGen) {
        let a = a.expect_linear_combination();
        let b = b.expect_linear_combination();
        let c = c.expect_linear_combination();
        ctx.result.push(R1C { a: a, b: b, c: c });
    }

    fn to_bits(
        &self,
        endianness: super::ssa::Endianness,
        size: usize,
        _out_type: &Type<V>,
        _ctx: &mut R1CGen,
    ) -> Self {
        let value_const = self.expect_constant();
        let mut bits = value_const.into_bigint().to_bits_le();
        // Truncate or pad to the desired output size
        if bits.len() > size {
            bits.truncate(size);
        } else {
            while bits.len() < size {
                bits.push(false);
            }
        }
        // Handle endianness
        let final_bits = match endianness {
            crate::compiler::ssa::Endianness::Little => bits,
            crate::compiler::ssa::Endianness::Big => {
                let mut reversed = bits;
                reversed.reverse();
                reversed
            }
        };
        // Convert bits to array of field elements (0 or 1)
        let mut bit_values = Vec::new();
        for bit in final_bits {
            let bit_value = if bit {
                Value::Const(ark_bn254::Fr::from(1u128))
            } else {
                Value::Const(ark_bn254::Fr::from(0u128))
            };
            bit_values.push(bit_value);
        }
        Value::Array(Rc::new(bit_values))
    }

    fn not(&self, out_type: &Type<V>, _ctx: &mut R1CGen) -> Self {
        let value_const = self.expect_constant();
        let bits = value_const.into_bigint().to_bits_le();
        let bit_size = out_type.get_bit_size();
        let mut negated_bits = Vec::new();
        for i in 0..bit_size {
            let bit = if i < bits.len() { bits[i] } else { false };
            negated_bits.push(!bit);
        }
        Value::Const(ark_bn254::Fr::from_bigint(BigInt::from_bits_le(&negated_bits)).unwrap())
    }

    fn of_u(_s: usize, v: u128, _ctx: &mut R1CGen) -> Self {
        Value::Const(ark_bn254::Fr::from(v))
    }

    fn of_field(f: super::Field, _ctx: &mut R1CGen) -> Self {
        Value::Const(ark_bn254::Fr::from(f))
    }

    fn mk_array(
        a: Vec<Self>,
        _ctx: &mut R1CGen,
        _seq_type: super::ssa::SeqType,
        _elem_type: &Type<V>,
    ) -> Self {
        Value::Array(Rc::new(a))
    }

    fn alloc(_ctx: &mut R1CGen) -> Self {
        Value::Ptr(Rc::new(RefCell::new(Value::Invalid)))
    }

    fn ptr_write(&self, value: &Self, _ctx: &mut R1CGen) {
        let ptr = self.expect_ptr();
        *ptr.borrow_mut() = value.clone();
    }

    fn ptr_read(&self, _out_type: &Type<V>, _ctx: &mut R1CGen) -> Self {
        let ptr = self.expect_ptr();
        let value = ptr.borrow().clone();
        value
    }

    fn expect_constant_bool(&self, _ctx: &mut R1CGen) -> bool {
        self.expect_constant() == ark_bn254::Fr::ONE
    }

    fn select(&self, if_t: &Self, if_f: &Self, _out_type: &Type<V>, _ctx: &mut R1CGen) -> Self {
        self.mul(if_t)
            .add(&Value::Const(ark_bn254::Fr::ONE).sub(self).mul(if_f))
    }

    fn write_witness(&self, _tp: Option<&Type<V>>, ctx: &mut R1CGen) -> Self {
        let witness_var = ctx.next_witness();
        Value::WitnessVar(witness_var)
    }

    fn fresh_witness(ctx: &mut R1CGen) -> Self {
        let witness_var = ctx.next_witness();
        Value::WitnessVar(witness_var)
    }

    fn mem_op(&self, _kind: MemOp, _ctx: &mut R1CGen) {}

    fn rangecheck(&self, max_bits: usize, _ctx: &mut R1CGen) {
        let self_const = self.expect_constant();
        let check = self_const.into_bigint().to_bits_le().iter().skip(max_bits).all(|b| !b);
        assert!(check);
    }

    fn to_radix(
        &self,
        _radix: &Self,
        _endianness: crate::compiler::ssa::Endianness,
        _size: usize,
        _out_type: &Type<V>,
        _ctx: &mut R1CGen,
    ) -> Self {
        todo!("ToRadix R1CS generation not yet implemented")
    }
}

impl R1CGen {
    pub fn new() -> Self {
        Self {
            result: vec![],
            next_witness: 1, // 0 is reserved for constant one
        }
    }

    pub fn verify(&self, witness: &[ark_bn254::Fr]) -> bool {
        for (i, r1c) in self.result.iter().enumerate() {
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
            if a * b != c {
                warn!(message = %"R1CS constraint failed to verify", index = i);
                return false;
            }
        }
        return true;
    }

    #[instrument(skip_all, name = "R1CGen::run")]
    pub fn run<V: Clone>(&mut self, ssa: &SSA<V>, type_info: &TypeInfo<V>) {
        let entry_point = ssa.get_main_id();
        let params = ssa.get_function(entry_point).get_param_types();
        let mut main_params = vec![];
        for value_type in params {
            main_params.push(self.initialize_main_input(&value_type));
        }

        let executor = SymbolicExecutor::new();
        executor.run(ssa, type_info, entry_point, main_params, self);
    }

    pub fn get_r1cs(self) -> Vec<R1C> {
        self.result
    }

    pub fn get_witness_size(&self) -> usize {
        self.next_witness
    }

    fn next_witness(&mut self) -> usize {
        let result = self.next_witness;
        self.next_witness += 1;
        result
    }

    fn initialize_main_input<V: Clone>(&mut self, tp: &Type<V>) -> Value {
        match &tp.expr {
            TypeExpr::U(_) => Value::WitnessVar(self.next_witness()),
            TypeExpr::Field => Value::WitnessVar(self.next_witness()),
            TypeExpr::Array(tp, size) => {
                let mut result = vec![];
                for _ in 0..*size {
                    result.push(self.initialize_main_input(tp));
                }
                Value::Array(Rc::new(result))
            }
            _ => panic!("unexpected main params"),
        }
    }
}
