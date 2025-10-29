use std::{cell::RefCell, fmt::Display, rc::Rc};

use crate::compiler::{
    analysis::{
        symbolic_executor::{self, SymbolicExecutor},
        types::TypeInfo,
    },
    ir::r#type::{Type, TypeExpr},
    ssa::{BinaryArithOpKind, BlockId, CmpKind, FunctionId, MemOp, Radix, SSA},
};
use ark_ff::{AdditiveGroup, BigInt, BigInteger, Field, PrimeField};
use itertools::Itertools;
use tracing::{instrument, warn};

// #[derive(Clone, Debug, Copy, PartialEq, PartialOrd, Eq, Ord)]
// pub enum WitnessIndex {
//     PreCommitment(usize),
//     ChallengePower(usize, usize),
//     LookupValueInverse(usize),
//     LookupValueInverseAux(usize),
// }

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

type LC = Vec<(usize, crate::compiler::Field)>;

#[derive(Clone)]
pub struct R1C {
    pub a: LC,
    pub b: LC,
    pub c: LC,
}

#[derive(Clone)]
pub struct LookupConstraint {
    pub table_id: usize,
    pub elements: Vec<LC>,
}

#[derive(Clone)]
pub enum Table {
    Range(u64),
    OfElems(Vec<LC>),
}

fn field_to_string(c: ark_bn254::Fr) -> String {
    if c.into_bigint() > crate::compiler::Field::MODULUS_MINUS_ONE_DIV_TWO {
        format!("-{}", -c)
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
    constraints: Vec<R1C>,
    tables: Vec<Table>,
    lookups: Vec<LookupConstraint>,
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

    fn lookup(
        &mut self,
        target: super::ssa::LookupTarget<Value>,
        keys: Vec<Value>,
        results: Vec<Value>,
    ) {
        match target {
            super::ssa::LookupTarget::Rangecheck(i) => {
                // TODO this will become table resolution logic eventually
                if self.tables.is_empty() {
                    self.tables.push(Table::Range(i as u64))
                } else {
                    match self.tables[0] {
                        Table::Range(i1) => assert_eq!(i1, i as u64, "unsupported"),
                        Table::OfElems(_) => panic!("unsupported"),
                    }
                }
                let els = keys
                    .into_iter()
                    .chain(results.into_iter())
                    .map(|e| e.expect_linear_combination())
                    .collect();
                self.lookups.push(LookupConstraint {
                    table_id: 0,
                    elements: els,
                });
            }
            super::ssa::LookupTarget::Array(_) => todo!("lookups from arrays"),
        }
    }
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
        ctx.constraints.push(R1C { a: a, b: b, c: c });
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
        let check = self_const
            .into_bigint()
            .to_bits_le()
            .iter()
            .skip(max_bits)
            .all(|b| !b);
        assert!(check);
    }

    fn to_radix(
        &self,
        _radix: &Radix<Self>,
        _endianness: crate::compiler::ssa::Endianness,
        _size: usize,
        _out_type: &Type<V>,
        _ctx: &mut R1CGen,
    ) -> Self {
        todo!("ToRadix R1CS generation not yet implemented")
    }
}

pub struct WitnessLayout {
    pub algebraic_size: usize,
    pub multiplicities_size: usize,

    pub challenges_size: usize,

    pub tables_data_size: usize,
    pub lookups_data_size: usize,
}

impl WitnessLayout {
    pub fn algebraic_start(&self) -> usize {
        0
    }

    pub fn algebraic_end(&self) -> usize {
        self.algebraic_size
    }

    pub fn multiplicities_start(&self) -> usize {
        self.algebraic_end()
    }

    pub fn multiplicities_end(&self) -> usize {
        self.multiplicities_start() + self.multiplicities_size
    }

    pub fn challenges_start(&self) -> usize {
        self.multiplicities_end()
    }

    pub fn challenges_end(&self) -> usize {
        self.challenges_start() + self.challenges_size
    }

    pub fn next_challenge(&mut self) -> usize {
        let challenge_id = self.challenges_end();
        self.challenges_size += 1;
        challenge_id
    }

    pub fn tables_data_start(&self) -> usize {
        self.challenges_end()
    }

    pub fn tables_data_end(&self) -> usize {
        self.tables_data_size + self.tables_data_start()
    }

    pub fn next_table_data(&mut self) -> usize {
        let table_data_id = self.tables_data_end();
        self.tables_data_size += 1;
        table_data_id
    }

    pub fn lookups_data_start(&self) -> usize {
        self.tables_data_end()
    }

    pub fn lookups_data_end(&self) -> usize {
        self.lookups_data_size + self.lookups_data_start()
    }

    pub fn next_lookups_data(&mut self) -> usize {
        let lookups_data_id = self.lookups_data_end();
        self.lookups_data_size += 1;
        lookups_data_id
    }

    pub fn size(&self) -> usize {
        self.algebraic_size
            + self.multiplicities_size
            + self.challenges_size
            + self.tables_data_size
            + self.lookups_data_size
    }
}

pub struct ConstraintsLayout {
    pub algebraic_size: usize,
    pub tables_data_size: usize,
    pub lookups_data_size: usize,
}

pub struct R1CS {
    pub witness_layout: WitnessLayout,
    pub constraints_layout: ConstraintsLayout,
    pub constraints: Vec<R1C>,
}

impl R1CGen {
    pub fn new() -> Self {
        Self {
            constraints: vec![],
            next_witness: 1, // 0 is reserved for constant one
            tables: vec![],
            lookups: vec![],
        }
    }

    pub fn verify(&self, witness: &[ark_bn254::Fr]) -> bool {
        for (i, r1c) in self.constraints.iter().enumerate() {
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
        self.constraints
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

    pub fn seal(self) -> R1CS {
        // Algebraic section
        let mut witness_layout = WitnessLayout {
            algebraic_size: self.next_witness,
            multiplicities_size: 0,
            challenges_size: 0,
            tables_data_size: 0,
            lookups_data_size: 0,
        };
        let mut constraints_layout = ConstraintsLayout {
            algebraic_size: self.constraints.len(),
            tables_data_size: 0,
            lookups_data_size: 0,
        };
        let mut result = self.constraints;

        // multiplicities init + compute the needed challenges
        struct TableInfo {
            multiplicities_witness_off: usize,
            table: Table,
            sum_constraint_idx: usize,
        }
        let mut table_infos = vec![];
        let mut max_width = 0;
        for table in self.tables.into_iter() {
            match table {
                Table::Range(len) => {
                    let len = 1 << len;
                    table_infos.push(TableInfo {
                        multiplicities_witness_off: witness_layout.multiplicities_size
                            + witness_layout.algebraic_size,
                        table,
                        sum_constraint_idx: 0,
                    });
                    max_width = max_width.max(1);
                    witness_layout.multiplicities_size += len;
                }
                Table::OfElems(els) => {
                    let len = els.len();
                    table_infos.push(TableInfo {
                        multiplicities_witness_off: witness_layout.multiplicities_size
                            + witness_layout.algebraic_size,
                        table: Table::OfElems(els),
                        sum_constraint_idx: 0,
                    });
                    max_width = max_width.max(2);
                    witness_layout.multiplicities_size += len;
                }
            }
        }

        if table_infos.is_empty() {
            return R1CS {
                witness_layout,
                constraints_layout,
                constraints: result,
            };
        }

        // challenges init
        let alpha = witness_layout.challenges_end();
        witness_layout.challenges_size += 1;
        let beta = if max_width > 1 {
            let beta = witness_layout.challenges_end();
            witness_layout.challenges_size += 1;
            beta
        } else {
            usize::MAX // hoping this crashes soon if used
        };

        // tables contents init
        for table_info in table_infos.iter_mut() {
            match &table_info.table {
                Table::Range(bits) => {
                    // for each element i, we need one witness `y = mᵢ / (α - i)`
                    // and one constraint saying `y * (α - i) - mᵢ = 0`
                    let len = 1 << bits;
                    let mut sum_lhs: LC = vec![];
                    for i in 0..len {
                        let y = witness_layout.next_table_data();
                        let m = table_info.multiplicities_witness_off + i;
                        result.push(R1C {
                            a: vec![(y, ark_bn254::Fr::ONE)],
                            b: vec![
                                (alpha, ark_bn254::Fr::ONE),
                                (0, -crate::compiler::Field::from(i as u64)),
                            ],
                            c: vec![(m, ark_bn254::Fr::ONE)],
                        });
                        sum_lhs.push((y, ark_bn254::Fr::ONE));
                    }
                    result.push(R1C {
                        a: sum_lhs,
                        b: vec![(0, ark_bn254::Fr::ONE)],
                        c: vec![], // this is prepared for the looked up values to come into
                    });
                    table_info.sum_constraint_idx = result.len() - 1;
                }
                Table::OfElems(els) => {
                    // for each element (i, v), we need two witness/constraint pairs:
                    // -> x = β * v, with the constraint `β * v - x = 0`
                    // -> y = mᵢ / (α - i - x), with the constraint `y * (α - i - x) - mᵢ = 0`
                    let mut sum_lhs: LC = vec![];
                    for (i, v) in els.iter().enumerate() {
                        let x = witness_layout.next_table_data();
                        let y = witness_layout.next_table_data();
                        let m = table_info.multiplicities_witness_off + i;
                        result.push(R1C {
                            a: vec![(beta, crate::compiler::Field::ONE)],
                            b: v.clone(),
                            c: vec![(x, -crate::compiler::Field::ONE)],
                        });
                        result.push(R1C {
                            a: vec![(y, ark_bn254::Fr::ONE)],
                            b: vec![
                                (alpha, ark_bn254::Fr::ONE),
                                (0, -crate::compiler::Field::from(i as u64)),
                                (x, -crate::compiler::Field::ONE),
                            ],
                            c: vec![(m, crate::compiler::Field::ONE)],
                        });
                        sum_lhs.push((y, ark_bn254::Fr::ONE));
                    }
                    result.push(R1C {
                        a: sum_lhs,
                        b: vec![(0, ark_bn254::Fr::ONE)],
                        c: vec![], // this is prepared for the looked up values to come into
                    });
                    table_info.sum_constraint_idx = result.len() - 1;
                }
            }
        }

        constraints_layout.tables_data_size = result.len() - constraints_layout.algebraic_size;

        // lookups init
        for lookup in self.lookups.into_iter() {
            if lookup.elements.len() >= 2 {
                todo!("wide tables");
            }

            let y = witness_layout.next_lookups_data();
            let mut b = vec![(alpha, ark_bn254::Fr::ONE)];
            for (w, coeff) in lookup.elements[0].iter() {
                b.push((*w, -*coeff));
            }
            result.push(R1C {
                a: vec![(y, ark_bn254::Fr::ONE)],
                b,
                c: vec![(0, ark_bn254::Fr::ONE)],
            });

            result[table_infos[lookup.table_id].sum_constraint_idx]
                .c
                .push((y, ark_bn254::Fr::ONE));
        }

        constraints_layout.lookups_data_size =
            result.len() - constraints_layout.algebraic_size - constraints_layout.tables_data_size;

        return R1CS {
            witness_layout,
            constraints_layout,
            constraints: result,
        };
    }
}

impl R1CS {
    pub fn compute_derivatives(
        &self,
        coeffs: &[crate::compiler::Field],
        res_a: &mut [crate::compiler::Field],
        res_b: &mut [crate::compiler::Field],
        res_c: &mut [crate::compiler::Field],
    ) {
        for (r1c, coeff) in self.constraints.iter().zip(coeffs.iter()) {
            for (a_ix, a_coeff) in r1c.a.iter() {
                res_a[*a_ix] += *a_coeff * *coeff;
            }
            for (b_ix, b_coeff) in r1c.b.iter() {
                res_b[*b_ix] += *b_coeff * *coeff;
            }
            for (c_ix, c_coeff) in r1c.c.iter() {
                res_c[*c_ix] += *c_coeff * *coeff;
            }
        }
    }
}
