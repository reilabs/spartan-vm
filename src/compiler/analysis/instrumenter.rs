use std::{cell::RefCell, collections::HashMap, rc::Rc};

use ark_ff::{AdditiveGroup, BigInt, BigInteger, PrimeField};
use itertools::Itertools;
use tracing::{Level, instrument};

use crate::compiler::{
    Field,
    ir::r#type::{Type, TypeExpr},
    ssa::{BinaryArithOpKind, CastTarget, CmpKind, Const, Endianness, FunctionId, SSA, Terminator},
    taint_analysis::ConstantTaint,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ValueSignature {
    U(usize, u128),
    Field(Field),
    Array(Vec<ValueSignature>),
    PointerTo(Box<ValueSignature>),
    FWitness,
    UWitness(usize),
}

impl ValueSignature {
    pub fn to_value(&self) -> Value {
        match self {
            ValueSignature::U(size, val) => Value::U(*size, *val),
            ValueSignature::Field(field) => Value::Field(field.clone()),
            ValueSignature::Array(vals) => {
                Value::Array(vals.iter().map(|v| v.to_value()).collect())
            }
            ValueSignature::PointerTo(val) => Value::Pointer(Rc::new(RefCell::new(val.to_value()))),
            ValueSignature::FWitness => Value::FWitness,
            ValueSignature::UWitness(s) => Value::UWitness(*s),
        }
    }

    pub fn pretty_print(&self) -> String {
        match self {
            ValueSignature::U(_, v) => format!("{v}"),
            ValueSignature::Field(f) => format!("{}", f),
            ValueSignature::Array(_) => "[...]".to_string(),
            ValueSignature::PointerTo(p) => format!("&({})", p.as_ref().pretty_print()),
            ValueSignature::FWitness => "W".to_string(),
            ValueSignature::UWitness(_) => "W".to_string(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    U(usize, u128),
    Field(Field),
    Array(Vec<Value>),
    Pointer(Rc<RefCell<Value>>),
    FWitness,
    UWitness(usize),
}

impl Value {
    fn cmp_op(
        &self,
        b: &Value,
        cmp_kind: &crate::compiler::ssa::CmpKind,
        instrumenter: &mut dyn OpInstrumenter,
    ) -> Value {
        match (self, b) {
            (Value::U(_, a), Value::U(_, b)) => match cmp_kind {
                CmpKind::Eq => Value::U(1, if a == b { 1 } else { 0 }),
                CmpKind::Lt => Value::U(1, if a < b { 1 } else { 0 }),
            },
            (Value::Field(a), Value::Field(b)) => match cmp_kind {
                CmpKind::Eq => Value::U(1, if a == b { 1 } else { 0 }),
                CmpKind::Lt => Value::U(1, if a < b { 1 } else { 0 }),
            },
            (Value::UWitness(s), _) | (_, Value::UWitness(s)) => {
                todo!();
            }
            (Value::FWitness, _) | (_, Value::FWitness) => {
                todo!();
            }
            (_, _) => {
                panic!("Cannot compare {:?} and {:?}", self, b);
            }
        }
    }

    fn binary_arith_op(
        &self,
        b: &Value,
        binary_arith_op_kind: &crate::compiler::ssa::BinaryArithOpKind,
        instrumenter: &mut dyn OpInstrumenter,
    ) -> Value {
        match (self, b) {
            (Value::U(s, a), Value::U(_, b)) => match binary_arith_op_kind {
                BinaryArithOpKind::Add => Value::U(*s, a + b),
                BinaryArithOpKind::Sub => Value::U(*s, a - b),
                BinaryArithOpKind::Mul => Value::U(*s, a * b),
                BinaryArithOpKind::Div => Value::U(*s, a / b),
                BinaryArithOpKind::And => Value::U(*s, a & b),
            },
            (Value::Field(a), Value::Field(b)) => match binary_arith_op_kind {
                BinaryArithOpKind::Add => Value::Field(a + b),
                BinaryArithOpKind::Sub => Value::Field(a - b),
                BinaryArithOpKind::Mul => Value::Field(a * b),
                BinaryArithOpKind::Div => Value::Field(a / b),
                BinaryArithOpKind::And => todo!(),
            },
            (Value::FWitness, Value::FWitness) => match binary_arith_op_kind {
                BinaryArithOpKind::Add => Value::FWitness,
                BinaryArithOpKind::Sub => Value::FWitness,
                BinaryArithOpKind::Mul => {
                    instrumenter.record_constraints(1);
                    Value::FWitness
                }
                BinaryArithOpKind::Div => {
                    instrumenter.record_constraints(1);
                    Value::FWitness
                }
                BinaryArithOpKind::And => todo!(),
            },
            (Value::FWitness, Value::Field(a)) | (Value::Field(a), Value::FWitness) => {
                match binary_arith_op_kind {
                    BinaryArithOpKind::Mul => {
                        if a == &Field::ZERO {
                            Value::Field(Field::ZERO)
                        } else {
                            Value::FWitness
                        }
                    }
                    _ => Value::FWitness,
                }
            }
            (Value::UWitness(s), _) | (_, Value::UWitness(s)) => {
                todo!();
            }
            (_, _) => panic!("Cannot perform binary arithmetic on {:?} and {:?}", self, b),
        }
    }

    fn blind_from(&mut self, tp: &Type<ConstantTaint>) {
        match (&self, tp.get_annotation(), &tp.expr) {
            (Value::UWitness(_), _, _) => {}
            (Value::FWitness, _, _) => {}
            (Value::U(s, _), ConstantTaint::Witness, _) => *self = Value::UWitness(*s),
            (Value::U { .. }, _, _) => {}
            (Value::Field { .. }, ConstantTaint::Witness, _) => *self = Value::FWitness,
            (Value::Field { .. }, _, _) => {}
            (Value::Array(_), ConstantTaint::Witness, _) => {
                panic!("Witness arrays not supported yet")
            }
            (Value::Array(vals), _, tp) => {
                let item_tp = match tp {
                    TypeExpr::Array(tp, _) => tp,
                    TypeExpr::Slice(tp) => tp,
                    _ => panic!("Unexpected array type: {:?}", tp),
                };
                match self {
                    Value::Array(vals) => {
                        for val in vals {
                            val.blind_from(&item_tp);
                        }
                    }
                    _ => panic!("Unexpected array type: {:?}", tp),
                }
            }
            (Value::Pointer(_), ConstantTaint::Witness, _) => {
                panic!("Witness pointers not supported yet");
            }
            (Value::Pointer(val), ConstantTaint::Pure, tp) => {
                let item_tp = match tp {
                    TypeExpr::Ref(tp) => tp,
                    _ => panic!("Unexpected pointer type: {:?}", tp),
                };
                val.borrow_mut().blind_from(&item_tp);
            }
        }
    }

    fn make_unspecialized_sig(&self, tp: &Type<ConstantTaint>) -> ValueSignature {
        match (self, tp.get_annotation(), &tp.expr) {
            (Value::UWitness(s), _, _) => ValueSignature::UWitness(*s),
            (Value::FWitness, _, _) => ValueSignature::FWitness,
            (Value::U(s, v), ConstantTaint::Pure, _) => ValueSignature::U(*s, *v),
            (Value::U(s, _), ConstantTaint::Witness, _) => ValueSignature::UWitness(*s),
            (Value::Field(f), ConstantTaint::Pure, _) => ValueSignature::Field(f.clone()),
            (Value::Field(f), ConstantTaint::Witness, _) => ValueSignature::FWitness,
            (Value::Array(vals), ConstantTaint::Pure, tp) => {
                let item_tp = match tp {
                    TypeExpr::Array(tp, _) => tp,
                    TypeExpr::Slice(tp) => tp,
                    _ => panic!("Unexpected array type: {:?}", tp),
                };
                ValueSignature::Array(
                    vals.iter()
                        .map(|v| v.make_unspecialized_sig(&item_tp))
                        .collect(),
                )
            }
            (Value::Array(_), ConstantTaint::Witness, _) => {
                panic!("Witness arrays not supported yet")
            }
            (Value::Pointer(val), ConstantTaint::Pure, tp) => {
                let item_tp = match tp {
                    TypeExpr::Ref(tp) => tp,
                    _ => panic!("Unexpected pointer type: {:?}", tp),
                };
                ValueSignature::PointerTo(Box::new(val.borrow().make_unspecialized_sig(&item_tp)))
            }
            (Value::Pointer(_), ConstantTaint::Witness, _) => {
                panic!("Witness pointers not supported yet")
            }
        }
    }

    fn assert_eq(&self, other: &Value, instrumenter: &mut dyn OpInstrumenter) {
        if self.is_witness() || other.is_witness() {
            instrumenter.record_constraints(1);
        }
    }

    fn is_witness(&self) -> bool {
        match self {
            Value::UWitness(_) => true,
            Value::FWitness => true,
            _ => false,
        }
    }

    fn array_get(&self, index: &Value, _instrumenter: &mut dyn OpInstrumenter) -> Value {
        match (self, index) {
            (Value::Array(vals), Value::U(_, index)) => vals[*index as usize].clone(),
            _ => panic!(
                "Cannot get array element from {:?} with index {:?}",
                self, index
            ),
        }
    }

    fn array_set(
        &self,
        index: &Value,
        value: &Value,
        _instrumenter: &mut dyn OpInstrumenter,
    ) -> Value {
        match (self, index, value) {
            (Value::Array(vals), Value::U(_, index), value) => {
                let mut new_vals = vals.clone();
                new_vals[*index as usize] = value.clone();
                Value::Array(new_vals)
            }
            _ => panic!(
                "Cannot set array element of {:?} with index {:?} to {:?}",
                self, index, value
            ),
        }
    }

    fn truncate_op(
        &self,
        _from: usize,
        to: usize,
        _instrumenter: &mut dyn OpInstrumenter,
    ) -> Value {
        match self {
            Value::U(_, v) => Value::U(to, v & ((1 << to) - 1)),
            Value::Field(f) => {
                let bits = f
                    .into_bigint()
                    .to_bits_le()
                    .into_iter()
                    .take(to)
                    .collect::<Vec<_>>();
                let r = Field::from_bigint(BigInt::from_bits_le(&bits));
                Value::Field(r.unwrap())
            }
            _ => panic!("Cannot truncate {:?}", self),
        }
    }

    fn cast_op(
        &self,
        cast_target: &crate::compiler::ssa::CastTarget,
        _instrumenter: &mut dyn OpInstrumenter,
    ) -> Value {
        match (self, cast_target) {
            (Value::U(_, v), CastTarget::U(s2)) => Value::U(*s2, *v),
            (Value::U(s, v), CastTarget::Field) => Value::Field(Field::from(*v)),
            (Value::Field(f), CastTarget::Field) => Value::Field(f.clone()),
            (Value::Field(f), CastTarget::U(s)) => {
                let bigint = f.into_bigint();

                Value::U(*s, bigint.0[0] as u128 | ((bigint.0[1] as u128) << 64))
            }
            _ => panic!("Cannot cast {:?} to {:?}", self, cast_target),
        }
    }

    fn constrain(a: &Value, b: &Value, c: &Value, instrumenter: &mut dyn OpInstrumenter) {
        if a.is_witness() || b.is_witness() || c.is_witness() {
            instrumenter.record_constraints(1);
        }
    }

    fn to_bits(
        &self,
        endianness: &crate::compiler::ssa::Endianness,
        size: usize,
        instrumenter: &mut dyn OpInstrumenter,
    ) -> Value {
        match self {
            Value::U(_, v) => {
                let mut r = vec![];
                for i in 0..size {
                    let bit = (v >> i) & 1;
                    let bit = Value::U(1, bit);
                    r.push(bit);
                }
                if *endianness == Endianness::Big {
                    r.reverse();
                }
                Value::Array(r)
            }
            Value::Field(f) => {
                let bigint = f.into_bigint();
                let bits = bigint.to_bits_le().into_iter().take(size);
                let mut bits = bits.map(|b| Value::U(1, b as u128)).collect::<Vec<_>>();
                if *endianness == Endianness::Big {
                    bits.reverse();
                }
                Value::Array(bits)
            }
            _ => panic!("Cannot convert {:?} to bits", self),
        }
    }

    fn not_op(&self, _instrumenter: &mut dyn OpInstrumenter) -> Value {
        match self {
            Value::U(s, v) => Value::U(*s, !v),
            _ => panic!("Cannot perform not operation on {:?}", self),
        }
    }
}

#[derive(Debug, Clone)]
pub struct SpecSplitValue {
    unspecialized: Value,
    specialized: Value,
}

impl SpecSplitValue {
    fn cmp_op(
        &self,
        b: &SpecSplitValue,
        cmp_kind: &crate::compiler::ssa::CmpKind,
        instrumenter: &mut dyn FunctionInstrumenter,
    ) -> SpecSplitValue {
        let unspecialized =
            self.unspecialized
                .cmp_op(&b.unspecialized, cmp_kind, instrumenter.get_unspecialized());
        let specialized =
            self.specialized
                .cmp_op(&b.specialized, cmp_kind, instrumenter.get_specialized());
        SpecSplitValue {
            unspecialized,
            specialized,
        }
    }

    fn binary_arith_op(
        &self,
        b: &SpecSplitValue,
        binary_arith_op_kind: &crate::compiler::ssa::BinaryArithOpKind,
        instrumenter: &mut dyn FunctionInstrumenter,
    ) -> SpecSplitValue {
        let unspecialized = self.unspecialized.binary_arith_op(
            &b.unspecialized,
            binary_arith_op_kind,
            instrumenter.get_unspecialized(),
        );
        let specialized = self.specialized.binary_arith_op(
            &b.specialized,
            binary_arith_op_kind,
            instrumenter.get_specialized(),
        );
        SpecSplitValue {
            unspecialized,
            specialized,
        }
    }

    fn cast_op(
        &self,
        cast_target: &crate::compiler::ssa::CastTarget,
        instrumenter: &mut dyn FunctionInstrumenter,
    ) -> SpecSplitValue {
        SpecSplitValue {
            unspecialized: self
                .unspecialized
                .cast_op(cast_target, instrumenter.get_unspecialized()),
            specialized: self
                .specialized
                .cast_op(cast_target, instrumenter.get_specialized()),
        }
    }

    fn truncate_op(
        &self,
        from: usize,
        to: usize,
        instrumenter: &mut dyn FunctionInstrumenter,
    ) -> SpecSplitValue {
        SpecSplitValue {
            unspecialized: self.unspecialized.truncate_op(
                from,
                to,
                instrumenter.get_unspecialized(),
            ),
            specialized: self
                .specialized
                .truncate_op(from, to, instrumenter.get_specialized()),
        }
    }

    fn not_op(&self, instrumenter: &mut dyn FunctionInstrumenter) -> SpecSplitValue {
        SpecSplitValue {
            unspecialized: self.unspecialized.not_op(instrumenter.get_unspecialized()),
            specialized: self.specialized.not_op(instrumenter.get_specialized()),
        }
    }

    fn ptr_write(&self, val: SpecSplitValue, instrumenter: &mut dyn FunctionInstrumenter) {
        todo!()
    }

    fn ptr_read(&self, instrumenter: &mut dyn FunctionInstrumenter) -> SpecSplitValue {
        todo!()
    }

    fn mk_array(values: Vec<SpecSplitValue>) -> SpecSplitValue {
        let (uns, spec) = values
            .into_iter()
            .map(|v| (v.unspecialized, v.specialized))
            .unzip();
        SpecSplitValue {
            unspecialized: Value::Array(uns),
            specialized: Value::Array(spec),
        }
    }

    fn blind_unspecialized_from(&mut self, tp: &Type<ConstantTaint>) {
        self.unspecialized.blind_from(tp);
    }

    fn blind_from(&mut self, tp: &Type<ConstantTaint>) {
        self.unspecialized.blind_from(tp);
        self.specialized.blind_from(tp);
    }

    fn assert_r1c(
        a: SpecSplitValue,
        b: SpecSplitValue,
        c: SpecSplitValue,
        instrumenter: &mut dyn FunctionInstrumenter,
    ) {
        todo!()
    }

    fn array_get(
        &self,
        i: SpecSplitValue,
        instrumenter: &mut dyn FunctionInstrumenter,
    ) -> SpecSplitValue {
        SpecSplitValue {
            unspecialized: self
                .unspecialized
                .array_get(&i.unspecialized, instrumenter.get_unspecialized()),
            specialized: self
                .specialized
                .array_get(&i.specialized, instrumenter.get_specialized()),
        }
    }

    fn array_set(
        &self,
        i: SpecSplitValue,
        v: SpecSplitValue,
        instrumenter: &mut dyn FunctionInstrumenter,
    ) -> SpecSplitValue {
        SpecSplitValue {
            unspecialized: self.unspecialized.array_set(
                &i.unspecialized,
                &v.unspecialized,
                instrumenter.get_unspecialized(),
            ),
            specialized: self.specialized.array_set(
                &i.specialized,
                &v.specialized,
                instrumenter.get_specialized(),
            ),
        }
    }

    fn select(
        &self,
        if_t: SpecSplitValue,
        if_f: SpecSplitValue,
        instrumenter: &mut dyn FunctionInstrumenter,
    ) -> SpecSplitValue {
        todo!()
    }

    fn constrain(
        a: SpecSplitValue,
        b: SpecSplitValue,
        c: SpecSplitValue,
        instrumenter: &mut dyn FunctionInstrumenter,
    ) {
        Value::constrain(
            &a.unspecialized,
            &b.unspecialized,
            &c.unspecialized,
            instrumenter.get_unspecialized(),
        );
        Value::constrain(
            &a.specialized,
            &b.specialized,
            &c.specialized,
            instrumenter.get_specialized(),
        );
    }

    fn assert_eq(
        a: SpecSplitValue,
        b: SpecSplitValue,
        instrumenter: &mut dyn FunctionInstrumenter,
    ) {
        a.specialized
            .assert_eq(&b.specialized, instrumenter.get_specialized());
        a.unspecialized
            .assert_eq(&b.unspecialized, instrumenter.get_unspecialized());
    }

    fn to_bits(
        &self,
        endianness: &crate::compiler::ssa::Endianness,
        size: usize,
        instrumenter: &mut dyn FunctionInstrumenter,
    ) -> SpecSplitValue {
        SpecSplitValue {
            unspecialized: self.unspecialized.to_bits(
                endianness,
                size,
                instrumenter.get_unspecialized(),
            ),
            specialized: self
                .specialized
                .to_bits(endianness, size, instrumenter.get_specialized()),
        }
    }

    fn make_unspecialized_sig(&self, tp: &Type<ConstantTaint>) -> ValueSignature {
        self.unspecialized.make_unspecialized_sig(tp)
    }

    fn expect_constant_bool(&self) -> bool {
        match (&self.unspecialized, &self.specialized) {
            (Value::U(1, v), Value::U(1, v2)) => {
                assert_eq!(*v, *v2);
                *v != 0
            }
            _ => panic!(
                "Expected constant bool, got {:?} and {:?}",
                self.unspecialized, self.specialized
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FunctionSignature {
    id: FunctionId,
    params: Vec<ValueSignature>,
}

impl FunctionSignature {
    pub fn pretty_print(&self, ssa: &SSA<ConstantTaint>) -> String {
        let fn_body = ssa.get_function(self.id);
        let name = fn_body.get_name();
        let params = self
            .params
            .iter()
            .map(ValueSignature::pretty_print)
            .collect::<Vec<_>>()
            .join(", ");
        format!("{}({})", name, params)
    }
}

trait OpInstrumenter {
    fn record_constraints(&mut self, number: usize);
}

trait FunctionInstrumenter {
    fn get_specialized(&mut self) -> &mut dyn OpInstrumenter;
    fn get_unspecialized(&mut self) -> &mut dyn OpInstrumenter;
    fn record_call(&mut self, sig: FunctionSignature);
    fn seal(self: Box<Self>) -> FunctionCost;
}

#[derive(Debug, Clone)]
struct Instrumenter {
    constraints: usize,
}

impl OpInstrumenter for Instrumenter {
    fn record_constraints(&mut self, number: usize) {
        self.constraints += number;
    }
}

#[derive(Debug, Clone)]
pub struct FunctionCost {
    calls: HashMap<FunctionSignature, usize>,
    raw: Instrumenter,
    specialized: Instrumenter,
}

impl FunctionInstrumenter for FunctionCost {
    fn get_specialized(&mut self) -> &mut dyn OpInstrumenter {
        &mut self.specialized
    }

    fn get_unspecialized(&mut self) -> &mut dyn OpInstrumenter {
        &mut self.raw
    }

    fn record_call(&mut self, sig: FunctionSignature) {
        *self.calls.entry(sig).or_insert(0) += 1;
    }

    fn seal(self: Box<Self>) -> FunctionCost {
        *self
    }
}

pub struct DummyInstrumenter {}

impl FunctionInstrumenter for DummyInstrumenter {
    fn get_specialized(&mut self) -> &mut dyn OpInstrumenter {
        self
    }

    fn get_unspecialized(&mut self) -> &mut dyn OpInstrumenter {
        self
    }

    fn record_call(&mut self, _: FunctionSignature) {}

    fn seal(self: Box<Self>) -> FunctionCost {
        panic!("DummyInstrumenter cannot be sealed");
    }
}

impl OpInstrumenter for DummyInstrumenter {
    fn record_constraints(&mut self, _: usize) {}
}

pub struct CostAnalysis {
    entry_point: Option<FunctionSignature>,
    functions: HashMap<FunctionSignature, FunctionCost>,
    stack: Vec<(FunctionSignature, Box<dyn FunctionInstrumenter>)>,
}

pub struct SpecializationSummary {
    calls: usize,
    raw_constraints: usize,
    specialized_constraints: usize,
    specialization_total_savings: usize,
}

pub struct Summary {
    total_constraints: usize,
    total_savings_to_make: usize,
    functions: HashMap<FunctionSignature, SpecializationSummary>,
}

impl Summary {
    pub fn pretty_print(&self, ssa: &SSA<ConstantTaint>) -> String {
        let mut r = String::new();
        r += &format!("Total constraints: {}\n", self.total_constraints);
        r += &format!(
            "Total savings to make: {} ({:.1}%)\n",
            self.total_savings_to_make,
            self.total_savings_to_make as f64 / self.total_constraints as f64 * 100.0
        );
        for (sig, summary) in self.functions.iter().sorted_by_key(|(_, s)| s.specialization_total_savings).rev() {
            r += &format!("Function {}\n", sig.pretty_print(ssa));
            r += &format!("  Called times: {}\n", summary.calls);
            r += &format!("  Raw constraints: {}\n", summary.raw_constraints);
            r += &format!(
                "  Specialized constraints: {}\n",
                summary.specialized_constraints
            );
            r += &format!(
                "  Specialization total savings: {}\n",
                summary.specialization_total_savings
            );
        }

        r
    }
}

impl CostAnalysis {
    fn enter_call(&mut self, sig: FunctionSignature) {
        if !self.stack.is_empty() {
            let (_, cost) = self.stack.last_mut().unwrap();
            cost.record_call(sig.clone());
        }
        if self.entry_point.is_none() {
            self.entry_point = Some(sig.clone());
        }
        if self.functions.contains_key(&sig) {
            self.stack.push((sig, Box::new(DummyInstrumenter {})));
        } else {
            let instrumenter = FunctionCost {
                calls: HashMap::new(),
                raw: Instrumenter { constraints: 0 },
                specialized: Instrumenter { constraints: 0 },
            };
            self.stack.push((sig, Box::new(instrumenter)));
        }
    }

    fn exit_call(&mut self) {
        let (sig, instrumenter) = self.stack.pop().unwrap();
        if !self.functions.contains_key(&sig) {
            let instrumenter = instrumenter.seal();
            self.functions.insert(sig, instrumenter);
        }
    }

    fn get_instrumenter(&mut self) -> &mut dyn FunctionInstrumenter {
        self.stack.last_mut().unwrap().1.as_mut()
    }

    pub fn seal(self) -> HashMap<FunctionSignature, FunctionCost> {
        self.functions
    }

    pub fn pretty_print(&self, ssa: &SSA<ConstantTaint>) -> String {
        let mut r = String::new();
        for (sig, cost) in self.functions.iter() {
            r += &format!("Function {}\n", sig.pretty_print(ssa));
            r += &format!("  Calls:\n");
            for (sig, count) in cost.calls.iter() {
                r += &format!("    {}: {} times\n", sig.pretty_print(ssa), count);
            }
            r += &format!("  Raw constraints: {}\n", cost.raw.constraints);
            r += &format!(
                "  Specialized constraints: {}\n",
                cost.specialized.constraints
            );
        }
        r
    }

    pub fn summarize(&self) -> Summary {
        let mut r = Summary {
            functions: HashMap::new(),
            total_constraints: 0,
            total_savings_to_make: 0,
        };
        for (sig, cost) in self.functions.iter() {
            r.functions.insert(
                sig.clone(),
                SpecializationSummary {
                    calls: 0,
                    raw_constraints: cost.raw.constraints,
                    specialized_constraints: cost.specialized.constraints,
                    specialization_total_savings: 0,
                },
            );
        }
        self.walk_call_tree(&mut r, 1, self.entry_point.as_ref().unwrap());

        for (_, summary) in r.functions.iter_mut() {
            summary.specialization_total_savings =
                (summary.raw_constraints - summary.specialized_constraints) * summary.calls;
            r.total_constraints += summary.raw_constraints * summary.calls;
            r.total_savings_to_make += summary.specialization_total_savings;
        }
        r
    }

    fn walk_call_tree(&self, summary: &mut Summary, mul: usize, from_sig: &FunctionSignature) {
        let from = self.functions.get(&from_sig).unwrap();
        let from_summary = summary.functions.get_mut(from_sig).unwrap();
        from_summary.calls += mul;
        for (sig, count) in from.calls.iter() {
            self.walk_call_tree(summary, count * mul, sig);
        }
    }
}

pub struct CostEstimator {}

impl CostEstimator {
    pub fn new() -> Self {
        Self {}
    }

    pub fn run(&self, ssa: &SSA<ConstantTaint>) -> CostAnalysis {
        let main_sig = self.make_main_sig(ssa);
        let mut costs = CostAnalysis {
            functions: HashMap::new(),
            stack: vec![],
            entry_point: Some(main_sig.clone()),
        };

        self.run_fn_from_signature(ssa, main_sig, &mut costs);

        costs
    }

    fn run_fn_from_signature(
        &self,
        ssa: &SSA<ConstantTaint>,
        sig: FunctionSignature,
        costs: &mut CostAnalysis,
    ) {
        let inputs = sig
            .params
            .iter()
            .map(|param| SpecSplitValue {
                // We need to call `to_value` twice, to avoid pointer aliasing.
                unspecialized: param.to_value(),
                specialized: param.to_value(),
            })
            .collect();
        self.run_fn(ssa, sig.id, inputs, costs);
    }

    #[instrument(skip_all, level = Level::DEBUG, fields(function = %ssa.get_function(fn_id).get_name()))]
    fn run_fn(
        &self,
        ssa: &SSA<ConstantTaint>,
        fn_id: FunctionId,
        inputs: Vec<SpecSplitValue>,
        costs: &mut CostAnalysis,
    ) -> Vec<SpecSplitValue> {
        let fn_body = ssa.get_function(fn_id);
        let entry = fn_body.get_entry();
        let mut scope = vec![
            SpecSplitValue {
                unspecialized: Value::FWitness,
                specialized: Value::FWitness,
            };
            fn_body.get_var_num_bound()
        ];
        let mut inputs_sig = vec![];
        for (i, val) in entry.get_parameter_values().enumerate() {
            let tp = fn_body.get_value_type(*val).unwrap();
            scope[val.0 as usize] = inputs[i].clone();
            scope[val.0 as usize].blind_from(tp);
            inputs_sig.push(scope[val.0 as usize].make_unspecialized_sig(tp));
        }
        let sig = FunctionSignature {
            id: fn_id,
            params: inputs_sig,
        };

        for (val, cst) in fn_body.iter_consts() {
            let v = match cst {
                Const::U(s, v) => Value::U(*s, *v),
                Const::Field(f) => Value::Field(f.clone()),
            };
            scope[val.0 as usize] = SpecSplitValue {
                unspecialized: v.clone(),
                specialized: v.clone(),
            };
        }

        costs.enter_call(sig);
        let mut current = Some(entry);

        while let Some(block) = current {
            for instr in block.get_instructions() {
                match instr {
                    crate::compiler::ssa::OpCode::Cmp(cmp_kind, r, a, b) => {
                        let a = scope[a.0 as usize].clone();
                        let b = scope[b.0 as usize].clone();
                        scope[r.0 as usize] = a.cmp_op(&b, cmp_kind, costs.get_instrumenter());
                    }
                    crate::compiler::ssa::OpCode::BinaryArithOp(binary_arith_op_kind, r, a, b) => {
                        let a = scope[a.0 as usize].clone();
                        let b = scope[b.0 as usize].clone();
                        scope[r.0 as usize] =
                            a.binary_arith_op(&b, binary_arith_op_kind, costs.get_instrumenter());
                    }
                    crate::compiler::ssa::OpCode::Cast(r, a, cast_target) => {
                        let a = scope[a.0 as usize].clone();
                        scope[r.0 as usize] = a.cast_op(cast_target, costs.get_instrumenter());
                    }
                    crate::compiler::ssa::OpCode::Truncate(r, a, from, to) => {
                        let a = scope[a.0 as usize].clone();
                        scope[r.0 as usize] = a.truncate_op(*from, *to, costs.get_instrumenter());
                    }
                    crate::compiler::ssa::OpCode::Not(r, a) => {
                        let a = scope[a.0 as usize].clone();
                        scope[r.0 as usize] = a.not_op(costs.get_instrumenter());
                    }
                    crate::compiler::ssa::OpCode::MkSeq(r, a, seq_type, _) => {
                        let a = a
                            .iter()
                            .map(|id| scope[id.0 as usize].clone())
                            .collect::<Vec<_>>();
                        scope[r.0 as usize] = SpecSplitValue::mk_array(a);
                    }
                    crate::compiler::ssa::OpCode::Alloc(r, _, _) => {
                        // The inner value is not important here, it will be overwritten by a consecutive write
                        scope[r.0 as usize].specialized =
                            Value::Pointer(Rc::new(RefCell::new(Value::FWitness)));
                        scope[r.0 as usize].unspecialized =
                            Value::Pointer(Rc::new(RefCell::new(Value::FWitness)));
                    }
                    crate::compiler::ssa::OpCode::Store(ptr, val) => {
                        let ptr = scope[ptr.0 as usize].clone();
                        let val = scope[val.0 as usize].clone();
                        ptr.ptr_write(val, costs.get_instrumenter());
                    }
                    crate::compiler::ssa::OpCode::Load(r, ptr) => {
                        let ptr = scope[ptr.0 as usize].clone();
                        let result_type = fn_body.get_value_type(*r).unwrap();
                        scope[r.0 as usize] = ptr.ptr_read(costs.get_instrumenter());
                        scope[r.0 as usize].blind_unspecialized_from(result_type);
                    }
                    crate::compiler::ssa::OpCode::AssertR1C(a, b, c) => {
                        let a = scope[a.0 as usize].clone();
                        let b = scope[b.0 as usize].clone();
                        let c = scope[c.0 as usize].clone();
                        SpecSplitValue::assert_r1c(a, b, c, costs.get_instrumenter());
                    }
                    crate::compiler::ssa::OpCode::Call(returns, function_id, arguments) => {
                        let params = arguments
                            .iter()
                            .map(|id| scope[id.0 as usize].clone())
                            .collect::<Vec<_>>();
                        let outputs = self.run_fn(ssa, *function_id, params, costs);
                        for (i, val) in returns.iter().enumerate() {
                            scope[val.0 as usize] = outputs[i].clone();
                        }
                    }
                    crate::compiler::ssa::OpCode::ArrayGet(r, a, i) => {
                        let a = scope[a.0 as usize].clone();
                        let i: SpecSplitValue = scope[i.0 as usize].clone();
                        scope[r.0 as usize] = a.array_get(i, costs.get_instrumenter());
                        let result_type = fn_body.get_value_type(*r).unwrap();
                        scope[r.0 as usize].blind_unspecialized_from(result_type);
                    }
                    crate::compiler::ssa::OpCode::ArraySet(r, arr, i, v) => {
                        let a = scope[arr.0 as usize].clone();
                        let i = scope[i.0 as usize].clone();
                        let v = scope[v.0 as usize].clone();
                        scope[r.0 as usize] = a.array_set(i, v, costs.get_instrumenter());
                    }
                    crate::compiler::ssa::OpCode::Select(r, cond, if_t, if_f) => {
                        let cond = scope[cond.0 as usize].clone();
                        let if_t = scope[if_t.0 as usize].clone();
                        let if_f = scope[if_f.0 as usize].clone();
                        scope[r.0 as usize] = cond.select(if_t, if_f, costs.get_instrumenter());
                    }
                    crate::compiler::ssa::OpCode::ToBits(r, a, endianness, size) => {
                        let a = scope[a.0 as usize].clone();
                        scope[r.0 as usize] =
                            a.to_bits(endianness, *size, costs.get_instrumenter());
                    }
                    crate::compiler::ssa::OpCode::WriteWitness(r, a, _) => {
                        let a = scope[a.0 as usize].clone();
                        if let Some(r) = r {
                            let tp = fn_body.get_value_type(*r).unwrap();
                            scope[r.0 as usize] = a;
                            scope[r.0 as usize].blind_unspecialized_from(tp);
                        }
                    }
                    crate::compiler::ssa::OpCode::Constrain(a, b, c) => {
                        let a = scope[a.0 as usize].clone();
                        let b = scope[b.0 as usize].clone();
                        let c = scope[c.0 as usize].clone();
                        SpecSplitValue::constrain(a, b, c, costs.get_instrumenter());
                    }
                    crate::compiler::ssa::OpCode::AssertEq(a, b) => {
                        let a = scope[a.0 as usize].clone();
                        let b = scope[b.0 as usize].clone();
                        SpecSplitValue::assert_eq(a, b, costs.get_instrumenter());
                    }
                }
            }

            match block.get_terminator().unwrap() {
                Terminator::Return(returns) => {
                    let mut outputs = returns
                        .iter()
                        .map(|id| scope[id.0 as usize].clone())
                        .collect::<Vec<_>>();
                    for (i, val) in outputs.iter_mut().enumerate() {
                        val.blind_from(fn_body.get_value_type(returns[i]).unwrap());
                    }
                    costs.exit_call();
                    return outputs;
                }
                Terminator::Jmp(target, params) => {
                    let mut params = params
                        .iter()
                        .map(|id| scope[id.0 as usize].clone())
                        .collect::<Vec<_>>();
                    let target_block = fn_body.get_block(*target);
                    let target_params = target_block.get_parameter_values();
                    for (param, val) in params.iter_mut().zip(target_params) {
                        let declared_tp = fn_body.get_value_type(*val).unwrap();
                        param.blind_unspecialized_from(declared_tp);
                        scope[val.0 as usize] = param.clone();
                    }
                    current = Some(target_block);
                }
                Terminator::JmpIf(cond, if_true, if_false) => {
                    let cond = scope[cond.0 as usize].clone();
                    if cond.expect_constant_bool() {
                        current = Some(fn_body.get_block(*if_true));
                    } else {
                        current = Some(fn_body.get_block(*if_false));
                    }
                }
            }
        }

        panic!("ICE: Unreachable, function did not return");
    }

    fn make_main_sig(&self, ssa: &SSA<ConstantTaint>) -> FunctionSignature {
        let id = ssa.get_main_id();
        let main_fn = ssa.get_function(id);
        let params = main_fn.get_param_types();
        let params = params
            .iter()
            .map(|param| self.make_witness_sig(param))
            .collect();
        FunctionSignature { id, params }
    }

    fn make_witness_sig(&self, tp: &Type<ConstantTaint>) -> ValueSignature {
        match &tp.expr {
            TypeExpr::U(size) => ValueSignature::UWitness(*size),
            TypeExpr::Field => ValueSignature::FWitness,
            TypeExpr::Array(internal, size) => {
                ValueSignature::Array(vec![self.make_witness_sig(internal); *size])
            }
            TypeExpr::Slice(_) => panic!("slice not possible here"),
            TypeExpr::Ref(_) => panic!("ref not possible here"),
        }
    }
}
