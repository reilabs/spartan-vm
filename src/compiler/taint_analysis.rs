use crate::compiler::ssa::{
    Block, BlockId, Function, FunctionId, OpCode, SSA, Terminator, Type, ValueId,
};
use crate::compiler::taint_analysis::Taint::Pure;
use crate::compiler::taint_analysis::TaintType::{NestedImmutable, NestedMutable, Primitive};
use std::collections::{HashMap, HashSet, VecDeque};

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
pub struct TypeVariable(pub usize);

impl std::fmt::Display for TypeVariable {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "V{}", self.0)
    }
}

#[derive(PartialEq, Eq, Debug, Clone, Hash)]
pub enum Taint {
    Pure,
    Witness,
    Variable(TypeVariable),
    Meet(Box<Taint>, Box<Taint>), // under the Pure > Witness ordering
    Instantiate(Box<Taint>, Vec<(TypeVariable, Taint)>),
}

impl Taint {
    pub fn to_string(&self) -> String {
        match self {
            Taint::Pure => "P".to_string(),
            Taint::Witness => "W".to_string(),
            Taint::Variable(var) => format!("V{}", var.0),
            Taint::Meet(left, right) => format!("{} ⊓ {}", left.to_string(), right.to_string()),
            Taint::Instantiate(var, substitutions) => {
                let subs = substitutions
                    .iter()
                    .map(|(from, to)| format!("V{} -> {}", from.0, to.to_string()))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("I({})[{}]", var.to_string(), subs)
            }
        }
    }

    pub fn meet(&self, other: &Taint) -> Taint {
        Taint::Meet(Box::new(self.clone()), Box::new(other.clone()))
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum TaintType {
    Primitive(Taint),
    NestedImmutable(Taint, Box<TaintType>),
    NestedMutable(Taint, Box<TaintType>),
}

impl TaintType {
    pub fn to_string(&self) -> String {
        match self {
            TaintType::Primitive(taint) => taint.to_string(),
            TaintType::NestedImmutable(taint, inner) => {
                format!("[{} of {}]", taint.to_string(), inner.to_string())
            }
            TaintType::NestedMutable(taint, inner) => {
                format!("[*{} of {}]", taint.to_string(), inner.to_string())
            }
        }
    }

    pub fn meet(&self, other: &TaintType) -> TaintType {
        match (self, other) {
            (TaintType::Primitive(t1), TaintType::Primitive(t2)) => {
                TaintType::Primitive(t1.meet(t2))
            }
            (TaintType::NestedImmutable(t1, inner1), TaintType::NestedImmutable(t2, inner2)) => {
                let inner_meet = inner1.meet(inner2);
                TaintType::NestedImmutable(t1.meet(t2), Box::new(inner_meet))
            }
            (TaintType::NestedMutable(t1, inner1), TaintType::NestedImmutable(t2, inner2)) => {
                let inner_meet = inner1.meet(inner2);
                TaintType::NestedMutable(t1.meet(t2), Box::new(inner_meet))
            }
            _ => panic!("Cannot meet different taint types"),
        }
    }

    pub fn toplevel_taint(&self) -> Taint {
        match self {
            TaintType::Primitive(taint) => taint.clone(),
            TaintType::NestedImmutable(taint, _) => taint.clone(),
            TaintType::NestedMutable(taint, _) => taint.clone(),
        }
    }

    pub fn child_taint_type(&self) -> Option<TaintType> {
        match self {
            TaintType::NestedImmutable(_, inner) => Some(*inner.clone()),
            TaintType::NestedMutable(_, inner) => Some(*inner.clone()),
            TaintType::Primitive(_) => None,
        }
    }

    pub fn with_toplevel_taint(&self, toplevel: Taint) -> TaintType {
        match self {
            TaintType::Primitive(_) => TaintType::Primitive(toplevel),
            TaintType::NestedImmutable(_, inner) => {
                TaintType::NestedImmutable(toplevel, inner.clone())
            }
            TaintType::NestedMutable(_, inner) => TaintType::NestedMutable(toplevel, inner.clone()),
        }
    }
}

pub struct TaintAnalysis {
    functions: HashMap<FunctionId, FunctionTaintAnalysis>,
    unification_context: UnificationContext,
}

struct FunctionTaintAnalysis {
    returns_taint: Vec<TaintType>,
    entry_block: BlockId,
    blocks: HashMap<BlockId, BlockTaintAnalysis>,
}

impl FunctionTaintAnalysis {
    pub fn new(returns_taint: Vec<TaintType>) -> Self {
        FunctionTaintAnalysis {
            returns_taint,
            entry_block: BlockId(0),
            blocks: HashMap::new(),
        }
    }

    pub fn get_block_analysis_mut(&mut self, block_id: BlockId) -> &mut BlockTaintAnalysis {
        self.blocks
            .entry(block_id)
            .or_insert_with(BlockTaintAnalysis::new)
    }

    pub fn get_block_analysis(&self, block_id: BlockId) -> &BlockTaintAnalysis {
        self.blocks
            .get(&block_id)
            .expect("Block analysis not found")
    }

    pub fn get_input_taints(&self) -> Vec<TaintType> {
        self.blocks
            .get(&self.entry_block)
            .map_or_else(Vec::new, |block| block.get_parameter_taints())
    }
}

struct BlockTaintAnalysis {
    values: HashMap<ValueId, TaintType>,
    parameter_values: Vec<ValueId>,
}

impl BlockTaintAnalysis {
    pub fn new() -> Self {
        BlockTaintAnalysis {
            values: HashMap::new(),
            parameter_values: Vec::new(),
        }
    }

    pub fn set_value_taint(&mut self, value: ValueId, taint: TaintType) -> TaintType {
        self.values.insert(value, taint.clone());
        taint
    }

    pub fn get_value_taint(&self, value: ValueId) -> Option<&TaintType> {
        self.values.get(&value)
    }

    pub fn set_parameter_values(&mut self, params: Vec<ValueId>) {
        self.parameter_values = params;
    }

    pub fn get_parameter_taints(&self) -> Vec<TaintType> {
        self.parameter_values
            .iter()
            .map(|value| self.values.get(value).cloned().unwrap())
            .collect()
    }
}

#[derive(Clone)]
pub enum Judgement {
    Eq(Taint, Taint),
    Le(Taint, Taint),
}

struct UnificationContext {
    last_variable: usize,
    judgements: Vec<Judgement>,
}

impl UnificationContext {
    pub fn new() -> Self {
        UnificationContext {
            last_variable: 0,
            judgements: Vec::new(),
        }
    }

    pub fn fresh_variable(&mut self) -> Taint {
        let var = TypeVariable(self.last_variable);
        self.last_variable += 1;
        Taint::Variable(var)
    }
}

// TODO: this will break on recursion
impl TaintAnalysis {
    pub fn get_function_analysis_mut(&mut self, fun_id: FunctionId) -> &mut FunctionTaintAnalysis {
        self.functions.entry(fun_id).or_insert_with(|| {
            let returns_taint = vec![];
            FunctionTaintAnalysis::new(returns_taint)
        })
    }

    pub fn get_function_analysis(&self, fun_id: FunctionId) -> &FunctionTaintAnalysis {
        self.functions
            .get(&fun_id)
            .expect("Function analysis not found")
    }

    pub fn new() -> Self {
        TaintAnalysis {
            functions: HashMap::new(),
            unification_context: UnificationContext::new(),
        }
    }
    pub fn run(&mut self, ssa: &SSA) -> Result<(), String> {
        for (fun_id, fun) in ssa.iter_functions() {
            self.initialize_function_returns(*fun_id, fun);
            self.initialize_block_inputs(*fun_id, fun);
        }

        for (fun_id, fun) in ssa.iter_functions() {
            self.analyze_instructions(ssa, *fun_id, fun);
        }

        Ok(())
    }

    fn initialize_function_returns(&mut self, fun_id: FunctionId, fun: &Function) {
        let returns_taint = fun
            .get_returns()
            .iter()
            .map(|typ| self.construct_free_taint_for_type(typ))
            .collect();
        let analysis = self.get_function_analysis_mut(fun_id);
        analysis.returns_taint = returns_taint;
    }

    fn initialize_block_inputs(&mut self, fun_id: FunctionId, fun: &Function) {
        for (block_id, block) in fun.get_blocks() {
            let param_values: Vec<_> = block.get_parameters().map(|(v, _)| *v).collect();
            for (value, tp) in block.get_parameters() {
                let taint = self.construct_free_taint_for_type(tp);
                let analysis = self.get_function_analysis_mut(fun_id);
                let block_analysis = analysis.get_block_analysis_mut(*block_id);
                block_analysis.set_value_taint(*value, taint);
            }
            // Set parameter values after setting taints
            let analysis = self.get_function_analysis_mut(fun_id);
            let block_analysis = analysis.get_block_analysis_mut(*block_id);
            block_analysis.set_parameter_values(param_values);
        }
    }

    fn analyze_instructions(&mut self, ssa: &SSA, fun_id: FunctionId, fun: &Function) {
        let analysis = self.get_function_analysis_mut(fun_id);
        analysis.entry_block = fun.get_entry_id();
        for (block_id, block) in fun.get_blocks() {
            self.analyze_block_instructions(ssa, fun_id, *block_id, block);
        }
    }

    fn analyze_block_instructions(
        &mut self,
        ssa: &SSA,
        fun_id: FunctionId,
        block_id: BlockId,
        block: &Block,
    ) {
        for instruction in block.get_instructions() {
            self.analyze_instruction(ssa, fun_id, block_id, instruction);
        }
        if let Some(terminator) = block.get_terminator() {
            self.analyze_terminator(ssa, fun_id, block_id, terminator);
        }
    }

    fn analyze_instruction(
        &mut self,
        ssa: &SSA,
        fun_id: FunctionId,
        block_id: BlockId,
        instruction: &OpCode,
    ) {
        match instruction {
            OpCode::FieldConst(r, _) | OpCode::BConst(r, _) | OpCode::UConst(r, _) => {
                self.set_taint_type(fun_id, block_id, *r, Primitive(Pure));
            }

            OpCode::Eq(r, lhs, rhs) | OpCode::Add(r, lhs, rhs) | OpCode::Lt(r, lhs, rhs) => {
                let lhs = self
                    .get_taint_type(fun_id, block_id, *lhs)
                    .expect("LHS not found");
                let rhs = self
                    .get_taint_type(fun_id, block_id, *rhs)
                    .expect("RHS not found");
                self.set_taint_type(fun_id, block_id, *r, lhs.meet(&rhs));
            }

            OpCode::Alloc(r, t) => {
                let free = self.construct_free_taint_for_type(t);
                let fv = self.unification_context.fresh_variable();
                self.set_taint_type(fun_id, block_id, *r, NestedMutable(fv, Box::new(free)));
            }
            OpCode::Store(ptr, v) => {
                let ptr_taint = self
                    .get_taint_type(fun_id, block_id, *ptr)
                    .expect("Pointer taint not found");
                let value_taint = self
                    .get_taint_type(fun_id, block_id, *v)
                    .expect("Value taint not found");
                match ptr_taint {
                    NestedMutable(_, inner) => {
                        self.emit_le(inner.toplevel_taint(), value_taint.toplevel_taint()); // TODO should it be deep?
                    }
                    _ => {
                        panic!("Unexpected taint for ptr");
                    }
                }
            }
            OpCode::Load(r, ptr) => {
                let ptr_taint = self
                    .get_taint_type(fun_id, block_id, *ptr)
                    .expect("Pointer taint not found");
                match ptr_taint {
                    NestedMutable(ptr_taint, inner) => {
                        self.set_taint_type(fun_id, block_id, *r, *inner.clone()); // TODO this should meet with ptr taint
                    }
                    _ => {
                        panic!("Unexpected taint for ptr");
                    }
                }
            }
            OpCode::AssertEq(_, _) => {}
            OpCode::Call(outputs, func, inputs) => {
                // Get SSA types for parameters and arguments
                let callee_func = ssa.get_function(*func);
                let param_types: Vec<_> = callee_func
                    .get_entry()
                    .get_parameters()
                    .map(|(_, t)| t)
                    .collect();
                let caller_function = ssa.get_function(fun_id);
                let arg_types: Vec<_> = inputs
                    .iter()
                    .map(|v| {
                        caller_function.get_value_type(*v).unwrap_or(&Type::Field) // fallback to Field for debug
                    })
                    .collect();

                let input_taints = inputs
                    .iter()
                    .map(|v| {
                        self.get_taint_type(fun_id, block_id, *v)
                            .expect("Input taint not found")
                    })
                    .collect::<Vec<_>>();
                let param_taints = self.get_function_analysis(*func).get_input_taints();

                // Debug prints
                println!("CALL: param_types = {:?}", param_types);
                println!("CALL: arg_types = {:?}", arg_types);
                println!("CALL: param_taints = {:?}", param_taints);
                println!("CALL: input_taints = {:?}", input_taints);

                let instantiations = self.prepare_instantiations(&param_taints, &input_taints);

                let declared_outputs = self.get_function_analysis(*func).returns_taint.clone();

                for (output, declared_output) in outputs.iter().zip(declared_outputs.iter()) {
                    let output_taint = self.instantiate_type(declared_output, &instantiations);
                    self.set_taint_type(fun_id, block_id, *output, output_taint);
                }
            }
            OpCode::ArrayGet(r, arr, ix) => {
                let arr_taint = self
                    .get_taint_type(fun_id, block_id, *arr)
                    .expect("Array taint not found");
                let ix_taint = self
                    .get_taint_type(fun_id, block_id, *ix)
                    .expect("Index taint not found");
                let item_taint = arr_taint
                    .child_taint_type()
                    .expect("Array taint should have child taint");
                let result_taint_type = item_taint.with_toplevel_taint(
                    arr_taint
                        .toplevel_taint()
                        .meet(&ix_taint.toplevel_taint())
                        .meet(&item_taint.toplevel_taint()),
                );
                self.set_taint_type(fun_id, block_id, *r, result_taint_type);
            }
        }
    }

    fn analyze_terminator(
        &mut self,
        ssa: &SSA,
        fun_id: FunctionId,
        block_id: BlockId,
        terminator: &Terminator,
    ) {
        match terminator {
            Terminator::Return(values) => {
                let returns_taint = self.get_function_analysis(fun_id).returns_taint.clone();
                let actual_returns_taint = values
                    .iter()
                    .map(|v| {
                        self.get_taint_type(fun_id, block_id, *v)
                            .expect("Return taint not found")
                    })
                    .collect::<Vec<_>>();
                for (declared, actual) in returns_taint.iter().zip(actual_returns_taint.iter()) {
                    self.deep_eq(declared.clone(), actual.clone());
                }
            }
            Terminator::Jmp(target, params) => {
                self.analyze_jump(ssa, fun_id, block_id, *target, params);
            }
            Terminator::JmpIf(cond, t1, t2) => {
                self.analyze_jump(ssa, fun_id, block_id, *t1, &[]);
                self.analyze_jump(ssa, fun_id, block_id, *t2, &[]);
            }
        }
    }

    fn analyze_jump(
        &mut self,
        ssa: &SSA,
        fun_id: FunctionId,
        block_id: BlockId,
        target: BlockId,
        values: &[ValueId],
    ) {
        let target_params = ssa.get_function(fun_id).get_block(target).get_parameters();
        let param_taints = target_params
            .map(|(v, _)| {
                self.get_taint_type(fun_id, target, *v)
                    .expect("Target taint not found")
            })
            .collect::<Vec<_>>();
        let value_taints = values
            .iter()
            .map(|v| {
                self.get_taint_type(fun_id, block_id, *v)
                    .expect("Param taint not found")
            })
            .collect::<Vec<_>>();

        let instantiations = self.prepare_instantiations(&param_taints, &value_taints);

        for (pt, vt) in instantiations {
            self.emit_le(Taint::Variable(pt), vt);
        }
        // for (val, param) in value_taints.iter().zip(param_taints.iter()) {
        //     match (val, param) {
        //         // Pointers may get tainted in the caller. Therefore, we assert that the current
        //         // type of the caller is no greater than the type inferred in the callee.
        //         (
        //             TaintType::NestedMutable(val_taint, _),
        //             TaintType::NestedMutable(Taint::Variable(tv), _),
        //         ) => {
        //             self.emit_le(
        //                 val_taint.clone(),
        //                 Taint::Instantiate(tv.clone(), instantiations.clone()),
        //             );
        //         }
        //         _ => (),
        //     }
        // }
    }

    fn instantiate_type(
        &mut self,
        typ: &TaintType,
        instantiations: &[(TypeVariable, Taint)],
    ) -> TaintType {
        match typ {
            TaintType::Primitive(t) => {
                TaintType::Primitive(Taint::Instantiate(Box::new(t.clone()), instantiations.to_vec()))
            }
            TaintType::NestedImmutable(t, inner) => {
                let instantiated_inner = self.instantiate_type(inner, instantiations);
                TaintType::NestedImmutable(
                    Taint::Instantiate(Box::new(t.clone()), instantiations.to_vec()),
                    Box::new(instantiated_inner),
                )
            }
            TaintType::NestedMutable(t, inner) => {
                let instantiated_inner = self.instantiate_type(inner, instantiations);
                TaintType::NestedMutable(
                    Taint::Instantiate(Box::new(t.clone()), instantiations.to_vec()),
                    Box::new(instantiated_inner),
                )
            }
            _ => panic!("Instantiated type must be fully free"),
        }
    }

    fn prepare_instantiations(
        &self,
        params: &[TaintType],
        values: &[TaintType],
    ) -> Vec<(TypeVariable, Taint)> {
        params
            .iter()
            .zip(values.iter())
            .flat_map(|(p, v)| self.prepare_instantiations_for_type(p, v))
            .collect()
    }

    fn prepare_instantiations_for_type(
        &self,
        param: &TaintType,
        value: &TaintType,
    ) -> Vec<(TypeVariable, Taint)> {
        match (param, value) {
            (TaintType::Primitive(Taint::Variable(tv)), TaintType::Primitive(v_taint)) => {
                vec![(*tv, v_taint.clone())]
            }
            (
                TaintType::NestedImmutable(Taint::Variable(tv), inner_param),
                TaintType::NestedImmutable(v_taint, inner_value),
            ) => {
                let mut instantiations = vec![(*tv, v_taint.clone())];
                instantiations
                    .extend(self.prepare_instantiations_for_type(inner_param, inner_value));
                instantiations
            }
            (
                TaintType::NestedMutable(Taint::Variable(tv), inner_param),
                TaintType::NestedMutable(v_taint, inner_value),
            ) => {
                let mut instantiations = vec![(*tv, v_taint.clone())];
                instantiations
                    .extend(self.prepare_instantiations_for_type(inner_param, inner_value));
                instantiations
            }
            _ => panic!(
                "Malformed params for instantiation {} and {}",
                param.to_string(),
                value.to_string()
            ),
        }
    }

    fn construct_free_taint_for_type(&mut self, typ: &Type) -> TaintType {
        match typ {
            Type::U32 | Type::Field | Type::Bool => {
                TaintType::Primitive(self.unification_context.fresh_variable())
            }
            Type::Array(i, _) => TaintType::NestedImmutable(
                self.unification_context.fresh_variable(),
                Box::new(self.construct_free_taint_for_type(i)),
            ),
            Type::Ref(i) => TaintType::NestedMutable(
                self.unification_context.fresh_variable(),
                Box::new(self.construct_free_taint_for_type(i)),
            ),
        }
    }

    fn construct_pure_taint_for_type(&self, typ: &Type) -> TaintType {
        match typ {
            Type::U32 | Type::Field | Type::Bool => TaintType::Primitive(Pure),
            Type::Array(i, _) => {
                TaintType::NestedImmutable(Pure, Box::new(self.construct_pure_taint_for_type(i)))
            }
            Type::Ref(i) => {
                TaintType::NestedMutable(Pure, Box::new(self.construct_pure_taint_for_type(i)))
            }
        }
    }

    fn construct_taint_for_main_param(typ: &Type) -> TaintType {
        match typ {
            Type::U32 | Type::Field | Type::Bool => TaintType::Primitive(Taint::Witness),
            Type::Array(i, _) => TaintType::NestedImmutable(
                Taint::Pure,
                Box::new(Self::construct_taint_for_main_param(i)),
            ),
            Type::Ref(i) => TaintType::NestedMutable(
                Taint::Pure,
                Box::new(Self::construct_taint_for_main_param(i)),
            ),
        }
    }

    fn construct_main_signature(ssa: &SSA) -> Vec<TaintType> {
        ssa.get_main()
            .get_param_types()
            .iter()
            .map(Self::construct_taint_for_main_param)
            .collect()
    }

    pub fn get_taint_type(
        &self,
        func_id: FunctionId,
        block_id: BlockId,
        value_id: ValueId,
    ) -> Option<TaintType> {
        let Some(analysis) = self.functions.get(&func_id) else {
            return None;
        };
        let Some(block_analysis) = analysis.blocks.get(&block_id) else {
            return None;
        };
        block_analysis.get_value_taint(value_id).cloned()
    }

    fn set_taint_type(
        &mut self,
        func_id: FunctionId,
        block_id: BlockId,
        value_id: ValueId,
        taint: TaintType,
    ) {
        let analysis = self.get_function_analysis_mut(func_id);
        let block_analysis = analysis.get_block_analysis_mut(block_id);
        block_analysis.set_value_taint(value_id, taint);
    }

    pub fn annotate_value(
        &self,
        func_id: FunctionId,
        block_id: BlockId,
        value_id: ValueId,
    ) -> String {
        let Some(taint) = self.get_taint_type(func_id, block_id, value_id) else {
            return "".to_string();
        };
        taint.to_string()
    }

    fn emit_le(&mut self, left: Taint, right: Taint) {
        self.unification_context
            .judgements
            .push(Judgement::Le(left, right));
    }

    fn deep_eq(&mut self, left: TaintType, right: TaintType) {
        let left_toplevel = left.toplevel_taint();
        let right_toplevel = right.toplevel_taint();
        self.emit_eq(left_toplevel, right_toplevel);
        if let (Some(l), Some(r)) = (left.child_taint_type(), right.child_taint_type()) {
            self.deep_eq(l, r);
        }
    }

    fn emit_eq(&mut self, left: Taint, right: Taint) {
        self.unification_context
            .judgements
            .push(Judgement::Eq(left, right));
    }

    pub fn judgements_string(&self) -> String {
        self.unification_context
            .judgements
            .iter()
            .map(|j| match j {
                Judgement::Eq(l, r) => format!("{} = {}", l.to_string(), r.to_string()),
                Judgement::Le(l, r) => format!("{} ≤ {}", l.to_string(), r.to_string()),
            })
            .collect::<Vec<_>>()
            .join("\n")
    }

    pub fn get_judgements(&self) -> Vec<String> {
        self.unification_context
            .judgements
            .iter()
            .map(|j| format!("{}", j))
            .collect()
    }

    pub fn get_judgements_data(&self) -> &[Judgement] {
        &self.unification_context.judgements
    }
}

impl std::fmt::Display for Judgement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Judgement::Eq(a, b) => write!(f, "{} = {}", a.to_string(), b.to_string()),
            Judgement::Le(a, b) => write!(f, "{} ≤ {}", a.to_string(), b.to_string()),
        }
    }
}
