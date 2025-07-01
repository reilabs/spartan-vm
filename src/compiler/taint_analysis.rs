use crate::compiler::ssa::{BlockId, FunctionId, SSA, Type, ValueId, Function};
use std::collections::{HashMap, VecDeque};

#[derive(PartialEq, Eq, Debug, Clone, Copy, Hash)]
struct TypeVariable(usize);

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum Taint {
    Pure,
    Witness,
    Variable(TypeVariable),
    Meet(Box<Taint>, Box<Taint>),
}

impl Taint {
    pub fn to_string(&self) -> String {
        match self {
            Taint::Pure => "P".to_string(),
            Taint::Witness => "W".to_string(),
            Taint::Variable(var) => format!("V{}", var.0),
            Taint::Meet(left, right) => format!("{} ⊓ {}", left.to_string(), right.to_string()),
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
pub enum TaintType {
    Primitive(Taint),
    Nested(Taint, Box<TaintType>),
}

impl TaintType {
    pub fn to_string(&self) -> String {
        match self {
            TaintType::Primitive(taint) => taint.to_string(),
            TaintType::Nested(taint, inner) => format!("({})[{}]", taint.to_string(), inner.to_string()),
        }
    }
}

pub struct TaintAnalysis {
    functions: HashMap<FunctionId, FunctionTaintAnalysis>,
    unification_context: UnificationContext
}

struct FunctionTaintAnalysis {
    returns_taint: Vec<TaintType>,
    blocks: HashMap<BlockId, BlockTaintAnalysis>,
}

impl FunctionTaintAnalysis {
    pub fn new(returns_taint: Vec<TaintType>) -> Self {
        FunctionTaintAnalysis {
            returns_taint,
            blocks: HashMap::new(),
        }
    }

    pub fn get_block_analysis_mut(&mut self, block_id: BlockId) -> &mut BlockTaintAnalysis {
        self.blocks.entry(block_id).or_insert_with(BlockTaintAnalysis::new)
    }

    pub fn get_block_analysis(&self, block_id: BlockId) -> &BlockTaintAnalysis {
        self.blocks.get(&block_id).expect("Block analysis not found")
    }
}

struct BlockTaintAnalysis {
    values: HashMap<ValueId, TaintType>,
}

impl BlockTaintAnalysis {
    pub fn new() -> Self {
        BlockTaintAnalysis {
            values: HashMap::new(),
        }
    }

    pub fn set_value_taint(&mut self, value: ValueId, taint: TaintType) -> TaintType {
        self.values.insert(value, taint.clone());
        taint
    }

    pub fn get_value_taint(&self, value: ValueId) -> Option<&TaintType> {
        self.values.get(&value)
    }
}

struct UnificationContext {
    last_variable: usize,
}

impl UnificationContext {
    pub fn new() -> Self {
        UnificationContext { last_variable: 0 }
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
        self.functions.get(&fun_id).expect("Function analysis not found")
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

        Ok(())
    }

    fn initialize_function_returns(&mut self, fun_id: FunctionId, fun: &Function) {
        let returns_taint = fun.get_returns().iter().map(|typ| {
            self.construct_free_taint_for_type(typ)
        }).collect();
        let analysis = self.get_function_analysis_mut(fun_id);
        analysis.returns_taint = returns_taint;
    }

    fn initialize_block_inputs(&mut self, fun_id: FunctionId, fun: &Function) {
        for (block_id, block) in fun.get_blocks() {
            for (value, tp) in block.get_parameters() {
                let taint = self.construct_free_taint_for_type(tp);
                let analysis = self.get_function_analysis_mut(fun_id);
                let block_analysis = analysis.get_block_analysis_mut(*block_id);
                block_analysis.set_value_taint(*value, taint);
            }
        }
    }

    fn construct_free_taint_for_type(&mut self, typ: &Type) -> TaintType {
        match typ {
            Type::U32 | Type::Field | Type::Bool => TaintType::Primitive(self.unification_context.fresh_variable()),
            Type::Array(i, _) | Type::Ref(i) => TaintType::Nested(
                self.unification_context.fresh_variable(),
                Box::new(self.construct_free_taint_for_type(i)),
            )
        }
    }

    fn construct_taint_for_main_param(typ: &Type) -> TaintType {
        match typ {
            Type::U32 | Type::Field | Type::Bool => TaintType::Primitive(Taint::Witness),
            Type::Array(i, _) | Type::Ref(i) => TaintType::Nested(
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

    pub fn annotate_value(&self, func_id: FunctionId, block_id: BlockId, value_id: ValueId) -> String {
        let Some(analysis) = self.functions.get(&func_id) else {
            return "".to_string();
        };
        let Some(block_analysis) = analysis.blocks.get(&block_id) else {
            return "".to_string();
        };
        let Some(taint) = block_analysis.get_value_taint(value_id) else {
            return "".to_string();
        };
        taint.to_string()
    }
}
