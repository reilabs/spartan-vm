use std::{collections::HashMap, fmt::{Debug, Display}};

use crate::compiler::{
    fix_double_jumps::ValueReplacements, flow_analysis::{FlowAnalysis, CFG}, ir::r#type::Empty, ssa::{BlockId, Const, Function, OpCode, ValueId, SSA}
};

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Expr {
    Add(Vec<Expr>),
    Mul(Vec<Expr>),
    FConst(ark_bn254::Fr),
    BConst(bool),
    UConst(u32),
    Variable(u64),
    Eq(Box<Expr>, Box<Expr>),
    Lt(Box<Expr>, Box<Expr>),
    ArrayGet(Box<Expr>, Box<Expr>),
}

impl Expr {
    pub fn variable(value_id: ValueId) -> Self {
        Self::Variable(value_id.0)
    }

    fn get_adds(&self) -> Vec<Self> {
        match self {
            Self::Add(exprs) => exprs.iter().cloned().collect(),
            _ => vec![self.clone()],
        }
    }

    fn get_muls(&self) -> Vec<Self> {
        match self {
            Self::Mul(exprs) => exprs.iter().cloned().collect(),
            _ => vec![self.clone()],
        }
    }

    pub fn add(&self, other: &Self) -> Self {
        let mut adds = self.get_adds();
        adds.extend(other.get_adds());
        adds.sort();
        Self::Add(adds)
    }

    pub fn mul(&self, other: &Self) -> Self {
        let mut muls = self.get_muls();
        muls.extend(other.get_muls());
        muls.sort();
        Self::Mul(muls)
    }

    pub fn bconst(value: bool) -> Self {
        Self::BConst(value)
    }

    pub fn uconst(value: u32) -> Self {
        Self::UConst(value)
    }

    pub fn fconst(value: ark_bn254::Fr) -> Self {
        Self::FConst(value)
    }

    pub fn eq(&self, other: &Self) -> Self {
        Self::Eq(Box::new(self.clone()), Box::new(other.clone()))
    }

    pub fn lt(&self, other: &Self) -> Self {
        Self::Lt(Box::new(self.clone()), Box::new(other.clone()))
    }

    pub fn array_get(&self, index: &Self) -> Self {
        Self::ArrayGet(Box::new(self.clone()), Box::new(index.clone()))
    }
}

impl Display for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Add(exprs) => write!(f, "({})", exprs.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(" + ")),
            Self::Mul(exprs) => write!(f, "({})", exprs.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(" * ")),
            Self::FConst(value) => write!(f, "{}", value),
            Self::BConst(value) => write!(f, "{}", value),
            Self::UConst(value) => write!(f, "{}", value),
            Self::Variable(value) => write!(f, "v{}", value),
            Self::Eq(lhs, rhs) => write!(f, "({} == {})", lhs, rhs),
            Self::Lt(lhs, rhs) => write!(f, "({} < {})", lhs, rhs),
            Self::ArrayGet(array, index) => write!(f, "{}[{}]", array, index),
        }
    }
}

impl Debug for Expr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self)
    }
}

pub struct CSE {}

impl CSE {
    pub fn new() -> Self {
        Self {}
    }

    pub fn run(&self, ssa: &mut SSA<Empty>, cfg: &FlowAnalysis) {
        for (function_id, function) in ssa.iter_functions_mut() {
            let cfg = cfg.get_function_cfg(*function_id);
            let exprs = self.gather_expressions(function, cfg);
            let mut value_replacements = ValueReplacements::new();
            for (expr, occurrences) in exprs {
                if occurrences.len() <= 1 {
                    continue;
                }
                let mut replacement_groups: Vec<((BlockId, usize, ValueId), Vec<ValueId>)> = vec![];
                for (block_id, instruction_idx, value_id) in occurrences {
                    let mut found = false;
                    for ((candidate_block, candidate_instruction, candidate_value_id), others) in replacement_groups.iter_mut() {
                        if self.can_replace(cfg, *candidate_block, *candidate_instruction, block_id, instruction_idx) {
                            found = true;
                            others.push(value_id);
                            break;
                        } else if self.can_replace(cfg, block_id, instruction_idx, *candidate_block, *candidate_instruction) {
                            found = true;
                            others.push(*candidate_value_id);
                            *candidate_block = block_id;
                            *candidate_instruction = instruction_idx;
                            *candidate_value_id = value_id;
                            break;
                        }
                    }
                    if !found {
                        replacement_groups.push(((block_id, instruction_idx, value_id), vec![]));
                    }

                }
                for ((_, _, value_id), others) in replacement_groups {
                    for other in others {
                        value_replacements.insert(other, value_id);
                    }
                }
            }

            for (_, block) in function.get_blocks_mut() {
                for instruction in block.get_instructions_mut() {
                    value_replacements.replace_inputs(instruction);
                }
                value_replacements.replace_terminator(block.get_terminator_mut());
            }
        }
    }

    fn can_replace(&self, cfg: &CFG, block1: BlockId, instruction1: usize, block2: BlockId, instruction2: usize) -> bool {
        if block1 == block2 && instruction1 < instruction2 {
            return true;
        }
        if cfg.dominates(block1, block2) {
            return true;
        }
        false
    }

    fn gather_expressions(
        &self,
        ssa: &Function<Empty>,
        cfg: &CFG,
    ) -> HashMap<Expr, Vec<(BlockId, usize, ValueId)>> {
        let mut result: HashMap<Expr, Vec<(BlockId, usize, ValueId)>> = HashMap::new();
        let mut exprs = HashMap::<ValueId, Expr>::new();

        for (value_id, const_) in ssa.iter_consts() {
            match const_ {
                Const::Bool(value) => exprs.insert(*value_id, Expr::bconst(*value)),
                Const::U32(value) => exprs.insert(*value_id, Expr::uconst(*value)),
                Const::Field(value) => exprs.insert(*value_id, Expr::fconst(*value)),
            };
        }

        fn get_expr(exprs: &HashMap<ValueId, Expr>, value_id: &ValueId) -> Expr {
            exprs
                .get(&value_id)
                .cloned()
                .unwrap_or(Expr::variable(*value_id))
        }

        for block_id in cfg.get_domination_pre_order() {
            let block = ssa.get_block(block_id);

            for (instruction_idx, instruction) in block.get_instructions().enumerate() {
                match instruction {
                    OpCode::Add(r, lhs, rhs) => {
                        let lhs_expr = get_expr(&exprs, lhs);
                        let rhs_expr = get_expr(&exprs, rhs);
                        let result_expr = lhs_expr.add(&rhs_expr);
                        exprs.insert(*r, result_expr.clone());
                        result.entry(result_expr).or_default().push((
                            block_id,
                            instruction_idx,
                            *r,
                        ));
                    }
                    OpCode::Mul(r, lhs, rhs) => {
                        let lhs_expr = get_expr(&exprs, lhs);
                        let rhs_expr = get_expr(&exprs, rhs);
                        let result_expr = lhs_expr.mul(&rhs_expr);
                        exprs.insert(*r, result_expr.clone());
                        result.entry(result_expr).or_default().push((
                            block_id,
                            instruction_idx,
                            *r,
                        ));
                    }
                    OpCode::Eq(r, lhs, rhs) => {
                        let lhs_expr = get_expr(&exprs, lhs);
                        let rhs_expr = get_expr(&exprs, rhs);
                        let result_expr = lhs_expr.eq(&rhs_expr);
                        exprs.insert(*r, result_expr.clone());
                        result.entry(result_expr).or_default().push((
                            block_id,
                            instruction_idx,
                            *r,
                        ));
                    }
                    OpCode::Lt(r, lhs, rhs) => {
                        let lhs_expr = get_expr(&exprs, lhs);
                        let rhs_expr = get_expr(&exprs, rhs);
                        let result_expr = lhs_expr.lt(&rhs_expr);
                        exprs.insert(*r, result_expr.clone());
                        result.entry(result_expr).or_default().push((
                            block_id,
                            instruction_idx,
                            *r,
                        ));
                    }
                    OpCode::ArrayGet(r, array, index) => {
                        let array_expr = get_expr(&exprs, array);
                        let index_expr = get_expr(&exprs, index);
                        let result_expr = array_expr.array_get(&index_expr);
                        exprs.insert(*r, result_expr.clone());
                        result.entry(result_expr).or_default().push((
                            block_id,
                            instruction_idx,
                            *r,
                        ));
                    }
                    OpCode::Alloc { .. }
                    | OpCode::Store { .. }
                    | OpCode::Load { .. }
                    | OpCode::AssertEq { .. }
                    | OpCode::Call { .. }
                    | OpCode::WriteWitness { .. }
                    | OpCode::Constrain(_, _, _) => {}
                }
            }
        }
        result
    }
}
