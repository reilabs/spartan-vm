use std::collections::{HashMap, HashSet, VecDeque};

use noirc_evaluator::ssa::ir::instruction;

use crate::compiler::{
    fix_double_jumps::ValueReplacements,
    flow_analysis::{CFG, FlowAnalysis},
    ir::r#type::{Empty, Type, TypeExpr},
    ssa::{BlockId, Function, OpCode, SSA, Terminator, ValueId},
};

pub struct Mem2Reg {}

impl Mem2Reg {
    pub fn new() -> Self {
        Self {}
    }

    pub fn run(&mut self, ssa: &mut SSA<Empty>, cfg: &FlowAnalysis) {
        for (function_id, function) in ssa.iter_functions_mut() {
            if !self.escape_safe(function) {
                continue;
            }
            let cfg = cfg.get_function_cfg(*function_id);
            let writes = self.find_pointer_writes(function);
            let phi_blocks = self.find_phi_blocks(&writes, cfg);
            let phi_args = self.initialize_phis(function, &phi_blocks);
            self.remove_ptrs(function, cfg, &phi_args);
        }
    }

    fn remove_ptrs(
        &self,
        function: &mut Function<Empty>,
        cfg: &CFG,
        phi_map: &HashMap<BlockId, Vec<(ValueId, ValueId)>>,
    ) {
        let mut ptr_values = HashMap::<BlockId, HashMap<ValueId, ValueId>>::new();
        let mut value_replacements = ValueReplacements::new();

        // Traverse the CFG in domination pre-order
        // This ensures that for each ptr the last value is already defined when we enter the block:
        // either it is defined by some dominator, or it is a phi parameter.
        for block_id in cfg.get_domination_pre_order() {
            // fetch all possible values from the parent block
            let mut values = if let Some(parent) = cfg.get_immediate_dominator(block_id) {
                if let Some(parent_values) = ptr_values.get(&parent) {
                    parent_values.clone()
                } else {
                    HashMap::new()
                }
            } else {
                HashMap::new()
            };

            // add phi parameters
            for (param, ptr) in phi_map.get(&block_id).unwrap_or(&vec![]) {
                values.insert(*ptr, *param);
            }

            let instructions = function.get_block_mut(block_id).take_instructions();
            let mut new_instructions = Vec::new();

            for mut instruction in instructions {
                match instruction {
                    OpCode::Alloc(_, _, _) => {}
                    OpCode::Store(lhs, rhs) => {
                        values.insert(lhs, rhs);
                    }
                    OpCode::Load(lhs, rhs) => {
                        let replacement = values.get(&rhs).expect("Uninitialized ptr value");
                        value_replacements.insert(lhs, *replacement);
                    }
                    _ => {
                        value_replacements.replace_instruction(&mut instruction);
                        new_instructions.push(instruction);
                    }
                }
            }

            function
                .get_block_mut(block_id)
                .put_instructions(new_instructions);

            let mut terminator = function.get_block_mut(block_id).take_terminator().unwrap();
            value_replacements.replace_terminator(&mut terminator);

            match &mut terminator {
                Terminator::Jmp(tgt, params) => {
                    let tmp = vec![];
                    let additional_params = phi_map.get(tgt).unwrap_or(&tmp);
                    for (_, val) in additional_params {
                        params.push(values[val]);
                    }
                }
                Terminator::JmpIf(_, t1, t2) => {
                    if phi_map.contains_key(t1) {
                        panic!("ICE: JmpIf with phi parameter");
                    }
                    if phi_map.contains_key(t2) {
                        panic!("ICE: JmpIf with phi parameter");
                    }
                }
                _ => {}
            }
            function.get_block_mut(block_id).set_terminator(terminator);
            ptr_values.insert(block_id, values);
        }
    }

    // returns for each block the vector of (param_id, value_id), where param_id is the id of a new parameter,
    // and value_id is the id of the pointer that is being replaced
    fn initialize_phis(
        &self,
        function: &mut Function<Empty>,
        phi_blocks: &HashMap<ValueId, HashSet<BlockId>>,
    ) -> HashMap<BlockId, Vec<(ValueId, ValueId)>> {
        let mut result: HashMap<BlockId, Vec<(ValueId, ValueId)>> = HashMap::new();
        for (value, blocks) in phi_blocks {
            for block in blocks {
                let param = function.add_parameter(
                    *block,
                    function.get_value_type(*value).unwrap().get_pointed(),
                );
                result.entry(*block).or_default().push((param, *value));
            }
        }
        result
    }

    fn find_pointer_writes(&self, function: &Function<Empty>) -> HashMap<ValueId, HashSet<BlockId>> {
        let mut writes: HashMap<ValueId, HashSet<BlockId>> = HashMap::new();
        for (block_id, block) in function.get_blocks() {
            for instruction in block.get_instructions() {
                match instruction {
                    OpCode::Store(lhs, _) => {
                        writes.entry(*lhs).or_default().insert(*block_id);
                    }
                    _ => {}
                }
            }
        }
        writes
    }

    fn find_phi_blocks(
        &self,
        writes: &HashMap<ValueId, HashSet<BlockId>>,
        cfg: &CFG,
    ) -> HashMap<ValueId, HashSet<BlockId>> {
        let mut result: HashMap<ValueId, HashSet<BlockId>> = HashMap::new();

        for (var, writes) in writes {
            let mut queue = VecDeque::<BlockId>::new();
            let mut visited = HashSet::<BlockId>::new();
            queue.extend(writes);

            while let Some(block) = queue.pop_front() {
                if visited.contains(&block) {
                    continue;
                }
                visited.insert(block);

                for block in cfg.get_dominance_frontier(block) {
                    result.entry(*var).or_default().insert(block);
                    queue.push_back(block);
                }
            }
        }

        result
    }

    // This is _very_ crude. We give up on mem2reg for the entire function
    // if we detect _any_ pointer escaping or entering the function, or being
    // written to another pointer. Obviously this needs a better implementation.
    fn escape_safe(&self, function: &Function<Empty>) -> bool {
        for (_, block) in function.get_blocks() {
            for (_, typ) in block.get_parameters() {
                if self.type_contains_ptr(typ) {
                    return false;
                }
            }

            for instruction in block.get_instructions() {
                match instruction {
                    OpCode::Store(_, r) => {
                        let rtyp = function.get_value_type(*r).unwrap();
                        if self.type_contains_ptr(rtyp) {
                            return false;
                        }
                    }
                    OpCode::Call(rets, _, args) => {
                        for v in rets.iter().chain(args.iter()) {
                            let vtyp = function.get_value_type(*v).unwrap();
                            if self.type_contains_ptr(vtyp) {
                                return false;
                            }
                        }
                    }
                    _ => {}
                }
            }

            match block.get_terminator() {
                Some(Terminator::Return(vals)) => {
                    for v in vals {
                        let vtyp = function.get_value_type(*v).unwrap();
                        if self.type_contains_ptr(vtyp) {
                            return false;
                        }
                    }
                }
                _ => {}
            }
        }

        true
    }

    fn type_contains_ptr(&self, typ: &Type<Empty>) -> bool {
        match typ {
            Type {
                expr: TypeExpr::Ref(_),
                ..
            } => true,
            Type {
                expr: TypeExpr::Array(inner, _),
                ..
            } => self.type_contains_ptr(inner),
            _ => false,
        }
    }
}
