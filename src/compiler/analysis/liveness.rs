use std::collections::{HashMap, HashSet, VecDeque};

use tracing::{info, instrument};

use crate::compiler::{flow_analysis::{FlowAnalysis, CFG}, ssa::{BlockId, Function, FunctionId, Terminator, ValueId, SSA}, taint_analysis::ConstantTaint};


pub enum InstructionPosition {
    Offset(usize),
    Terminator,
}

pub struct InstructionPointer {
    pub position: InstructionPosition,
    pub block: BlockId,
}

pub struct FunctionLastUses {
    pub last_use_of_value: HashMap<ValueId, InstructionPointer>,
    pub values_to_drop: HashMap<InstructionPointer, HashSet<ValueId>>,
}

pub struct LastUses {
    pub function_last_uses: HashMap<FunctionId, FunctionLastUses>,
}

pub struct LivenessAnalysis {
}

impl LivenessAnalysis {
    pub fn new() -> Self {
        Self {}
    }

    #[instrument(skip_all, name = "LivenessAnalysis::run")]
    pub fn run(&self, ssa: &SSA<ConstantTaint>, cfg: &FlowAnalysis) -> LastUses {
        let mut result = LastUses {
            function_last_uses: HashMap::new(),
        };

        for (function_id, function) in ssa.iter_functions() {
            info!("Function {}", function.get_name());
            let function_last_uses = self.run_function(function, cfg.get_function_cfg(*function_id));
            result.function_last_uses.insert(*function_id, function_last_uses);
        }


        result
    }

    fn run_function(&self, function: &Function<ConstantTaint>, cfg: &CFG) -> FunctionLastUses {
        let mut gens = HashMap::<BlockId, HashSet<ValueId>>::new();
        let mut kills = HashMap::<BlockId, HashSet<ValueId>>::new();

        for (block_id, block) in function.get_blocks() {
            let mut k = HashSet::new();
            let mut g = HashSet::new();
            match block.get_terminator().unwrap() {
                Terminator::Return(vs) => {
                    for v in vs {
                        g.insert(*v);
                    }
                }
                Terminator::Jmp(_, params) => {
                    for v in params {
                        g.insert(*v);
                    }
                }
                Terminator::JmpIf(cond, _, _) => {
                    g.insert(*cond);
                }
            }

            for instr in block.get_instructions().rev() {
                for value_id in instr.get_inputs() {
                    g.insert(*value_id);
                }
                for value_id in instr.get_results() {
                    k.insert(*value_id);
                    g.remove(value_id);
                }
            }

            for (value_id, _) in block.get_parameters() {
                k.insert(*value_id);
            }

            gens.insert(*block_id, g);
            kills.insert(*block_id, k);
        }

        let mut live_in = HashMap::<BlockId, HashSet<ValueId>>::new();
        let mut live_out = HashMap::<BlockId, HashSet<ValueId>>::new();
        let mut queue = VecDeque::new();

        for ret in cfg.get_return_blocks() {
            queue.push_back(ret);
        }

        while let Some(block_id) = queue.pop_front() {
            let visited = live_in.contains_key(&block_id);
            live_in.entry(block_id).or_insert(HashSet::new());
            let original_live_in: &HashSet<ValueId> = live_in.get(&block_id).unwrap();


            let mut new_live_out: HashSet<ValueId> = HashSet::new();

            for block_id in cfg.get_successors(block_id) {
                new_live_out.extend(live_in.get(&block_id).unwrap_or(&HashSet::new()));
            }

            let mut new_live_in = new_live_out.clone();
            new_live_in.extend(gens.get(&block_id).unwrap_or(&HashSet::new()));
            let kills = kills.get(&block_id).unwrap();
            new_live_in.retain(|v| !kills.contains(v));

            live_out.insert(block_id, new_live_out.clone());
            if !visited || original_live_in != &new_live_in {
                for pred in cfg.get_predecessors(block_id) {
                    queue.push_back(pred);
                }
            }
            live_in.insert(block_id, new_live_in);

        }

        for (block_id, _) in function.get_blocks() {
            let live_in = live_in.get(&block_id).expect(&format!("live_in not found for block {}", block_id.0));
            let live_out = live_out.get(&block_id).expect(&format!("live_out not found for block {}", block_id.0));
            let last_uses = live_in.difference(live_out).cloned().collect::<Vec<_>>();

            info!("block {}", block_id.0);
            info!("live_in: {}", live_in.iter().map(|v| v.0.to_string()).collect::<Vec<_>>().join(", "));
            info!("live_out: {}", live_out.iter().map(|v| v.0.to_string()).collect::<Vec<_>>().join(", "));
            info!("last_uses: {}", last_uses.iter().map(|v| v.0.to_string()).collect::<Vec<_>>().join(", "));
        }

        FunctionLastUses {
            last_use_of_value: HashMap::new(),
            values_to_drop: HashMap::new(),
        }
    }
}