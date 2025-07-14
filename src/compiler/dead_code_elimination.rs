use std::collections::{HashMap, HashSet};

use crate::compiler::{
    flow_analysis::{CFG, FlowAnalysis},
    ir::r#type::Empty,
    ssa::{BlockId, Function, OpCode, SSA, Terminator, ValueId},
};

pub struct DCE {}

#[derive(Debug)]
enum WorkItem {
    LiveBlock(BlockId),
    LiveValue(ValueId),
    LiveInstruction(BlockId, usize),
}

enum ValueDefinition {
    Param(BlockId, usize),
    Instruction(BlockId, usize),
    Const(ValueId),
}

impl DCE {
    pub fn new() -> Self {
        Self {}
    }

    pub fn run(&mut self, ssa: &mut SSA<Empty>, cfg: &FlowAnalysis) {
        for (function_id, function) in ssa.iter_functions_mut() {
            println!("DCE: function {:?}", function_id);
            let cfg = cfg.get_function_cfg(*function_id);
            let definitions = self.generate_definitions(function);

            let mut live_values: HashSet<ValueId> = HashSet::new();
            let mut live_blocks: HashSet<BlockId> = HashSet::new();
            let mut live_instructions: HashMap<BlockId, HashSet<usize>> = HashMap::new();
            let mut live_params: HashMap<BlockId, HashSet<usize>> = HashMap::new();
            let mut live_branches: HashSet<BlockId> = HashSet::new();
            let mut live_consts: HashSet<ValueId> = HashSet::new();

            let mut worklist: Vec<WorkItem> = vec![];

            for (parameter, _) in function.get_entry().get_parameters() {
                // All function parameters are live
                worklist.push(WorkItem::LiveValue(*parameter));
            }

            for (block_id, block) in function.get_blocks() {
                for (i, instruction) in block.get_instructions().enumerate() {
                    match instruction {
                        // calls, stores, constraints and witness stores are critical side-effects
                        OpCode::Call { .. } | OpCode::Store { .. } | OpCode::Constrain { .. } => {
                            worklist.push(WorkItem::LiveInstruction(*block_id, i));
                        }
                        // assert_eq is critical if it's not definitionally true
                        OpCode::AssertEq(lhs, rhs) => {
                            if lhs != rhs {
                                worklist.push(WorkItem::LiveInstruction(*block_id, i));
                            }
                        }
                        OpCode::Load { .. }
                        | OpCode::Add { .. }
                        | OpCode::Mul { .. }
                        | OpCode::Eq { .. }
                        | OpCode::Alloc { .. }
                        | OpCode::Lt { .. }
                        | OpCode::WriteWitness { .. } // Note that a witness store is only critical if the return is used
                        | OpCode::ArrayGet { .. } => {}
                    }
                }

                if let Some(terminator) = block.get_terminator() {
                    match terminator {
                        Terminator::Return(values) => {
                            worklist.push(WorkItem::LiveBlock(*block_id));
                            for value in values {
                                worklist.push(WorkItem::LiveValue(*value));
                            }
                        }
                        _ => {}
                    }
                }
            }

            while let Some(item) = worklist.pop() {
                // println!("Item: {:?}", item);
                match item {
                    WorkItem::LiveBlock(block_id) => {
                        if live_blocks.contains(&block_id) {
                            continue;
                        }
                        live_blocks.insert(block_id);

                        // All blocks in the post-domination frontier are live,
                        // because they decide whether or not this block is entered.
                        // Also, the condition on which they enter is live.
                        for pd in cfg.get_post_dominance_frontier(block_id) {
                            println!(
                                "Aliving block {:?} because it's in the post-dom frontier of {:?}",
                                pd, block_id
                            );
                            worklist.push(WorkItem::LiveBlock(pd));
                            live_branches.insert(pd);

                            match function.get_block(pd).get_terminator() {
                                Some(Terminator::JmpIf(condition, _, _)) => {
                                    worklist.push(WorkItem::LiveValue(*condition));
                                }
                                _ => panic!("ICE: It's a frontier, must end with a conditional"),
                            }
                        }

                        // If the block has parameters, all predecessor become
                        // live, as they define the phi inputs.
                        if function.get_block(block_id).has_parameters() {
                            for predecessor in cfg.get_jumps_into(block_id) {
                                println!(
                                    "Aliving block {:?} because it jumps into {:?} with phi",
                                    predecessor, block_id
                                );
                                worklist.push(WorkItem::LiveBlock(predecessor));
                            }
                        }
                    }
                    WorkItem::LiveValue(value_id) => {
                        if live_values.contains(&value_id) {
                            continue;
                        }
                        live_values.insert(value_id);

                        let definition = definitions.get(&value_id).unwrap();
                        match definition {
                            ValueDefinition::Param(block_id, i) => {
                                if live_params
                                    .get(block_id)
                                    .unwrap_or(&HashSet::new())
                                    .contains(i)
                                {
                                    continue;
                                }
                                live_params
                                    .entry(*block_id)
                                    .or_insert(HashSet::new())
                                    .insert(*i);

                                // The defining block is live
                                println!(
                                    "Aliving block {:?} because it defines {:?}",
                                    block_id, value_id
                                );
                                worklist.push(WorkItem::LiveBlock(*block_id));
                                // For all jumps into it, the respective argument is live
                                for block_id in cfg.get_jumps_into(*block_id) {
                                    let jumpin_block = function.get_block(block_id);
                                    match jumpin_block.get_terminator() {
                                        Some(Terminator::Jmp(_, params)) => {
                                            worklist.push(WorkItem::LiveValue(params[*i]));
                                        }
                                        _ => panic!(
                                            "ICE: the block has phis, so jumps into it must be Jmps"
                                        ),
                                    }
                                }
                            }
                            ValueDefinition::Instruction(block_id, i) => {
                                // The instruction is live
                                if block_id.0 == 1 && *i == 0 {
                                    println!(
                                        "Aliving instruction {:?} in block {:?} because it defines {:?}",
                                        i, block_id, value_id
                                    );
                                }
                                worklist.push(WorkItem::LiveInstruction(*block_id, *i));
                            }
                            ValueDefinition::Const(value_id) => {
                                live_consts.insert(*value_id);
                            }
                        }
                    }
                    WorkItem::LiveInstruction(block_id, i) => {
                        if live_instructions
                            .get(&block_id)
                            .unwrap_or(&HashSet::new())
                            .contains(&i)
                        {
                            continue;
                        }
                        live_instructions
                            .entry(block_id)
                            .or_insert(HashSet::new())
                            .insert(i);

                        // The containing block is live
                        println!(
                            "Aliving block {:?} because it contains live instruction {:?}",
                            block_id, i
                        );
                        worklist.push(WorkItem::LiveBlock(block_id));

                        let instruction = function.get_block(block_id).get_instruction(i);
                        for input in instruction.get_inputs() {
                            worklist.push(WorkItem::LiveValue(*input));
                        }
                    }
                }
            }

            // println!("Live params: {:?}", live_params);

            for value_id in function.iter_consts().map(|(v, _)| *v).collect::<Vec<_>>() {
                if !live_consts.contains(&value_id) {
                    function.remove_const(value_id);
                }
            }

            for block_id in cfg.get_domination_pre_order() {
                let mut block = function.take_block(block_id);
                if !live_blocks.contains(&block_id) {
                    continue;
                }

                let instructions = block.take_instructions();
                let mut new_instructions = vec![];

                for (i, instruction) in instructions.into_iter().enumerate() {
                    if live_instructions
                        .get(&block_id)
                        .unwrap_or(&HashSet::new())
                        .contains(&i)
                    {
                        new_instructions.push(instruction);
                    }
                }

                block.put_instructions(new_instructions);

                let new_terminator = match block.take_terminator() {
                    Some(Terminator::Jmp(target, params)) => {
                        if live_blocks.contains(&target) {
                            let mut new_params = vec![];
                            for (i, param) in params.into_iter().enumerate() {
                                // println!("Jump from {:?} to {:?}", block_id, target);
                                if live_params
                                    .get(&target)
                                    .unwrap_or(&HashSet::new())
                                    .contains(&i)
                                {
                                    // println!("Keeping param {:?}", param);
                                    new_params.push(param);
                                }
                            }
                            Terminator::Jmp(target, new_params)
                        } else {
                            let new_target =
                                self.closest_live_post_dominator(cfg, block_id, &live_blocks);
                            // we can safely jump without params – blocks with params are post-dominated
                            // by their phi-setting blocks, so we wouldn't find one here.
                            Terminator::Jmp(new_target, vec![])
                        }
                    }
                    Some(Terminator::JmpIf(condition, then, otherwise)) => {
                        if live_branches.contains(&block_id) {
                            Terminator::JmpIf(
                                condition,
                                self.closest_live_block(cfg, then, &live_blocks),
                                self.closest_live_block(cfg, otherwise, &live_blocks),
                            )
                        } else {
                            Terminator::Jmp(
                                self.closest_live_post_dominator(cfg, block_id, &live_blocks),
                                // Again, the jump is parameterless – live blocks with params are
                                // post-dominated by the phi-setting blocks which are all live, but this
                                // block ended with a conditional jump, so it wasn't setting phis.
                                vec![],
                            )
                        }
                    }
                    Some(Terminator::Return(values)) => {
                        let mut new_values = vec![];
                        for value in values.into_iter() {
                            if live_values.contains(&value) {
                                new_values.push(value);
                            }
                        }
                        Terminator::Return(new_values)
                    }
                    None => panic!("ICE: block has no terminator"),
                };

                block.set_terminator(new_terminator);

                let params = block.take_parameters();
                let mut new_params = vec![];
                for (i, param) in params.into_iter().enumerate() {
                    if live_params
                        .get(&block_id)
                        .unwrap_or(&HashSet::new())
                        .contains(&i)
                    {
                        new_params.push(param);
                    }
                }
                block.put_parameters(new_params);

                function.put_block(block_id, block);
            }
        }
    }

    fn generate_definitions(&self, ssa: &Function<Empty>) -> HashMap<ValueId, ValueDefinition> {
        let mut definitions = HashMap::new();

        for (value_id, _) in ssa.iter_consts() {
            definitions.insert(*value_id, ValueDefinition::Const(*value_id));
        }

        for (block_id, block) in ssa.get_blocks() {
            for (i, (val, _)) in block.get_parameters().enumerate() {
                definitions.insert(*val, ValueDefinition::Param(*block_id, i));
            }

            for (i, instruction) in block.get_instructions().enumerate() {
                for val in instruction.get_results() {
                    definitions.insert(*val, ValueDefinition::Instruction(*block_id, i));
                }
            }
        }

        definitions
    }

    fn closest_live_block(
        &self,
        cfg: &CFG,
        block_id: BlockId,
        live_blocks: &HashSet<BlockId>,
    ) -> BlockId {
        if live_blocks.contains(&block_id) {
            return block_id;
        }
        return self.closest_live_post_dominator(cfg, block_id, live_blocks);
    }

    fn closest_live_post_dominator(
        &self,
        cfg: &CFG,
        block_id: BlockId,
        live_blocks: &HashSet<BlockId>,
    ) -> BlockId {
        let mut current_block = cfg.get_post_dominator(block_id);
        while !live_blocks.contains(&current_block) {
            current_block = cfg.get_post_dominator(current_block);
        }
        current_block
    }
}
