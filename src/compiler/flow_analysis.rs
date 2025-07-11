use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::io::Write;
use std::process::Command;

use petgraph::Direction;
use petgraph::algo::dominators::{self, Dominators};
use petgraph::graph::{DiGraph, NodeIndex};
use petgraph::visit::{Bfs, DfsPostOrder, EdgeRef, Walker};

use crate::compiler::ssa::{BlockId, FunctionId, OpCode, SSA, Terminator};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum JumpType {
    Entry,
    Jmp,
    JmpIf,
    Return,
}

#[derive(Debug, Clone)]
pub struct CFGData {
    cfg: DiGraph<(), JumpType>,
    dominators: Dominators<NodeIndex<u32>>,
    dominator_post_order: Vec<NodeIndex<u32>>,
    node_dominator_post_order: HashMap<NodeIndex<u32>, usize>,
    dominator_pre_order: Vec<NodeIndex<u32>>,
    node_dominator_pre_order: HashMap<NodeIndex<u32>, usize>,
}

impl CFGData {
    pub fn from_graph(cfg: DiGraph<(), JumpType>, entry: NodeIndex<u32>) -> Self {
        let dominators = dominators::simple_fast(&cfg, entry);
        let mut preorder = Vec::new();
        let mut postorder = Vec::new();
        let mut preorder_map = HashMap::new();
        let mut postorder_map = HashMap::new();
        Self::compute_dominator_traversals(
            entry,
            &dominators,
            &mut preorder,
            &mut postorder,
            &mut preorder_map,
            &mut postorder_map,
        );

        Self {
            cfg,
            dominators,
            dominator_post_order: postorder,
            node_dominator_post_order: postorder_map,
            dominator_pre_order: preorder,
            node_dominator_pre_order: preorder_map,
        }
    }

    fn compute_dominator_traversals(
        entry: NodeIndex<u32>,
        dominators: &Dominators<NodeIndex<u32>>,
        preorder: &mut Vec<NodeIndex<u32>>,
        postorder: &mut Vec<NodeIndex<u32>>,
        preorder_map: &mut HashMap<NodeIndex<u32>, usize>,
        postorder_map: &mut HashMap<NodeIndex<u32>, usize>,
    ) {
        preorder_map.insert(entry, preorder.len());
        preorder.push(entry);
        for child in dominators.immediately_dominated_by(entry) {
            if entry == child {
                continue;
            }
            Self::compute_dominator_traversals(
                child,
                &dominators,
                preorder,
                postorder,
                preorder_map,
                postorder_map,
            );
        }
        postorder_map.insert(entry, postorder.len());
        postorder.push(entry);
    }

    pub fn dominates(&self, a: NodeIndex<u32>, b: NodeIndex<u32>) -> bool {
        self.node_dominator_pre_order[&a] <= self.node_dominator_pre_order[&b]
            && self.node_dominator_post_order[&a] >= self.node_dominator_post_order[&b]
    }
}

struct CFGBuilder {
    cfg: DiGraph<(), JumpType>,
    block_to_node: HashMap<BlockId, NodeIndex<u32>>,
    node_to_block: HashMap<NodeIndex<u32>, BlockId>,
    entry_node: NodeIndex<u32>,
    return_node: NodeIndex<u32>,
}

impl CFGBuilder {
    pub fn new() -> Self {
        let mut cfg = DiGraph::new();
        let entry_node = cfg.add_node(());
        let return_node = cfg.add_node(());
        Self {
            cfg,
            block_to_node: HashMap::new(),
            node_to_block: HashMap::new(),
            entry_node,
            return_node,
        }
    }

    pub fn add_jump(&mut self, source: BlockId, target: BlockId, jump_type: JumpType) {
        let source_node = *self
            .block_to_node
            .entry(source)
            .or_insert_with(|| self.cfg.add_node(()));
        self.node_to_block.insert(source_node, source);
        let target_node = *self
            .block_to_node
            .entry(target)
            .or_insert_with(|| self.cfg.add_node(()));
        self.node_to_block.insert(target_node, target);
        self.cfg.add_edge(source_node, target_node, jump_type);
    }

    pub fn set_entry(&mut self, block_id: BlockId) {
        let node = *self.block_to_node.get(&block_id).unwrap();
        self.cfg.add_edge(self.entry_node, node, JumpType::Entry);
    }

    pub fn add_block(&mut self, block_id: BlockId) {
        let node = *self
            .block_to_node
            .entry(block_id)
            .or_insert_with(|| self.cfg.add_node(()));
        self.node_to_block.insert(node, block_id);
    }

    pub fn add_return(&mut self, block_id: BlockId) {
        let node = *self
            .block_to_node
            .entry(block_id)
            .or_insert_with(|| self.cfg.add_node(()));
        self.node_to_block.insert(node, block_id);
        self.cfg.add_edge(node, self.return_node, JumpType::Return);
    }

    pub fn build(self) -> CFG {
        let cfg_data = CFGData::from_graph(self.cfg.clone(), self.entry_node);
        let mut reverse_cfg = self.cfg;
        reverse_cfg.reverse();
        let reverse_cfg_data = CFGData::from_graph(reverse_cfg, self.return_node);
        CFG {
            entry_node: self.entry_node,
            return_node: self.return_node,
            block_to_node: self.block_to_node,
            node_to_block: self.node_to_block,
            cfg: cfg_data,
            reverse_cfg: reverse_cfg_data,
        }
    }
}

#[derive(Debug, Clone)]
pub struct CFG {
    entry_node: NodeIndex<u32>,
    return_node: NodeIndex<u32>,
    block_to_node: HashMap<BlockId, NodeIndex<u32>>,
    node_to_block: HashMap<NodeIndex<u32>, BlockId>,
    cfg: CFGData,
    reverse_cfg: CFGData,
}

impl CFG {
    pub fn get_blocks_bfs(&self) -> impl Iterator<Item = BlockId> {
        Bfs::new(&self.cfg.cfg, self.entry_node)
            .iter(&self.cfg.cfg)
            .filter_map(|node| self.node_to_block.get(&node).cloned())
    }

    pub fn is_loop_entry(&self, block_id: BlockId) -> bool {
        let node = *self.block_to_node.get(&block_id).unwrap();
        for predecessor in self.predecessors(node) {
            if self.cfg.dominates(node, predecessor) {
                return true;
            }
        }
        false
    }

    fn predecessors(&self, node: NodeIndex<u32>) -> impl Iterator<Item = NodeIndex<u32>> {
        self.cfg
            .cfg
            .edges_directed(node, Direction::Incoming)
            .map(|edge| edge.source())
    }

    fn get_merge_point_node(&self, node: NodeIndex<u32>) -> NodeIndex {
        self.reverse_cfg
            .dominators
            .immediate_dominator(node)
            .unwrap()
    }

    pub fn get_merge_point(&self, block_id: BlockId) -> BlockId {
        let node = *self.block_to_node.get(&block_id).unwrap();
        *self
            .node_to_block
            .get(&self.get_merge_point_node(node))
            .unwrap()
    }

    pub fn get_if_body(&self, block_id: BlockId) -> Vec<BlockId> {
        let entry = *self.block_to_node.get(&block_id).unwrap();
        let merge = self.get_merge_point_node(entry);
        let mut result = Vec::new();
        for node in self.cfg.cfg.node_indices() {
            if self.cfg.dominates(entry, node) && self.reverse_cfg.dominates(merge, node) {
                result.push(*self.node_to_block.get(&node).unwrap());
            }
        }
        result
    }

    pub fn get_jumps_into_merge_from_branch(&self, branch: BlockId, merge: BlockId) -> Vec<BlockId> {
        let branch_id = *self.block_to_node.get(&branch).unwrap();
        let merge_id = *self.block_to_node.get(&merge).unwrap();
        let mut result = Vec::new();
        for predecessor in self.predecessors(merge_id) {
            if self.cfg.dominates(branch_id, predecessor) {
                result.push(*self.node_to_block.get(&predecessor).unwrap());
            }
        }
        result
    }
}

#[derive(Debug, Clone)]
pub struct CallGraph {
    call_graph: DiGraph<(), ()>,
    func_to_node: HashMap<FunctionId, NodeIndex<u32>>,
    node_to_func: HashMap<NodeIndex<u32>, FunctionId>,
}

impl CallGraph {
    pub fn new() -> Self {
        CallGraph {
            call_graph: DiGraph::new(),
            func_to_node: HashMap::new(),
            node_to_func: HashMap::new(),
        }
    }

    pub fn add_call(&mut self, caller: FunctionId, callee: FunctionId) {
        let caller_node = *self.func_to_node.get(&caller).unwrap();
        let callee_node = *self.func_to_node.get(&callee).unwrap();
        self.call_graph.add_edge(caller_node, callee_node, ());
    }

    pub fn add_function(&mut self, func_id: FunctionId) {
        let node = *self
            .func_to_node
            .entry(func_id)
            .or_insert_with(|| self.call_graph.add_node(()));
        self.node_to_func.insert(node, func_id);
    }

    pub fn detect_loops(&self) -> Vec<Vec<FunctionId>> {
        petgraph::algo::kosaraju_scc(&self.call_graph)
            .into_iter()
            .filter(|scc| scc.len() > 1)
            .map(|scc| {
                scc.into_iter()
                    .map(|node| self.node_to_func[&node])
                    .collect()
            })
            .collect()
    }

    pub fn get_post_order(&self, main_fn_id: FunctionId) -> impl Iterator<Item = FunctionId> {
        DfsPostOrder::new(&self.call_graph, self.func_to_node[&main_fn_id])
            .iter(&self.call_graph)
            .filter_map(|node| self.node_to_func.get(&node).cloned())
    }
}

#[derive(Debug, Clone)]
pub struct FlowAnalysis {
    call_graph: CallGraph,
    pub function_cfgs: HashMap<FunctionId, CFG>,
}

impl FlowAnalysis {
    pub fn run(ssa: &SSA) -> Self {
        let mut call_graph = CallGraph::new();
        let mut function_cfgs = HashMap::new();

        for (func_id, _) in ssa.iter_functions() {
            call_graph.add_function(*func_id);
        }

        for (func_id, func) in ssa.iter_functions() {
            let mut cfg = CFGBuilder::new();

            for (block_id, _) in func.get_blocks() {
                cfg.add_block(*block_id);
            }

            cfg.set_entry(func.get_entry_id());

            for (block_id, block) in func.get_blocks() {
                if let Some(instruction) = block.get_terminator() {
                    match instruction {
                        Terminator::Jmp(target, _) => {
                            cfg.add_jump(*block_id, *target, JumpType::Jmp);
                        }
                        Terminator::JmpIf(_, t1, t2) => {
                            cfg.add_jump(*block_id, *t1, JumpType::JmpIf);
                            cfg.add_jump(*block_id, *t2, JumpType::JmpIf);
                        }
                        Terminator::Return(_) => {
                            cfg.add_return(*block_id);
                        }
                    }
                }
                for instruction in block.get_instructions() {
                    match instruction {
                        OpCode::Call(_, tgt_id, _) => {
                            call_graph.add_call(*func_id, *tgt_id);
                        }
                        _ => {}
                    }
                }
            }
            function_cfgs.insert(*func_id, cfg.build());
        }

        Self {
            call_graph,
            function_cfgs,
        }
    }

    pub fn get_call_graph(&self) -> &CallGraph {
        &self.call_graph
    }

    pub fn get_function_cfg(&self, function_id: FunctionId) -> &CFG {
        &self.function_cfgs[&function_id]
    }

    // pub fn get_post_dominator_tree(&self, function_id: FunctionId) -> Dominators<NodeIndex<u32>> {
    //     let cfg = self.function_cfgs.get(&function_id).unwrap();

    //     let cached = cfg.post_dominator_tree.borrow();
    //     if let Some(ref post_dominator_tree) = *cached {
    //         return post_dominator_tree.clone();
    //     }
    //     drop(cached);

    //     let mut rev_graph = cfg.cfg.clone();
    //     rev_graph.reverse();
    //     let post_dominator_tree = dominators::simple_fast(&rev_graph, cfg.return_node);

    //     let mut cache = cfg.post_dominator_tree.borrow_mut();
    //     *cache = Some(post_dominator_tree.clone());

    //     post_dominator_tree
    // }

    // pub fn get_dominator_tree(&self, function_id: FunctionId) -> Dominators<NodeIndex<u32>> {
    //     let cfg = self.function_cfgs.get(&function_id).unwrap();
    //     let cached = cfg.dominator_tree.borrow();
    //     if let Some(ref dominator_tree) = *cached {
    //         return dominator_tree.clone();
    //     }
    //     drop(cached);
    //     let dominator_tree = dominators::simple_fast(&cfg.cfg, cfg.entry_node);
    //     let mut cache = cfg.dominator_tree.borrow_mut();
    //     *cache = Some(dominator_tree.clone());
    //     dominator_tree
    // }

    // fn compute_merge_point(
    //     post_dom: &Dominators<NodeIndex<u32>>,
    //     mut blk1: NodeIndex<u32>,
    //     mut blk2: NodeIndex<u32>,
    // ) -> NodeIndex<u32> {
    //     let mut depth1 = Self::get_depth_in_post_dominator_tree(&post_dom, blk1);
    //     let mut depth2 = Self::get_depth_in_post_dominator_tree(&post_dom, blk2);
    //     if depth1 > depth2 {
    //         std::mem::swap(&mut blk1, &mut blk2);
    //         std::mem::swap(&mut depth1, &mut depth2);
    //     }
    //     let mut cur2 = Self::get_ancestor_in_post_dominator_tree(&post_dom, blk2, depth2 - depth1);
    //     let mut cur1 = blk1;
    //     while cur1 != cur2 {
    //         cur1 = post_dom.immediate_dominator(cur1).unwrap();
    //         cur2 = post_dom.immediate_dominator(cur2).unwrap();
    //     }
    //     cur1
    // }

    // pub fn initialize_jump_info(&mut self, function_id: FunctionId) {
    //     let dom = self.get_dominator_tree(function_id);
    //     let post_dom = self.get_post_dominator_tree(function_id);
    //     let cfg = self.function_cfgs.get_mut(&function_id).unwrap();

    //     for node in cfg.cfg.node_indices() {
    //         if node == cfg.entry_node || node == cfg.return_node {
    //             continue;
    //         }
    //         for edge in cfg.cfg.edges_directed(node, Direction::Outgoing) {
    //             if let Some(mut doms) = dom.dominators(node) {
    //                 if doms.any(|dom| dom == edge.target()) {
    //                     cfg.loop_entrys.push(cfg.node_to_block[&edge.target()]);
    //                 }
    //             }
    //         }
    //     }

    //     for node in cfg.cfg.node_indices() {
    //         if node == cfg.entry_node || node == cfg.return_node {
    //             continue;
    //         }
    //         if cfg.loop_entrys.contains(&cfg.node_to_block[&node]) {
    //             continue;
    //         }
    //         let outgoing_edges = cfg
    //             .cfg
    //             .edges_directed(node, Direction::Outgoing)
    //             .collect::<Vec<_>>();
    //         if outgoing_edges
    //             .iter()
    //             .any(|edge| edge.weight() == &JumpType::JmpIf)
    //         {
    //             assert!(outgoing_edges.len() == 2);
    //             let t1 = outgoing_edges[0].target();
    //             let t2 = outgoing_edges[1].target();
    //             let merge_point = Self::compute_merge_point(&post_dom, t1, t2);
    //             cfg.if_merge_points
    //                 .insert(cfg.node_to_block[&node], cfg.node_to_block[&merge_point]);
    //         }
    //     }
    // }

    // pub fn is_loop_entry(&self, function_id: FunctionId, block_id: BlockId) -> bool {
    //     let cfg = self.function_cfgs.get(&function_id).unwrap();
    //     cfg.loop_entrys.contains(&block_id)
    // }

    // pub fn get_merge_point(&self, function_id: FunctionId, block_id: BlockId) -> BlockId {
    //     let cfg = self.function_cfgs.get(&function_id).unwrap();
    //     *cfg.if_merge_points.get(&block_id).unwrap()
    // }

    // pub fn get_if_body(&self, function_id: FunctionId, entry_id: BlockId) -> Vec<BlockId> {
    //     // The body of an if contains all blocks that are dominated by the entry
    //     // and post-dominated by the merge point.
    //     let cfg = self.function_cfgs.get(&function_id).unwrap();
    //     let post_dom = self.get_post_dominator_tree(function_id);
    //     let dom = self.get_dominator_tree(function_id);
    //     let mut result = Vec::new();
    //     let merge_point = cfg.block_to_node[&cfg.if_merge_points.get(&entry_id).unwrap()];
    //     let entry_node = cfg.block_to_node[&entry_id];
    //     for node in cfg.cfg.node_indices() {
    //         if node == entry_node || node == merge_point {
    //             continue;
    //         }
    //         let Some(mut post_doms) = post_dom.dominators(node) else {
    //             continue;
    //         };
    //         let Some(mut doms) = dom.dominators(node) else {
    //             continue;
    //         };
    //         if doms.any(|dom| dom == entry_node)
    //             && post_doms.any(|post_dom| post_dom == merge_point)
    //         {
    //             result.push(cfg.node_to_block[&node]);
    //         }
    //     }
    //     result
    // }

    // fn get_depth_in_post_dominator_tree(
    //     post_dom: &Dominators<NodeIndex<u32>>,
    //     node: NodeIndex<u32>,
    // ) -> u32 {
    //     let mut depth = 0;
    //     let mut current = node;
    //     while let Some(parent) = post_dom.immediate_dominator(current) {
    //         depth += 1;
    //         current = parent;
    //     }
    //     depth
    // }

    // fn get_ancestor_in_post_dominator_tree(
    //     post_dom: &Dominators<NodeIndex<u32>>,
    //     node: NodeIndex<u32>,
    //     depth: u32,
    // ) -> NodeIndex<u32> {
    //     let mut current = node;
    //     for _ in 0..depth {
    //         current = post_dom.immediate_dominator(current).unwrap();
    //     }
    //     current
    // }

    // pub fn get_blocks_bfs(&self, function_id: FunctionId) -> impl Iterator<Item = BlockId> {
    //     let cfg = self.function_cfgs.get(&function_id).unwrap();
    //     Bfs::new(&cfg.cfg, cfg.entry_node)
    //         .iter(&cfg.cfg)
    //         .filter_map(|node| cfg.node_to_block.get(&node).cloned())
    // }

    // pub fn to_graphviz(&self) -> String {
    //     let mut dot = String::new();
    //     dot.push_str("digraph FlowAnalysis {\n");
    //     dot.push_str("  rankdir=TB;\n");
    //     dot.push_str("  compound=true;\n");
    //     dot.push_str("  node [shape=box];\n\n");

    //     for (func_id, _) in &self.function_cfgs {
    //         dot.push_str(&format!(
    //             "  entry_{} [label=\"\", shape=point, style=invis];\n",
    //             func_id.0
    //         ));
    //         dot.push_str(&format!(
    //             "  return_{} [label=\"\", shape=point, style=invis];\n",
    //             func_id.0
    //         ));
    //     }

    //     dot.push_str("\n");

    //     dot.push_str("  { rank=source;\n");
    //     for (func_id, _) in &self.function_cfgs {
    //         dot.push_str(&format!("    entry_{};\n", func_id.0));
    //     }
    //     dot.push_str("  }\n\n");

    //     dot.push_str("  { rank=sink;\n");
    //     for (func_id, _) in &self.function_cfgs {
    //         dot.push_str(&format!("    return_{};\n", func_id.0));
    //     }
    //     dot.push_str("  }\n\n");

    //     dot.push_str("  subgraph cluster_call_graph {\n");
    //     dot.push_str("    label=\"Call Graph\";\n");
    //     dot.push_str("    style=filled;\n");
    //     dot.push_str("    color=lightgrey;\n");
    //     dot.push_str("    node [style=filled,color=white];\n");

    //     for (func_id, node_index) in &self.func_to_node {
    //         dot.push_str(&format!(
    //             "    func_{} [label=\"fn_{}\"];\n",
    //             func_id.0, func_id.0
    //         ));
    //     }

    //     for edge in self.call_graph.edge_indices() {
    //         let (source, target) = self.call_graph.edge_endpoints(edge).unwrap();
    //         let source_func = self.node_to_func[&source];
    //         let target_func = self.node_to_func[&target];
    //         dot.push_str(&format!(
    //             "    func_{} -> func_{};\n",
    //             source_func.0, target_func.0
    //         ));
    //     }

    //     dot.push_str("  }\n\n");

    //     for (func_id, cfg) in &self.function_cfgs {
    //         dot.push_str(&format!("  subgraph cluster_cfg_{} {{\n", func_id.0));
    //         dot.push_str(&format!("    label=\"CFG fn_{}\";\n", func_id.0));
    //         dot.push_str("    style=filled;\n");
    //         dot.push_str("    color=lightblue;\n");
    //         dot.push_str("    node [style=filled,color=white];\n");

    //         for (block_id, node_index) in &cfg.block_to_node {
    //             dot.push_str(&format!(
    //                 "    block_{}_{} [label=\"block_{}\"];\n",
    //                 func_id.0, block_id.0, block_id.0
    //             ));
    //         }

    //         for edge in cfg.cfg.edge_indices() {
    //             let (source, target) = cfg.cfg.edge_endpoints(edge).unwrap();
    //             let edge_weight = &cfg.cfg[edge];
    //             match edge_weight {
    //                 JumpType::Jmp => {
    //                     let source_block = cfg.node_to_block[&source];
    //                     let target_block = cfg.node_to_block[&target];
    //                     dot.push_str(&format!(
    //                         "    block_{}_{} -> block_{}_{};\n",
    //                         func_id.0, source_block.0, func_id.0, target_block.0
    //                     ));
    //                 }
    //                 JumpType::JmpIf => {
    //                     let source_block = cfg.node_to_block[&source];
    //                     let target_block = cfg.node_to_block[&target];
    //                     dot.push_str(&format!(
    //                         "    block_{}_{} -> block_{}_{} [color=red];\n",
    //                         func_id.0, source_block.0, func_id.0, target_block.0
    //                     ));
    //                 }
    //                 _ => {} // Skip Entry and Return edges - they'll be handled outside
    //             }
    //         }

    //         dot.push_str("  }\n\n");
    //     }

    //     // Add entry and return edges outside the subgraphs
    //     for (func_id, cfg) in &self.function_cfgs {
    //         for edge in cfg.cfg.edge_indices() {
    //             let (source, target) = cfg.cfg.edge_endpoints(edge).unwrap();
    //             let edge_weight = &cfg.cfg[edge];
    //             match edge_weight {
    //                 JumpType::Return => {
    //                     let source_block = cfg.node_to_block[&source];
    //                     dot.push_str(&format!(
    //                         "  block_{}_{} -> return_{} [style=dashed, color=red];\n",
    //                         func_id.0, source_block.0, func_id.0
    //                     ));
    //                 }
    //                 JumpType::Entry => {
    //                     let target_block = cfg.node_to_block[&target];
    //                     dot.push_str(&format!(
    //                         "  entry_{} -> block_{}_{} [style=dashed, color=green];\n",
    //                         func_id.0, func_id.0, target_block.0
    //                     ));
    //                 }
    //                 _ => {} // Skip Jmp and JmpIf edges - they're handled inside subgraphs
    //             }
    //         }
    //     }

    //     dot.push_str("}\n");
    //     dot
    // }

    // pub fn save_as_png(&self, filename: &str) -> Result<(), String> {
    //     let dot_content = self.to_graphviz();

    //     let temp_dot_file = format!("{}.dot", filename);
    //     let mut file = fs::File::create(&temp_dot_file)
    //         .map_err(|e| format!("Failed to create temporary dot file: {}", e))?;

    //     file.write_all(dot_content.as_bytes())
    //         .map_err(|e| format!("Failed to write dot content: {}", e))?;

    //     let output = Command::new("dot")
    //         .args(&["-Tpng", &temp_dot_file, "-o", &format!("{}.png", filename)])
    //         .output()
    //         .map_err(|e| format!("Failed to execute dot command: {}", e))?;

    //     if !output.status.success() {
    //         let stderr = String::from_utf8_lossy(&output.stderr);
    //         return Err(format!("dot command failed: {}", stderr));
    //     }

    //     fs::remove_file(&temp_dot_file)
    //         .map_err(|e| format!("Failed to remove temporary dot file: {}", e))?;

    //     Ok(())
    // }
}
