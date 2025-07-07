use std::collections::{HashMap, HashSet};
use std::process::Command;
use std::fs;
use std::io::Write;

use petgraph::graph::{DiGraph, NodeIndex};

use crate::compiler::ssa::{BlockId, FunctionId, OpCode, SSA, Terminator};

#[derive(Debug, Clone)]
pub enum JumpType {
    Jmp,
    JmpIf,
}

#[derive(Debug, Clone)]
pub struct FunctionCFG {
    block_to_node: HashMap<BlockId, NodeIndex<u32>>,
    node_to_block: HashMap<NodeIndex<u32>, BlockId>,
    return_blocks: HashSet<BlockId>,
    entry_block: BlockId,
    cfg: DiGraph<(), JumpType>,
}

impl FunctionCFG {
    pub fn new() -> Self {
        FunctionCFG {
            block_to_node: HashMap::new(),
            node_to_block: HashMap::new(),
            return_blocks: HashSet::new(),
            entry_block: BlockId(0),
            cfg: DiGraph::new(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FlowAnalysis {
    func_to_node: HashMap<FunctionId, NodeIndex<u32>>,
    node_to_func: HashMap<NodeIndex<u32>, FunctionId>,
    call_graph: DiGraph<(), ()>,
    function_cfgs: HashMap<FunctionId, FunctionCFG>,
}

impl FlowAnalysis {
    pub fn new() -> Self {
        FlowAnalysis {
            func_to_node: HashMap::new(),
            node_to_func: HashMap::new(),
            call_graph: DiGraph::new(),
            function_cfgs: HashMap::new(),
        }
    }

    pub fn run(&mut self, ssa: &SSA) {
        for (func_id, func) in ssa.iter_functions() {
            let node = self.call_graph.add_node(());
            self.func_to_node.insert(*func_id, node);
            self.node_to_func.insert(node, *func_id);
        }

        for (func_id, func) in ssa.iter_functions() {
            let mut cfg = FunctionCFG::new();

            for (block_id, _) in func.get_blocks() {
                let node = cfg.cfg.add_node(());
                cfg.block_to_node.insert(*block_id, node);
                cfg.node_to_block.insert(node, *block_id);
            }

            cfg.entry_block = func.get_entry_id();

            for (block_id, block) in func.get_blocks() {
                if let Some(instruction) = block.get_terminator() {
                    match instruction {
                        Terminator::Jmp(target, _) => {
                            cfg.cfg.add_edge(
                                cfg.block_to_node[&*block_id],
                                cfg.block_to_node[&*target],
                                JumpType::Jmp,
                            );
                        }
                        Terminator::JmpIf(_, t1, t2) => {
                            cfg.cfg.add_edge(
                                cfg.block_to_node[&*block_id],
                                cfg.block_to_node[&*t1],
                                JumpType::JmpIf,
                            );
                            cfg.cfg.add_edge(
                                cfg.block_to_node[&*block_id],
                                cfg.block_to_node[&*t2],
                                JumpType::JmpIf,
                            );
                        }
                        Terminator::Return(_) => {
                            cfg.return_blocks.insert(*block_id);
                        }
                    }
                }
                for instruction in block.get_instructions() {
                    match instruction {
                        OpCode::Call(_, tgt_id, _) => {
                            self.call_graph.add_edge(
                                self.func_to_node[&*func_id],
                                self.func_to_node[&*tgt_id],
                                (),
                            );
                        }
                        _ => {}
                    }
                }
            }
            self.function_cfgs.insert(*func_id, cfg);
        }
    }

    /// Generate a Graphviz dot representation of the flow analysis
    pub fn to_graphviz(&self) -> String {
        let mut dot = String::new();
        dot.push_str("digraph FlowAnalysis {\n");
        dot.push_str("  rankdir=TB;\n");
        dot.push_str("  compound=true;\n");
        dot.push_str("  node [shape=box];\n\n");

        // Call graph subgraph
        dot.push_str("  subgraph cluster_call_graph {\n");
        dot.push_str("    label=\"Call Graph\";\n");
        dot.push_str("    style=filled;\n");
        dot.push_str("    color=lightgrey;\n");
        dot.push_str("    node [style=filled,color=white];\n");

        // Add function nodes to call graph
        for (func_id, node_index) in &self.func_to_node {
            dot.push_str(&format!("    func_{} [label=\"fn_{}\"];\n", func_id.0, func_id.0));
        }

        // Add call edges
        for edge in self.call_graph.edge_indices() {
            let (source, target) = self.call_graph.edge_endpoints(edge).unwrap();
            let source_func = self.node_to_func[&source];
            let target_func = self.node_to_func[&target];
            dot.push_str(&format!(
                "    func_{} -> func_{};\n",
                source_func.0, target_func.0
            ));
        }

        dot.push_str("  }\n\n");

        // Function CFG subgraphs
        for (func_id, cfg) in &self.function_cfgs {
            dot.push_str(&format!("  subgraph cluster_cfg_{} {{\n", func_id.0));
            dot.push_str(&format!("    label=\"CFG fn_{}\";\n", func_id.0));
            dot.push_str("    style=filled;\n");
            dot.push_str("    color=lightblue;\n");
            dot.push_str("    node [style=filled,color=white];\n");

            // Add block nodes
            for (block_id, node_index) in &cfg.block_to_node {
                dot.push_str(&format!(
                    "    block_{}_{} [label=\"block_{}\"];\n",
                    func_id.0, block_id.0, block_id.0
                ));
            }

            // Add control flow edges
            for edge in cfg.cfg.edge_indices() {
                let (source, target) = cfg.cfg.edge_endpoints(edge).unwrap();
                let source_block = cfg.node_to_block[&source];
                let target_block = cfg.node_to_block[&target];
                let edge_weight = &cfg.cfg[edge];
                match edge_weight {
                    JumpType::Jmp => {
                        dot.push_str(&format!(
                            "    block_{}_{} -> block_{}_{};\n",
                            func_id.0, source_block.0, func_id.0, target_block.0
                        ));
                    }
                    JumpType::JmpIf => {
                        dot.push_str(&format!(
                            "    block_{}_{} -> block_{}_{} [color=red];\n",
                            func_id.0, source_block.0, func_id.0, target_block.0
                        ));
                    }
                }
            }

            dot.push_str("  }\n\n");

            // Add entry arrow for entry block
            dot.push_str(&format!(
                "  entry_{} -> block_{}_{} [style=dashed, color=green];\n",
                func_id.0, func_id.0, cfg.entry_block.0
            ));

            // Add return arrows for return blocks
            for return_block_id in &cfg.return_blocks {
                dot.push_str(&format!(
                    "  block_{}_{} -> return_{} [style=dashed, color=red];\n",
                    func_id.0, return_block_id.0, func_id.0
                ));
            }
        }

        // Add entry and return nodes (invisible nodes for arrows to point to/from)
        for (func_id, _) in &self.function_cfgs {
            dot.push_str(&format!(
                "  entry_{} [label=\"\", shape=point, style=invis];\n",
                func_id.0
            ));
            dot.push_str(&format!(
                "  return_{} [label=\"\", shape=point, style=invis];\n",
                func_id.0
            ));
        }

        dot.push_str("}\n");
        dot
    }

    /// Generate a PNG image from the flow analysis Graphviz representation
    pub fn save_as_png(&self, filename: &str) -> Result<(), String> {
        let dot_content = self.to_graphviz();
        
        // Create a temporary dot file
        let temp_dot_file = format!("{}.dot", filename);
        let mut file = fs::File::create(&temp_dot_file)
            .map_err(|e| format!("Failed to create temporary dot file: {}", e))?;
        
        file.write_all(dot_content.as_bytes())
            .map_err(|e| format!("Failed to write dot content: {}", e))?;
        
        // Use dot command to generate PNG
        let output = Command::new("dot")
            .args(&["-Tpng", &temp_dot_file, "-o", &format!("{}.png", filename)])
            .output()
            .map_err(|e| format!("Failed to execute dot command: {}", e))?;
        
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(format!("dot command failed: {}", stderr));
        }
        
        // Clean up temporary dot file
        fs::remove_file(&temp_dot_file)
            .map_err(|e| format!("Failed to remove temporary dot file: {}", e))?;
        
        Ok(())
    }
}
