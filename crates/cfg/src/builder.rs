//! Generic CFG builder
//!
//! Builds a control flow graph from a sequence of instructions implementing
//! the [`InstructionInfo`] trait.

use std::collections::{HashMap, HashSet};

use petgraph::{algo::dominators, graph::DiGraph};

use crate::{
    graph::{BlockData, Cfg},
    InstructionInfo,
};

/// Build a CFG from a sequence of instructions.
///
/// The instructions must implement [`InstructionInfo`] to provide the
/// control flow information needed for CFG construction.
pub fn build_cfg<I: InstructionInfo>(instructions: &[I]) -> Cfg<I> {
    CfgBuilder::new(instructions).build()
}

/// Builder for constructing a CFG from instructions
struct CfgBuilder<'a, I: InstructionInfo> {
    instructions: &'a [I],
    graph: DiGraph<BlockData<I>, ()>,
    target_to_block: HashMap<I::Target, petgraph::graph::NodeIndex>,
    nodes: Vec<petgraph::graph::NodeIndex>,
}

impl<'a, I: InstructionInfo> CfgBuilder<'a, I> {
    fn new(instructions: &'a [I]) -> Self {
        Self {
            instructions,
            graph: DiGraph::new(),
            target_to_block: HashMap::new(),
            nodes: Vec::new(),
        }
    }

    fn build(mut self) -> Cfg<I> {
        let block_starts = self.find_block_boundaries();
        self.create_blocks(&block_starts);
        self.add_edges();
        self.identify_back_edges();

        Cfg::new(self.graph, self.target_to_block)
    }

    /// Find basic block boundaries.
    ///
    /// A new block starts at:
    /// - The beginning of the code
    /// - Any branch target
    /// - The instruction after a branch
    fn find_block_boundaries(&self) -> Vec<usize> {
        // Collect all branch targets first
        let branch_targets: HashSet<I::Target> = self
            .instructions
            .iter()
            .filter_map(|i| i.branch_target())
            .collect();

        let mut block_starts = Vec::new();
        let mut previous_was_branch = false;

        for (idx, item) in self.instructions.iter().enumerate() {
            // Check if this instruction is a branch target
            let is_branch_target = item
                .as_target()
                .is_some_and(|target| branch_targets.contains(&target));

            let is_start = idx == 0 || is_branch_target || previous_was_branch;

            if is_start && self.has_code_at(idx) {
                block_starts.push(idx);
            }

            previous_was_branch = item.is_branch() || item.is_return();
        }

        block_starts
    }

    /// Create graph nodes for each basic block.
    fn create_blocks(&mut self, block_starts: &[usize]) {
        for (block_idx, &start_idx) in block_starts.iter().enumerate() {
            let end_idx = block_starts
                .get(block_idx + 1)
                .copied()
                .unwrap_or(self.instructions.len());

            let instruction_range = start_idx..end_idx;

            // Get the target identifier from the first item in the block
            let label = self.instructions[start_idx].as_target();

            // Count instructions (items with mnemonic)
            let instruction_count = instruction_range
                .clone()
                .filter(|&idx| self.instructions[idx].mnemonic().is_some())
                .count();

            let node = self.graph.add_node(BlockData {
                label,
                instruction_range: instruction_range.clone(),
                back_edge_target: None,
                terminator_index: None,
                instruction_count,
            });
            self.nodes.push(node);

            // Register all labels/targets in this block
            for idx in instruction_range {
                if let Some(target) = self.instructions[idx].as_target() {
                    self.target_to_block.insert(target, node);
                }
            }
        }
    }

    /// Add edges based on control flow and record terminator indices.
    fn add_edges(&mut self) {
        for (block_idx, &node) in self.nodes.iter().enumerate() {
            let block = &self.graph[node];

            // Find the last instruction in the block
            let terminator = block
                .instruction_range
                .clone()
                .rev()
                .find(|&idx| self.instructions[idx].mnemonic().is_some());

            if let Some(terminator_idx) = terminator {
                let item = &self.instructions[terminator_idx];

                if item.is_branch() || item.is_return() {
                    self.graph[node].terminator_index = Some(terminator_idx);
                }

                // Add edge to branch target (if direct branch, not a call)
                if item.is_branch() && !item.is_call() {
                    if let Some(target) = item.branch_target() {
                        if let Some(&target_node) = self.target_to_block.get(&target) {
                            self.graph.add_edge(node, target_node, ());
                        }
                    }
                }

                // Add fall-through edge (if not return and not unconditional jump)
                if !item.is_return() && !item.is_unconditional_jump() {
                    if let Some(&next_node) = self.nodes.get(block_idx + 1) {
                        self.graph.add_edge(node, next_node, ());
                    }
                }
            } else if let Some(&next_node) = self.nodes.get(block_idx + 1) {
                // No terminator - fall through to next block
                self.graph.add_edge(node, next_node, ());
            }
        }
    }

    /// Compute dominators and mark back-edges.
    ///
    /// A back-edge is an edge A → B where B dominates A.
    fn identify_back_edges(&mut self) {
        if self.nodes.is_empty() {
            return;
        }

        let entry = self.nodes[0];
        let dominators = dominators::simple_fast(&self.graph, entry);

        let back_edges: Vec<_> = self
            .nodes
            .iter()
            .filter_map(|&node| {
                self.graph
                    .neighbors(node)
                    .find(|&successor| {
                        dominators
                            .dominators(node)
                            .is_some_and(|mut iter| iter.any(|d| d == successor))
                    })
                    .map(|target| (node, target))
            })
            .collect();

        for (node, _target_node) in back_edges {
            debug_assert!(
                self.graph[node].instruction_count > 0,
                "back-edge should have instructions"
            );
            // Get branch target directly from the terminator instruction
            if let Some(term_idx) = self.graph[node].terminator_index {
                if let Some(target) = self.instructions[term_idx].branch_target() {
                    self.graph[node].back_edge_target = Some(target);
                }
            }
        }
    }

    /// Check if there's any code at or after this position before the next label/target.
    fn has_code_at(&self, idx: usize) -> bool {
        if self.instructions[idx].mnemonic().is_some() {
            return true;
        }

        self.instructions
            .iter()
            .skip(idx + 1)
            .take_while(|item| item.as_target().is_none())
            .any(|item| item.mnemonic().is_some())
    }
}

// #[cfg(test)]
// mod tests {
//     use super::*;

//     /// Mock instruction for testing
//     #[derive(Clone)]
//     struct MockInstruction {
//         // position: usize,
//         mnemonic: Option<&'static str>,
//         target: Option<String>,
//         label: Option<String>,
//     }

//     impl InstructionInfo for MockInstruction {
//         // type Position = usize;
//         type Target = String;

//         // fn position(&self) -> usize {
//         //     self.position
//         // }

//         fn mnemonic(&self) -> Option<&str> {
//             self.mnemonic
//         }

//         fn branch_target(&self) -> Option<String> {
//             self.target.clone()
//         }

//         fn label(&self) -> Option<String> {
//             self.label.clone()
//         }

//         fn position_as_target(&self) -> Option<String> {
//             None // Text-like behavior
//         }
//     }

//     fn inst(_pos: usize, mnemonic: &'static str) -> MockInstruction {
//         MockInstruction {
//             // position: pos,
//             mnemonic: Some(mnemonic),
//             target: None,
//             label: None,
//         }
//     }

//     fn label_inst(_pos: usize, label: &str, mnemonic: &'static str) -> MockInstruction {
//         MockInstruction {
//             // position: pos,
//             mnemonic: Some(mnemonic),
//             target: None,
//             label: Some(label.to_string()),
//         }
//     }

//     fn branch_inst(_pos: usize, mnemonic: &'static str, target: &str) -> MockInstruction {
//         MockInstruction {
//             // position: pos,
//             mnemonic: Some(mnemonic),
//             target: Some(target.to_string()),
//             label: None,
//         }
//     }

//     #[test]
//     fn test_empty_input() {
//         let instructions: Vec<MockInstruction> = vec![];
//         let cfg = build_cfg(&instructions);
//         assert_eq!(cfg.block_count(), 0);
//     }

//     #[test]
//     fn test_single_instruction() {
//         let instructions = vec![inst(0, "ret")];
//         let cfg = build_cfg(&instructions);
//         assert_eq!(cfg.block_count(), 1);
//     }

//     #[test]
//     fn test_simple_loop() {
//         // _func:
//         //     mov x0, #0
//         // .Lloop:
//         //     add x0, x0, #1
//         //     b.lt .Lloop
//         //     ret
//         let instructions = vec![
//             label_inst(0, "_func", "mov"),
//             label_inst(1, ".Lloop", "add"),
//             branch_inst(2, "b.lt", ".Lloop"),
//             inst(3, "ret"),
//         ];

//         let cfg = build_cfg(&instructions);

//         // Should have multiple blocks
//         assert!(cfg.block_count() >= 2);

//         // Should detect back-edge to .Lloop
//         let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
//         assert_eq!(back_edge_count, 1, "Should have exactly one back-edge");

//         // The back-edge target should be .Lloop
//         let back_edge_block = cfg.blocks().find(|&b| cfg.has_back_edge(b)).unwrap();
//         assert_eq!(
//             cfg.back_edge_target(back_edge_block),
//             Some(&".Lloop".to_string())
//         );
//     }

//     #[test]
//     fn test_nested_loops() {
//         // .Louter:
//         //     mov x0, #0
//         // .Linner:
//         //     add x0, x0, #1
//         //     b.lt .Linner
//         //     b.lt .Louter
//         //     ret
//         let instructions = vec![
//             label_inst(0, ".Louter", "mov"),
//             label_inst(1, ".Linner", "add"),
//             branch_inst(2, "b.lt", ".Linner"),
//             branch_inst(3, "b.lt", ".Louter"),
//             inst(4, "ret"),
//         ];

//         let cfg = build_cfg(&instructions);

//         let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
//         assert_eq!(back_edge_count, 2, "Should have two back-edges");
//     }

//     #[test]
//     fn test_no_back_edge_for_forward_branch() {
//         // _func:
//         //     cmp x0, #0
//         //     b.eq .Lskip
//         //     mov x1, #1
//         // .Lskip:
//         //     ret
//         let instructions = vec![
//             label_inst(0, "_func", "cmp"),
//             branch_inst(1, "b.eq", ".Lskip"),
//             inst(2, "mov"),
//             label_inst(3, ".Lskip", "ret"),
//         ];

//         let cfg = build_cfg(&instructions);

//         let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
//         assert_eq!(
//             back_edge_count, 0,
//             "Forward branches should not be back-edges"
//         );
//     }

//     #[test]
//     fn test_call_not_branch_edge() {
//         // _func:
//         //     bl _helper
//         //     ret
//         // _helper:
//         //     ret
//         let instructions = vec![
//             label_inst(0, "_func", "mov"),
//             branch_inst(1, "bl", "_helper"),
//             inst(2, "ret"),
//             label_inst(3, "_helper", "ret"),
//         ];

//         let cfg = build_cfg(&instructions);

//         // BL should NOT create a CFG edge to _helper (calls are interprocedural)
//         // The _func block should only fall through, not branch to _helper
//         let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
//         assert_eq!(back_edge_count, 0, "Calls should not create back-edges");
//     }

//     #[test]
//     fn test_instruction_count() {
//         // _func:
//         //     mov x0, #0
//         //     add x0, x0, #1
//         //     ret
//         let instructions = vec![
//             label_inst(0, "_func", "mov"),
//             inst(1, "add"),
//             inst(2, "ret"),
//         ];

//         let cfg = build_cfg(&instructions);

//         let block = cfg.blocks().next().unwrap();
//         assert_eq!(cfg.instruction_count(block), 3);
//     }

//     #[test]
//     fn test_self_loop() {
//         // .Lspin:
//         //     b .Lspin
//         let instructions = vec![label_inst(0, ".Lspin", "b")];
//         // Need to set branch target
//         let mut instructions = instructions;
//         instructions[0].target = Some(".Lspin".to_string());

//         let cfg = build_cfg(&instructions);

//         let back_edge_count = cfg.blocks().filter(|&b| cfg.has_back_edge(b)).count();
//         assert_eq!(back_edge_count, 1, "Self-loop should have back-edge");
//     }
// }
