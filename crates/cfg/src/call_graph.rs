//! Call-graph construction and cycle detection
//!
//! Builds an inter-procedural call graph from the block-level CFG produced by
//! [`CfgBuilder`] and checks for recursive cycles.

use std::collections::{HashMap, HashSet, VecDeque};

use crate::{
    CfgInstruction,
    builder::CfgBuilder,
    block_graph::{BlockGraph, BlockIndex, InnerBlockGraph},
};

/// Build a block-level CFG with call-cycle detection from a sequence of instructions.
///
/// This is the full path used by the native verifier. Returns the block graph
/// together with the call-cycle result: `Some(entry)` if the call graph contains
/// a cycle, `None` if acyclic.
pub fn build_call_graph<I: CfgInstruction>(instructions: &[I]) -> (BlockGraph, Option<usize>) {
    let mut builder = CfgBuilder::new(instructions);
    builder.compute_block_graph();
    let cycle = CallGraphAnalyzer::new(&builder).detect_cycle();
    let graph = BlockGraph::new(builder.inner_block_graph, builder.target_to_block);
    (graph, cycle)
}

/// Analyzes the call graph derived from a built block-level CFG.
///
/// Constructed from a [`CfgBuilder`] that has already run
/// [`compute_block_graph`](CfgBuilder::compute_block_graph).
struct CallGraphAnalyzer<'a, I: CfgInstruction> {
    nodes: &'a [BlockIndex],
    graph: &'a InnerBlockGraph,
    target_to_block: &'a HashMap<usize, BlockIndex>,
    instructions: &'a [I],
}

impl<'a, I: CfgInstruction> CallGraphAnalyzer<'a, I> {
    /// Create an analyzer by borrowing the post-build state of a [`CfgBuilder`].
    fn new(builder: &'a CfgBuilder<'_, I>) -> Self {
        Self {
            nodes: &builder.nodes,
            graph: &builder.inner_block_graph,
            target_to_block: &builder.target_to_block,
            instructions: builder.instructions,
        }
    }

    /// Build a call graph, check for cycles, and return the result.
    ///
    /// Function entries are: target 0 (module entry) plus all `bl` targets recorded
    /// in the CFG. For each function, BFS through CFG successors assigns blocks to
    /// that function, stopping at blocks belonging to other functions. Tail calls
    /// (`b`/`b.cond` to another function's entry) are recorded as call edges.
    ///
    /// Returns `Some(entry)` if the call graph contains a cycle (where `entry` is
    /// the function entry target at the cycle point), or `None` if acyclic.
    fn detect_cycle(&self) -> Option<usize> {
        if self.nodes.is_empty() {
            return None;
        }

        // Collect function entries: module entry + all valid bl targets.
        // Every entry is guaranteed to be in target_to_block.
        let mut entries = HashSet::new();
        entries.insert(self.instructions[0].as_target());

        for &node in self.nodes {
            for &target in &self.graph[node].call_targets {
                if self.target_to_block.contains_key(&target) {
                    entries.insert(target);
                }
            }
        }

        // One graph node per function entry
        let mut call_graph = petgraph::graph::DiGraph::<usize, ()>::new();
        let entry_to_node: HashMap<usize, petgraph::graph::NodeIndex> = entries
            .iter()
            .map(|&entry| (entry, call_graph.add_node(entry)))
            .collect();

        // For each function entry, BFS through CFG successors.
        // Stop at blocks that start at another function's entry.
        // Record bl targets and tail-call edges as call graph edges.
        for &entry in &entries {
            let start_block = self.target_to_block[&entry];
            let caller = entry_to_node[&entry];

            let mut callees = HashSet::new();
            let mut visited = HashSet::new();
            let mut queue = VecDeque::new();

            visited.insert(start_block);
            queue.push_back(start_block);

            while let Some(block) = queue.pop_front() {
                // Collect bl targets from this block
                for &target in &self.graph[block].call_targets {
                    if entries.contains(&target) {
                        callees.insert(target);
                    }
                }

                // Traverse CFG successors, stopping at other function entries
                for successor in self.graph.neighbors(block) {
                    if visited.contains(&successor) {
                        continue;
                    }

                    let successor_start = self.graph[successor].instruction_range.start;
                    let successor_target = self.instructions[successor_start].as_target();

                    if successor_target != entry && entries.contains(&successor_target) {
                        // Successor is another function's entry — tail call
                        callees.insert(successor_target);
                    } else {
                        // Same function, continue BFS
                        visited.insert(successor);
                        queue.push_back(successor);
                    }
                }
            }

            for callee_target in callees {
                let callee = entry_to_node[&callee_target];
                call_graph.add_edge(caller, callee, ());
            }
        }

        // Check for cycles via toposort
        if let Err(cycle) = petgraph::algo::toposort(&call_graph, None) {
            Some(call_graph[cycle.node_id()])
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::traits::mock_instruction::MockInstruction;

    use super::*;

    #[test]
    fn test_no_calls_acyclic() {
        // Linear code, no bl at all → no cycle
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::new("sub", 1),
            MockInstruction::new("ret", 2),
        ];
        let (_cfg, cycle) = build_call_graph(&instructions);
        assert!(cycle.is_none());
    }

    #[test]
    fn test_empty_input() {
        let instructions: Vec<MockInstruction> = vec![];
        let (_cfg, cycle) = build_call_graph(&instructions);
        assert!(cycle.is_none());
    }

    #[test]
    fn test_acyclic_call() {
        // func_a [0]: bl func_b; ret
        // func_b [2]: add; ret
        let instructions = vec![
            MockInstruction::with_target("bl", 0, 2), // call func_b
            MockInstruction::new("ret", 1),
            MockInstruction::new("add", 2), // func_b entry
            MockInstruction::new("ret", 3),
        ];
        let (_cfg, cycle) = build_call_graph(&instructions);
        assert!(cycle.is_none());
    }

    #[test]
    fn test_acyclic_call_chain() {
        // A → B → C, no cycle
        // func_a [0]: bl func_b; ret
        // func_b [2]: bl func_c; ret
        // func_c [4]: add; ret
        let instructions = vec![
            MockInstruction::with_target("bl", 0, 2), // A calls B
            MockInstruction::new("ret", 1),
            MockInstruction::with_target("bl", 2, 4), // B calls C
            MockInstruction::new("ret", 3),
            MockInstruction::new("add", 4), // C
            MockInstruction::new("ret", 5),
        ];
        let (_cfg, cycle) = build_call_graph(&instructions);
        assert!(cycle.is_none());
    }

    #[test]
    fn test_mutual_recursion_via_bl() {
        // A calls B, B calls A → cycle
        // func_a [0]: bl func_b; ret
        // func_b [2]: bl func_a; ret
        let instructions = vec![
            MockInstruction::with_target("bl", 0, 2), // A calls B
            MockInstruction::new("ret", 1),
            MockInstruction::with_target("bl", 2, 0), // B calls A
            MockInstruction::new("ret", 3),
        ];
        let (_cfg, cycle) = build_call_graph(&instructions);
        assert!(cycle.is_some(), "should detect mutual recursion via bl");
    }

    #[test]
    fn test_self_recursive_bl() {
        // A calls itself via bl → cycle
        // func_a [0]: add; bl func_a; ret
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::with_target("bl", 1, 0), // self-call
            MockInstruction::new("ret", 2),
        ];
        let (_cfg, cycle) = build_call_graph(&instructions);
        assert!(cycle.is_some(), "should detect self-recursive bl");
    }

    #[test]
    fn test_tail_call_cycle() {
        // A calls B via bl, B tail-calls A via unconditional b → cycle
        // func_a [0]: bl func_b; ret
        // func_b [2]: b func_a  (tail call — jumps to another function entry)
        let instructions = vec![
            MockInstruction::with_target("bl", 0, 2), // A calls B
            MockInstruction::new("ret", 1),
            MockInstruction::with_target("b", 2, 0), // B tail-calls A
        ];
        let (_cfg, cycle) = build_call_graph(&instructions);
        assert!(cycle.is_some(), "should detect cycle via tail call");
    }

    #[test]
    fn test_conditional_tail_call_cycle() {
        // A calls B via bl, B conditionally tail-calls A via b.lt → cycle
        // func_a [0]: bl func_b; ret
        // func_b [2]: cmp; b.lt func_a; ret
        let instructions = vec![
            MockInstruction::with_target("bl", 0, 2), // A calls B
            MockInstruction::new("ret", 1),
            MockInstruction::new("cmp", 2),             // B entry
            MockInstruction::with_target("b.lt", 3, 0), // conditional tail-call to A
            MockInstruction::new("ret", 4),
        ];
        let (_cfg, cycle) = build_call_graph(&instructions);
        assert!(
            cycle.is_some(),
            "should detect cycle via conditional tail call"
        );
    }

    #[test]
    fn test_diamond_call_graph_acyclic() {
        // A → B, A → C, B → D, C → D — acyclic diamond
        // func_a [0]:  bl B; bl C; ret
        // func_b [3]:  bl D; ret
        // func_c [5]:  bl D; ret
        // func_d [7]:  add; ret
        let instructions = vec![
            MockInstruction::with_target("bl", 0, 3), // A calls B
            MockInstruction::with_target("bl", 1, 5), // A calls C
            MockInstruction::new("ret", 2),
            MockInstruction::with_target("bl", 3, 7), // B calls D
            MockInstruction::new("ret", 4),
            MockInstruction::with_target("bl", 5, 7), // C calls D
            MockInstruction::new("ret", 6),
            MockInstruction::new("add", 7), // D
            MockInstruction::new("ret", 8),
        ];
        let (_cfg, cycle) = build_call_graph(&instructions);
        assert!(cycle.is_none(), "diamond call graph should be acyclic");
    }

    #[test]
    fn test_three_way_cycle() {
        // A → B → C → A
        let instructions = vec![
            MockInstruction::with_target("bl", 0, 2), // A calls B
            MockInstruction::new("ret", 1),
            MockInstruction::with_target("bl", 2, 4), // B calls C
            MockInstruction::new("ret", 3),
            MockInstruction::with_target("bl", 4, 0), // C calls A
            MockInstruction::new("ret", 5),
        ];
        let (_cfg, cycle) = build_call_graph(&instructions);
        assert!(cycle.is_some(), "should detect A → B → C → A cycle");
    }

    #[test]
    fn test_bl_to_out_of_range_target_ignored() {
        // bl targets an address not in the instruction stream — should be
        // silently ignored (no panic, no false cycle).
        let instructions = vec![
            MockInstruction::with_target("bl", 0, 999), // target doesn't exist
            MockInstruction::new("ret", 1),
        ];
        let (_cfg, cycle) = build_call_graph(&instructions);
        assert!(
            cycle.is_none(),
            "bl to out-of-range target should be ignored, not cause a cycle"
        );
    }

    #[test]
    fn test_internal_loop_does_not_confuse_call_graph() {
        // Function A has an internal back-edge loop and calls B.
        // The loop should not create a spurious call-graph cycle.
        // func_a [0]: add; b.lt 0 (loop); bl func_b; ret
        // func_b [4]: sub; ret
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::with_target("b.lt", 1, 0), // internal back-edge
            MockInstruction::with_target("bl", 2, 4),   // call func_b
            MockInstruction::new("ret", 3),
            MockInstruction::new("sub", 4), // func_b entry
            MockInstruction::new("ret", 5),
        ];
        let (_cfg, cycle) = build_call_graph(&instructions);
        assert!(
            cycle.is_none(),
            "internal loop should not create a call-graph cycle"
        );
    }
}
