//! Generic CFG builder
//!
//! Builds a control flow graph from a sequence of instructions implementing
//! the [`CfgInstruction`] trait.

use std::collections::{HashMap, HashSet};

use crate::{
    CfgInstruction,
    graph::{BlockData, BlockIndex, Cfg, Graph},
};

/// Build a CFG from a sequence of instructions.
///
/// The instructions must implement [`CfgInstruction`] to provide the
/// control flow information needed for CFG construction.
pub fn build_cfg<I: CfgInstruction>(instructions: &[I]) -> Cfg {
    CfgBuilder::new(instructions).build()
}

/// Builder for constructing a CFG from instructions
struct CfgBuilder<'a, I: CfgInstruction> {
    instructions: &'a [I],
    graph: Graph,
    target_to_block: HashMap<usize, BlockIndex>,
    nodes: Vec<BlockIndex>,
}

impl<'a, I: CfgInstruction> CfgBuilder<'a, I> {
    /// Create a new CFG builder.
    fn new(instructions: &'a [I]) -> Self {
        Self {
            instructions,
            graph: Graph::default(),
            target_to_block: HashMap::new(),
            nodes: Vec::new(),
        }
    }

    /// Build the CFG.
    fn build(mut self) -> Cfg {
        let block_starts = self.find_block_boundaries();
        self.create_blocks(&block_starts);
        self.add_edges();
        self.identify_back_edges();

        Cfg::new(self.graph)
    }

    /// Find basic block boundaries.
    ///
    /// A new block starts at:
    /// - The beginning of the code
    /// - Any branch target
    /// - The instruction after a branch or return
    fn find_block_boundaries(&self) -> Vec<usize> {
        // Collect all branch targets first
        let branch_targets: HashSet<usize> = self
            .instructions
            .iter()
            .filter_map(|i| i.branch_target())
            .collect();

        let mut block_starts = Vec::new();
        let mut previous_was_branch = false;

        for (idx, item) in self.instructions.iter().enumerate() {
            // Check if this instruction is a branch target
            let is_branch_target = branch_targets.contains(&item.as_target());

            let is_start = idx == 0 || is_branch_target || previous_was_branch;

            if is_start {
                block_starts.push(idx);
            }

            previous_was_branch = item.is_branch();
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

            // All items are instructions, count = range length
            let instruction_count = instruction_range.len();

            let node = self.graph.add_node(BlockData {
                instruction_range: instruction_range.clone(),
                back_edge_target: None,         // to be filled later
                has_explicit_terminator: false, // to be filled later
                instruction_count,
                call_targets: Vec::new(),       // to be filled later
            });
            self.nodes.push(node);

            // Register all targets in this block
            for idx in instruction_range {
                let target = self.instructions[idx].as_target();
                self.target_to_block.insert(target, node);
            }
        }
    }

    /// Add edges based on control flow and record terminator indices.
    fn add_edges(&mut self) {
        for (block_idx, &node) in self.nodes.iter().enumerate() {
            let block = &self.graph[node];

            // The terminator is the last instruction in the block
            // (all items are instructions, so last in range)
            if let Some(terminator_idx) = block.instruction_range.clone().last() {
                let item = &self.instructions[terminator_idx];

                if item.is_branch() {
                    self.graph[node].has_explicit_terminator = true;
                }

                // Add edge to branch target if one exists.
                // Non-branches and indirect branches have no target (branch_target() = None).
                if item.is_call() {
                    // Calls return to next instruction, not jump to target.
                    if let Some(target) = item.branch_target() {
                        self.graph[node].call_targets.push(target);
                    }
                } else if let Some(target) = item.branch_target() {
                    // Target may not exist if it's outside the function's instruction
                    // range (adversarial code) - the verifier will reject these later.
                    if let Some(&target_node) = self.target_to_block.get(&target) {
                        self.graph.add_edge(node, target_node, ());
                    }
                }

                // Add fall-through edge (if not return and not unconditional jump)
                if !item.is_branch() || item.is_conditional() || item.is_call() {
                    if let Some(&next_node) = self.nodes.get(block_idx + 1) {
                        self.graph.add_edge(node, next_node, ());
                    }
                }
            } else if let Some(&next_node) = self.nodes.get(block_idx + 1) {
                // Empty block - fall through to next block
                self.graph.add_edge(node, next_node, ());
            }
        }
    }

    /// Compute dominators and mark back-edges.
    /// A back-edge is an edge A → B where B dominates A.
    fn identify_back_edges(&mut self) {
        if self.nodes.is_empty() {
            return;
        }

        let entry = self.nodes[0];
        let dominators = petgraph::algo::dominators::simple_fast(&self.graph, entry);

        // Find nodes that are SOURCES of back-edges (nodes with a successor that dominates them)
        let back_edge_sources: Vec<_> = self
            .nodes
            .iter()
            .copied()
            .filter(|&node| {
                self.graph.neighbors(node).any(|successor| {
                    dominators
                        .dominators(node)
                        .is_some_and(|mut iter| iter.any(|d| d == successor))
                })
            })
            .collect();

        for node in back_edge_sources {
            assert!(
                self.graph[node].instruction_count > 0,
                "back-edge source block has no instructions"
            );
            // Get branch target directly from the terminator instruction.
            // Back-edge sources must have an explicit terminator (the branch that creates the back-edge).
            let block = &self.graph[node];
            if block.has_explicit_terminator {
                let terminator_idx = block.instruction_range.end - 1;
                // Indirect branches have no static target. This can happen if the back-edge is via
                // fall-through from an indirect branch. The verifier will reject indirect branches.
                if let Some(target) = self.instructions[terminator_idx].branch_target() {
                    self.graph[node].back_edge_target = Some(target);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::traits::mock_instruction::MockInstruction;

    #[test]
    fn test_empty_input() {
        let instructions: Vec<MockInstruction> = vec![];
        let cfg = crate::build_cfg(&instructions);

        assert_eq!(cfg.block_count(), 0);
        assert_eq!(cfg.back_edge_count(), 0);
    }

    #[test]
    fn test_single_instruction() {
        let instructions = vec![MockInstruction::new("add", 0)];
        let cfg = crate::build_cfg(&instructions);

        assert_eq!(cfg.block_count(), 1);
        assert_eq!(cfg.back_edge_count(), 0);

        // Check block range
        let block = cfg.blocks().next().unwrap();
        assert_eq!(cfg.instruction_count(block), 1);
    }

    #[test]
    fn test_branch_creates_boundary() {
        // Instructions: add, b (to somewhere), sub
        // The sub should start a new block
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::with_target("b", 1, 100), // branch to external target
            MockInstruction::new("sub", 2),
        ];
        let cfg = crate::build_cfg(&instructions);

        // Should have 2 blocks: [add, b] and [sub]
        assert_eq!(cfg.block_count(), 2);
    }

    #[test]
    fn test_return_creates_boundary() {
        // Instructions: add, ret, sub
        // The sub should start a new block
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::new("ret", 1),
            MockInstruction::new("sub", 2),
        ];
        let cfg = crate::build_cfg(&instructions);

        // Should have 2 blocks: [add, ret] and [sub]
        assert_eq!(cfg.block_count(), 2);
    }

    #[test]
    fn test_branch_target_creates_boundary() {
        // Instructions: add, b.lt (to index 3), mul, sub
        // Branch target at index 3 (sub) creates a new block
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::with_target("b.lt", 1, 3),
            MockInstruction::new("mul", 2),
            MockInstruction::new("sub", 3), // branch target
        ];
        let cfg = crate::build_cfg(&instructions);

        // Should have 3 blocks: [add, b.lt], [mul], [sub]
        assert_eq!(cfg.block_count(), 3);
    }

    #[test]
    fn test_block_ranges() {
        // Linear code: 4 instructions, no branches
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::new("sub", 1),
            MockInstruction::new("mul", 2),
            MockInstruction::new("mov", 3),
        ];
        let cfg = crate::build_cfg(&instructions);

        // Single block with all 4 instructions
        assert_eq!(cfg.block_count(), 1);
        let block = cfg.blocks().next().unwrap();
        assert_eq!(cfg.instruction_count(block), 4);
    }

    #[test]
    fn test_conditional_has_fall_through() {
        // Instructions: add, b.lt (forward), sub, ret
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::with_target("b.lt", 1, 3), // conditional branch to ret
            MockInstruction::new("sub", 2),
            MockInstruction::new("ret", 3),
        ];
        let cfg = crate::build_cfg(&instructions);

        // Should have 3 blocks
        assert_eq!(cfg.block_count(), 3);

        // Block 0 should have terminator at index 1 (b.lt)
        let blocks: Vec<_> = cfg.blocks().collect();
        assert_eq!(cfg.terminator_index(blocks[0]), Some(1));
    }

    #[test]
    fn test_return_no_fall_through() {
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::new("ret", 1),
            MockInstruction::new("sub", 2), // unreachable
        ];
        let cfg = crate::build_cfg(&instructions);

        // 2 blocks: [add, ret], [sub]
        assert_eq!(cfg.block_count(), 2);

        // First block ends with ret, no fall-through edge
        // (The sub block is separate but unreachable)
    }

    #[test]
    fn test_unconditional_no_fall_through() {
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::with_target("b", 1, 100), // unconditional branch away
            MockInstruction::new("sub", 2),            // unreachable via fall-through
        ];
        let cfg = crate::build_cfg(&instructions);

        // 2 blocks
        assert_eq!(cfg.block_count(), 2);
    }

    #[test]
    fn test_simple_loop_back_edge() {
        // Simple loop:
        //   0: add
        //   1: cmp
        //   2: b.lt -> 0  (back-edge)
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::new("cmp", 1),
            MockInstruction::with_target("b.lt", 2, 0), // back-edge to start
        ];
        let cfg = crate::build_cfg(&instructions);

        // Single block with a back-edge to itself
        assert_eq!(cfg.block_count(), 1);
        assert_eq!(cfg.back_edge_count(), 1);

        let block = cfg.blocks().next().unwrap();
        assert!(cfg.has_back_edge(block));
        assert_eq!(cfg.back_edge_target(block), Some(&0));
    }

    #[test]
    fn test_self_loop() {
        // Single instruction loop: b -> 0
        let instructions = vec![MockInstruction::with_target("b", 0, 0)];
        let cfg = crate::build_cfg(&instructions);

        assert_eq!(cfg.block_count(), 1);
        assert_eq!(cfg.back_edge_count(), 1);

        let block = cfg.blocks().next().unwrap();
        assert_eq!(cfg.back_edge_target(block), Some(&0));
    }

    #[test]
    fn test_nested_loops() {
        // Outer loop with inner loop:
        //   0: mov      <- outer loop start
        //   1: add      <- inner loop start
        //   2: b.lt -> 1  (inner back-edge)
        //   3: cmp
        //   4: b.ne -> 0  (outer back-edge)
        let instructions = vec![
            MockInstruction::new("mov", 0),
            MockInstruction::new("add", 1),
            MockInstruction::with_target("b.lt", 2, 1), // inner loop back
            MockInstruction::new("cmp", 3),
            MockInstruction::with_target("b.ne", 4, 0), // outer loop back
        ];
        let cfg = crate::build_cfg(&instructions);

        // Blocks: [mov], [add, b.lt], [cmp, b.ne]
        // Block at index 1 is a branch target, block at index 3 is after a branch
        assert_eq!(cfg.block_count(), 3);
        assert_eq!(cfg.back_edge_count(), 2);
    }

    #[test]
    fn test_forward_only_no_back_edge() {
        // Only forward branches:
        //   0: cmp
        //   1: b.eq -> 3
        //   2: add
        //   3: ret
        let instructions = vec![
            MockInstruction::new("cmp", 0),
            MockInstruction::with_target("b.eq", 1, 3),
            MockInstruction::new("add", 2),
            MockInstruction::new("ret", 3),
        ];
        let cfg = crate::build_cfg(&instructions);

        // 3 blocks: [cmp, b.eq], [add], [ret]
        assert_eq!(cfg.block_count(), 3);
        assert_eq!(cfg.back_edge_count(), 0);
    }

    #[test]
    fn test_linear_code() {
        // No branches at all
        let instructions = vec![
            MockInstruction::new("mov", 0),
            MockInstruction::new("add", 1),
            MockInstruction::new("sub", 2),
            MockInstruction::new("mul", 3),
        ];
        let cfg = crate::build_cfg(&instructions);

        assert_eq!(cfg.block_count(), 1);
        assert_eq!(cfg.back_edge_count(), 0);
        assert_eq!(cfg.instruction_count(cfg.blocks().next().unwrap()), 4);
    }

    #[test]
    fn test_while_loop_pattern() {
        // Classic while loop:
        //   0: cmp      <- loop header (condition check)
        //   1: b.ge -> 4  (exit if condition false)
        //   2: add      <- loop body
        //   3: b -> 0     (back-edge)
        //   4: ret      <- after loop
        let instructions = vec![
            MockInstruction::new("cmp", 0),
            MockInstruction::with_target("b.ge", 1, 4), // exit condition
            MockInstruction::new("add", 2),
            MockInstruction::with_target("b", 3, 0), // back-edge
            MockInstruction::new("ret", 4),
        ];
        let cfg = crate::build_cfg(&instructions);

        // Blocks: [cmp, b.ge], [add, b], [ret]
        assert_eq!(cfg.block_count(), 3);
        assert_eq!(cfg.back_edge_count(), 1);

        // The block containing the back-edge should be identified
        let blocks: Vec<_> = cfg.blocks().collect();
        let back_edge_block = blocks.iter().find(|&&b| cfg.has_back_edge(b)).unwrap();
        assert_eq!(cfg.back_edge_target(*back_edge_block), Some(&0));
    }

    #[test]
    fn test_call_not_back_edge() {
        // Call instruction should not create a back-edge even if target < current
        //   0: mov
        //   1: bl -> 0  (call, not a back-edge for CFG)
        //   2: ret
        let instructions = vec![
            MockInstruction::new("mov", 0),
            MockInstruction::with_target("bl", 1, 0), // call to earlier address
            MockInstruction::new("ret", 2),
        ];
        let cfg = crate::build_cfg(&instructions);

        // bl is a call, so it doesn't create an edge in the CFG (calls return)
        // 2 blocks: [mov, bl], [ret]
        // The call has fall-through because it's not an unconditional jump
        assert_eq!(cfg.block_count(), 2);
        assert_eq!(cfg.back_edge_count(), 0);
    }

    #[test]
    fn test_bl_populates_call_targets() {
        // bl stores its target in call_targets, not as a CFG edge
        //   0: mov
        //   1: bl -> 0
        //   2: ret
        let instructions = vec![
            MockInstruction::new("mov", 0),
            MockInstruction::with_target("bl", 1, 0),
            MockInstruction::new("ret", 2),
        ];
        let cfg = crate::build_cfg(&instructions);

        // Block 0: [mov, bl] — should have call_targets = [0]
        let block0 = cfg.blocks().next().unwrap();
        assert_eq!(cfg.call_targets(block0), &[0]);
    }

    #[test]
    fn test_non_call_branches_have_no_call_targets() {
        // b and b.cond should NOT populate call_targets
        let instructions = vec![
            MockInstruction::with_target("b.lt", 0, 2),
            MockInstruction::new("add", 1),
            MockInstruction::with_target("b", 2, 0), // back-edge
        ];
        let cfg = crate::build_cfg(&instructions);

        for block in cfg.blocks() {
            assert!(
                cfg.call_targets(block).is_empty(),
                "block starting at {:?} should have no call targets",
                cfg.instruction_range(block)
            );
        }
    }

    #[test]
    fn test_multiple_bl_in_block() {
        // Two consecutive bl instructions in one block (bl has fall-through,
        // so both stay in the same block unless the target creates a split).
        //   0: bl -> 100
        //   1: bl -> 200
        //   2: ret
        let instructions = vec![
            MockInstruction::with_target("bl", 0, 100),
            MockInstruction::with_target("bl", 1, 200),
            MockInstruction::new("ret", 2),
        ];
        let cfg = crate::build_cfg(&instructions);

        // Blocks: [bl, bl], [ret]
        // Only the last instruction in a block is the terminator checked
        // for call_targets, but both bl's create block boundaries.
        // Actually: bl at 0 is a branch → next instruction (1) starts a new block.
        // So blocks are: [bl->100], [bl->200], [ret]
        // Each single-bl block has one call target.
        let blocks: Vec<_> = cfg.blocks().collect();
        assert_eq!(blocks.len(), 3);
        assert_eq!(cfg.call_targets(blocks[0]), &[100]);
        assert_eq!(cfg.call_targets(blocks[1]), &[200]);
        assert!(cfg.call_targets(blocks[2]).is_empty());
    }

    #[test]
    fn test_multiple_branch_targets_same_block() {
        // Multiple branches to same target:
        //   0: b.eq -> 3
        //   1: b.lt -> 3
        //   2: add
        //   3: ret
        let instructions = vec![
            MockInstruction::with_target("b.eq", 0, 3),
            MockInstruction::with_target("b.lt", 1, 3),
            MockInstruction::new("add", 2),
            MockInstruction::new("ret", 3),
        ];
        let cfg = crate::build_cfg(&instructions);

        // Blocks: [b.eq], [b.lt], [add], [ret]
        // Each conditional branch ends its block, and ret is a target
        assert_eq!(cfg.block_count(), 4);
        assert_eq!(cfg.back_edge_count(), 0);
    }
}
