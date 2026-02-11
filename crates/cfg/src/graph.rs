//! CFG data structures

use std::{collections::HashSet, ops::Range};

pub type BlockIndex = petgraph::graph::NodeIndex;

pub(crate) type Graph = petgraph::graph::DiGraph<BlockData, ()>;

/// Data stored in each basic block node
#[derive(Debug)]
pub struct BlockData {
    /// Range of indices into the original instruction list.
    /// E.g., for a block containing instructions 3, 4, 5 this would be `3..6`
    pub instruction_range: Range<usize>,

    /// Branch target of the back-edge, if this block ends with one.
    pub back_edge_target: Option<usize>,

    /// Whether this block ends with an explicit terminator instruction.
    ///
    /// A **terminator** is the instruction that ends a basic block's control flow -
    /// either a branch instruction (conditional or unconditional) or a return.
    /// Blocks without an explicit terminator "fall through" to the next block.
    pub has_explicit_terminator: bool,

    /// Number of actual instructions in this block
    pub instruction_count: usize,

    /// Targets of call instructions (`bl`) in this block.
    /// Values are instruction indices (text) or byte offsets (binary),
    /// matching the `CfgInstruction::branch_target()` convention.
    pub call_targets: Vec<usize>,
}

/// Control flow graph backed by petgraph
pub struct Cfg {
    /// The underlying directed graph
    graph: Graph,
}

impl Cfg {
    /// Create a new CFG from graph (used by builder)
    pub(crate) fn new(graph: Graph) -> Self {
        Self { graph }
    }

    /// Iterate over all block indices
    pub fn blocks(&self) -> impl Iterator<Item = BlockIndex> {
        self.graph.node_indices()
    }

    /// Get the number of blocks
    #[cfg(test)]
    pub fn block_count(&self) -> usize {
        self.graph.node_count()
    }

    /// Get the number of blocks with back-edges
    #[cfg(test)]
    pub fn back_edge_count(&self) -> usize {
        self.blocks().filter(|&b| self.has_back_edge(b)).count()
    }

    /// Check if a block has a back-edge
    pub fn has_back_edge(&self, block: BlockIndex) -> bool {
        self.graph[block].back_edge_target.is_some()
    }

    /// Get the target of the back-edge (if any)
    pub fn back_edge_target(&self, block: BlockIndex) -> Option<&usize> {
        self.graph[block].back_edge_target.as_ref()
    }

    /// Get the index of the block's terminator instruction.
    ///
    /// Returns `Some(index)` if the block has an explicit terminator (branch or return),
    /// where index is derived from `instruction_range.end - 1`.
    /// Returns `None` if the block falls through without an explicit terminator.
    pub fn terminator_index(&self, block: BlockIndex) -> Option<usize> {
        let data = &self.graph[block];
        if data.has_explicit_terminator {
            // The terminator is always the last instruction in the block
            Some(data.instruction_range.end - 1)
        } else {
            None
        }
    }

    /// Get the number of actual instructions in a block
    pub fn instruction_count(&self, block: BlockIndex) -> usize {
        self.graph[block].instruction_count
    }

    /// Get the instruction range for a block
    pub fn instruction_range(&self, block: BlockIndex) -> &Range<usize> {
        &self.graph[block].instruction_range
    }

    /// Iterate over CFG successors of a block
    pub fn successors(&self, block: BlockIndex) -> impl Iterator<Item = BlockIndex> + '_ {
        self.graph.neighbors(block)
    }

    /// Get the call targets from a block (targets of `bl` instructions)
    pub fn call_targets(&self, block: BlockIndex) -> &[usize] {
        &self.graph[block].call_targets
    }

    /// Find all blocks not reachable from the given roots.
    ///
    /// `roots` contains instruction indices that identify BFS starting points.
    /// Any block whose start index matches a root becomes a BFS origin.
    pub fn find_unreachable_blocks(&self, roots: &[usize]) -> Vec<BlockIndex> {
        let reachable = self.compute_reachable(roots);
        self.graph
            .node_indices()
            .filter(|node| !reachable.contains(node))
            .collect()
    }

    /// Computes all blocks reachable from the given roots via BFS.
    fn compute_reachable(&self, roots: &[usize]) -> HashSet<BlockIndex> {
        let mut reachable = HashSet::new();

        if self.graph.node_count() == 0 {
            return reachable;
        }

        let root_set: HashSet<usize> = roots.iter().copied().collect();
        for node in self.graph.node_indices() {
            let start = self.graph[node].instruction_range.start;
            if root_set.contains(&start) && !reachable.contains(&node) {
                let mut bfs = petgraph::visit::Bfs::new(&self.graph, node);
                while let Some(n) = bfs.next(&self.graph) {
                    reachable.insert(n);
                }
            }
        }

        reachable
    }
}

#[cfg(test)]
mod tests {
    use crate::{build_cfg, traits::mock_instruction::MockInstruction};

    #[test]
    fn test_empty_cfg_has_no_unreachable() {
        let instructions: Vec<MockInstruction> = vec![];
        let cfg = build_cfg(&instructions);

        assert!(cfg.find_unreachable_blocks(&[0]).is_empty());
    }

    #[test]
    fn test_single_block_all_reachable() {
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::new("sub", 1),
            MockInstruction::new("ret", 2),
        ];
        let cfg = build_cfg(&instructions);

        assert_eq!(cfg.block_count(), 1);
        assert!(cfg.find_unreachable_blocks(&[0]).is_empty());
    }

    #[test]
    fn test_linear_code_all_reachable() {
        // Multiple blocks connected via fall-through
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::with_target("b.lt", 1, 3), // conditional branch forward
            MockInstruction::new("mul", 2),
            MockInstruction::new("ret", 3),
        ];
        let cfg = build_cfg(&instructions);

        // Blocks: [add, b.lt], [mul], [ret]
        assert_eq!(cfg.block_count(), 3);
        assert!(cfg.find_unreachable_blocks(&[0]).is_empty());
    }

    #[test]
    fn test_unreachable_after_unconditional_branch() {
        // Code after unconditional branch is unreachable
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::with_target("b", 1, 100), // unconditional branch away
            MockInstruction::new("sub", 2),            // unreachable
            MockInstruction::new("mul", 3),
        ];
        let cfg = build_cfg(&instructions);

        // Blocks: [add, b], [sub, mul]
        // Second block is unreachable (no edge from first block)
        assert_eq!(cfg.block_count(), 2);

        let unreachable = cfg.find_unreachable_blocks(&[0]);
        assert_eq!(unreachable.len(), 1);

        // Verify the unreachable block is the one starting at index 2
        let unreachable_block = unreachable[0];
        assert_eq!(cfg.instruction_range(unreachable_block).start, 2);
    }

    #[test]
    fn test_unreachable_after_return() {
        // Code after return is unreachable
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::new("ret", 1),
            MockInstruction::new("sub", 2), // unreachable
            MockInstruction::new("mul", 3),
        ];
        let cfg = build_cfg(&instructions);

        // Blocks: [add, ret], [sub, mul]
        assert_eq!(cfg.block_count(), 2);

        let unreachable = cfg.find_unreachable_blocks(&[0]);
        assert_eq!(unreachable.len(), 1);

        let unreachable_block = unreachable[0];
        assert_eq!(cfg.instruction_range(unreachable_block).start, 2);
    }

    #[test]
    fn test_extra_root_rescues_unreachable_block() {
        // Two "functions": func1 returns, func2 starts after it.
        // Without extra roots, func2 is unreachable.
        // With extra root at index 2, func2 becomes reachable.
        //
        // func1: [add, ret]  (indices 0,1)
        // func2: [sub, ret]  (indices 2,3)
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::new("ret", 1),
            MockInstruction::new("sub", 2), // func2 entry
            MockInstruction::new("ret", 3),
        ];
        let cfg = build_cfg(&instructions);

        // Without extra roots: func2 is unreachable
        let unreachable = cfg.find_unreachable_blocks(&[0]);
        assert_eq!(unreachable.len(), 1);
        assert_eq!(cfg.instruction_range(unreachable[0]).start, 2);

        // With roots at 0 (entry) and 2 (func2): all reachable
        let unreachable = cfg.find_unreachable_blocks(&[0, 2]);
        assert!(
            unreachable.is_empty(),
            "func2 should be reachable via extra root"
        );
    }

    #[test]
    fn test_extra_root_transitive_reachability() {
        // func1: [add, ret]
        // func2: [b.lt -> func3, sub]  (conditional branch to func3)
        // func3: [mul, ret]
        //
        // Extra root at func2 should make both func2 AND func3 reachable.
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::new("ret", 1),
            MockInstruction::with_target("b.lt", 2, 4), // func2: branch to func3
            MockInstruction::new("sub", 3),
            MockInstruction::new("mul", 4), // func3 entry
            MockInstruction::new("ret", 5),
        ];
        let cfg = build_cfg(&instructions);

        // Without roots: func2 and func3 are unreachable
        let unreachable = cfg.find_unreachable_blocks(&[0]);
        assert!(
            unreachable.len() >= 2,
            "func2 and func3 should be unreachable"
        );

        // With roots at 0 and func2: func3 should also become reachable transitively
        let unreachable = cfg.find_unreachable_blocks(&[0, 2]);
        assert!(
            unreachable.is_empty(),
            "func3 should be transitively reachable via func2: unreachable = {:?}",
            unreachable
                .iter()
                .map(|b| cfg.instruction_range(*b).clone())
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn test_extra_root_partial_rescue() {
        // Three functions after entry. Only func2 gets an extra root.
        // func3 remains unreachable.
        //
        // func1: [add, ret]    (indices 0,1)
        // func2: [sub, ret]    (indices 2,3)
        // func3: [mul, ret]    (indices 4,5)
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::new("ret", 1),
            MockInstruction::new("sub", 2), // func2
            MockInstruction::new("ret", 3),
            MockInstruction::new("mul", 4), // func3
            MockInstruction::new("ret", 5),
        ];
        let cfg = build_cfg(&instructions);

        // Roots at 0 (entry) and func2; func3 should still be unreachable
        let unreachable = cfg.find_unreachable_blocks(&[0, 2]);
        assert_eq!(unreachable.len(), 1);
        assert_eq!(cfg.instruction_range(unreachable[0]).start, 4);
    }

    #[test]
    fn test_diamond_both_arms_reachable() {
        // if-else diamond: conditional branch to "else", fall-through to "then",
        // both merge at the end.
        //
        // [cmp, b.eq -> 3]  block0
        // [add]             block1 (then)
        // [b -> 4]          block1 continues... actually let me restructure
        //
        // block0: [cmp, b.eq -> idx 3]  (conditional: fall-through to 2, branch to 3)
        // block1: [add, b -> idx 4]     (then-arm, unconditional jump to merge)
        // block2: [sub]                 (else-arm, fall-through to merge)
        // block3: [ret]                 (merge point)
        let instructions = vec![
            MockInstruction::with_target("b.eq", 0, 3), // if eq, goto else
            MockInstruction::new("add", 1),             // then
            MockInstruction::with_target("b", 2, 4),    // jump to merge
            MockInstruction::new("sub", 3),             // else
            MockInstruction::new("ret", 4),             // merge
        ];
        let cfg = build_cfg(&instructions);

        assert!(
            cfg.find_unreachable_blocks(&[0]).is_empty(),
            "all arms of diamond should be reachable"
        );
    }

    #[test]
    fn test_loop_exit_reachable() {
        // Loop with conditional back-edge and fall-through exit
        //
        // block0: [add, b.lt -> idx 0]  (loop body with back-edge)
        // block1: [ret]                 (exit, reachable via fall-through)
        let instructions = vec![
            MockInstruction::new("add", 0),
            MockInstruction::with_target("b.lt", 1, 0), // back-edge
            MockInstruction::new("ret", 2),             // loop exit
        ];
        let cfg = build_cfg(&instructions);

        assert!(
            cfg.find_unreachable_blocks(&[0]).is_empty(),
            "loop exit should be reachable via conditional fall-through"
        );
    }
}
