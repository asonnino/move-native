//! Static stack depth verification
//!
//! Verifies that the total stack usage cannot exceed a budget, and that
//! the call graph contains no cycles (which would imply unbounded depth).
//!
//! # Why static verification?
//!
//! Move has no recursion (call graph is a DAG) and no dynamic dispatch
//! (all `bl` targets are PC-relative). This makes static stack bounding
//! feasible with zero runtime overhead.
//!
//! Without this check, a deep call chain could overflow the stack, hitting
//! the guard page. The SIGSEGV handler would run on the same overflowed
//! stack, double-fault, and kill the validator process (denial-of-service).
//!
//! # Algorithm
//!
//! 1. Sum all SP decrements across the entire module (conservative upper bound)
//! 2. Reject if the sum exceeds the budget
//! 3. Identify function entries from `bl` targets in the CFG
//! 4. Build call graph via CFG BFS (including tail calls via `b` to function entries)
//! 5. Verify no cycles (defense-in-depth: Move prevents recursion)

use std::collections::{HashMap, HashSet, VecDeque};

use cfg::Cfg;
use petgraph::graph::{DiGraph, NodeIndex};

use crate::DecodedInstruction;
use crate::error::VerificationError;

/// Default stack budget in bytes (1 MiB).
///
/// This is generous for Move programs which have bounded call depth.
/// The actual OS thread stack is typically 8 MiB, so 1 MiB leaves plenty
/// of headroom for the runtime, signal handlers, and native functions.
pub const DEFAULT_STACK_BUDGET: u32 = 1024 * 1024;

/// Analyzes stack depth for a sequence of decoded instructions.
pub struct StackAnalyzer<'a> {
    instructions: &'a [DecodedInstruction],
    cfg: &'a Cfg,
}

impl<'a> StackAnalyzer<'a> {
    pub fn new(instructions: &'a [DecodedInstruction], cfg: &'a Cfg) -> Self {
        Self { instructions, cfg }
    }

    /// Run stack depth verification against the given budget.
    ///
    /// Returns reachable function entry offsets (instruction indices into
    /// `self.instructions`) for use in multi-root reachability, or an error
    /// if the stack depth exceeds the budget or cycles are detected.
    pub fn verify(&self, budget: u32) -> Result<Vec<usize>, VerificationError> {
        if self.instructions.is_empty() {
            return Ok(vec![]);
        }

        // Linear sum of all SP decrements as conservative upper bound.
        // This overestimates (counts all functions, not just the worst-case
        // call chain), but with a 1 MiB budget and realistic Move programs
        // the overestimate is negligible.
        let total_sp = self
            .instructions
            .iter()
            .try_fold(0u32, |acc, instruction| {
                Ok(acc.saturating_add(instruction.sp_decrement()?))
            })?;

        if total_sp > budget {
            return Err(VerificationError::StackDepthExceeded {
                max_depth: total_sp,
                budget,
            });
        }

        // Build a directed graph of function calls (bl targets + tail calls).
        let call_graph = self.build_call_graph();

        // Move forbids recursion, so the call graph must be a DAG.
        // A cycle would imply unbounded stack depth.
        self.check_no_cycles(&call_graph)?;

        // Return function entries reachable from offset 0 via the call graph.
        // The caller uses these as additional roots for unreachable-code detection.
        Ok(self.reachable_function_entries(&call_graph))
    }

    /// Build a call graph as a `DiGraph` where each node weight is the
    /// function's entry byte offset and edges represent calls.
    ///
    /// Function entries are: offset 0 (entry) plus all internal `bl` targets.
    /// For each function, BFS through CFG successors assigns blocks to functions,
    /// stopping at blocks belonging to other functions. Tail calls (`b`/`b.cond`
    /// to another function's entry) are recorded as call edges.
    fn build_call_graph(&self) -> DiGraph<usize, ()> {
        // Collect function entries: offset 0 + all bl targets from CFG blocks
        let mut entries = HashSet::new();
        entries.insert(0usize);

        let valid_offsets: HashSet<usize> = self.instructions.iter().map(|i| i.offset).collect();

        for block in self.cfg.blocks() {
            for &target in self.cfg.call_targets(block) {
                if valid_offsets.contains(&target) {
                    entries.insert(target);
                }
            }
        }

        // Map byte offset → block index for the block starting at that offset
        let offset_to_block: HashMap<usize, cfg::BlockIndex> = self
            .cfg
            .blocks()
            .map(|b| {
                let start_idx = self.cfg.instruction_range(b).start;
                (self.instructions[start_idx].offset, b)
            })
            .collect();

        // Build the DiGraph: one node per function entry
        let mut graph = DiGraph::new();
        let mut offset_to_node: HashMap<usize, NodeIndex> = HashMap::new();

        for &entry in &entries {
            let node = graph.add_node(entry);
            offset_to_node.insert(entry, node);
        }

        // For each function entry, BFS through CFG successors.
        // Stop at blocks that start at another function's entry.
        // Record bl targets and tail-call edges as call graph edges.
        for &entry in &entries {
            let Some(&start_block) = offset_to_block.get(&entry) else {
                continue;
            };

            let caller = offset_to_node[&entry];
            let mut callees = HashSet::new();
            let mut visited = HashSet::new();
            let mut queue = VecDeque::new();

            visited.insert(start_block);
            queue.push_back(start_block);

            while let Some(block) = queue.pop_front() {
                // Collect bl targets from this block
                for &target in self.cfg.call_targets(block) {
                    if entries.contains(&target) {
                        callees.insert(target);
                    }
                }

                // Traverse CFG successors, stopping at other function entries
                for succ in self.cfg.successors(block) {
                    if visited.contains(&succ) {
                        continue;
                    }

                    let succ_start = self.cfg.instruction_range(succ).start;
                    let succ_offset = self.instructions[succ_start].offset;

                    if succ_offset != entry && entries.contains(&succ_offset) {
                        // Successor is another function's entry — tail call
                        callees.insert(succ_offset);
                    } else {
                        // Same function, continue BFS
                        visited.insert(succ);
                        queue.push_back(succ);
                    }
                }
            }

            for callee_offset in callees {
                let callee = offset_to_node[&callee_offset];
                graph.add_edge(caller, callee, ());
            }
        }

        graph
    }

    /// Verify the call graph is acyclic using petgraph's topological sort.
    fn check_no_cycles(&self, graph: &DiGraph<usize, ()>) -> Result<(), VerificationError> {
        if let Err(cycle) = petgraph::algo::toposort(graph, None) {
            let cycle_entry = graph[cycle.node_id()];
            return Err(VerificationError::RecursiveCallGraph { cycle_entry });
        }
        Ok(())
    }

    /// BFS on call graph from function at offset 0 to find reachable function entries.
    /// Returns instruction indices (not byte offsets) for use with
    /// `find_unreachable_blocks`.
    fn reachable_function_entries(&self, graph: &DiGraph<usize, ()>) -> Vec<usize> {
        // Find the node for the entry function (offset 0)
        let entry_node = graph
            .node_indices()
            .find(|&n| graph[n] == 0)
            .expect("call graph must contain entry function at offset 0");

        let mut bfs = petgraph::visit::Bfs::new(graph, entry_node);
        let mut entries = Vec::new();

        while let Some(node) = bfs.next(graph) {
            let offset = graph[node];
            if let Some(instr_idx) = self
                .instructions
                .iter()
                .position(|instr| instr.offset == offset)
            {
                entries.push(instr_idx);
            }
        }

        entries
    }
}

#[cfg(test)]
mod tests {
    use cfg::build_cfg;

    use crate::decode_instructions;
    use crate::error::VerificationError;

    use super::{DEFAULT_STACK_BUDGET, DecodedInstruction, StackAnalyzer};

    fn decode(bytes: &[u8]) -> Vec<DecodedInstruction> {
        decode_instructions(bytes).expect("decode failed")
    }

    #[test]
    fn test_empty_code() {
        let instructions = decode(&[]);
        let cfg = build_cfg(&instructions);
        let analyzer = StackAnalyzer::new(&instructions, &cfg);
        analyzer.verify(DEFAULT_STACK_BUDGET).unwrap();
    }

    #[test]
    fn test_budget_exceeded() {
        // Single function with large frame
        // sub sp, sp, #4095 (max 12-bit immediate)
        let code = [
            0xff, 0xff, 0x3f, 0xd1, // sub sp, sp, #4095   [0]
            0xff, 0xff, 0x3f, 0x91, // add sp, sp, #4095   [4]
            0xc0, 0x03, 0x5f, 0xd6, // ret                  [8]
        ];
        let instructions = decode(&code);
        let cfg = build_cfg(&instructions);
        let analyzer = StackAnalyzer::new(&instructions, &cfg);
        let result = analyzer.verify(8); // very small budget
        assert!(
            matches!(
                result,
                Err(VerificationError::StackDepthExceeded {
                    max_depth: 4095,
                    budget: 8
                })
            ),
            "should report stack depth exceeded: {:?}",
            result
        );
    }

    #[test]
    fn test_linear_sum_across_functions() {
        // Two functions: func1 (frame=16), func2 (frame=32)
        // Linear sum = 48 (conservative: counts both, even though
        // the actual worst-case call depth would be less)
        let code = [
            0xff, 0x43, 0x00, 0xd1, // sub sp, sp, #16    (offset 0)
            0x03, 0x00, 0x00, 0x94, // bl #12 (offset 16)  (offset 4)
            0xff, 0x43, 0x00, 0x91, // add sp, sp, #16    (offset 8)
            0xc0, 0x03, 0x5f, 0xd6, // ret                (offset 12)
            0xff, 0x83, 0x00, 0xd1, // sub sp, sp, #32    (offset 16) <- func2
            0xff, 0x83, 0x00, 0x91, // add sp, sp, #32    (offset 20)
            0xc0, 0x03, 0x5f, 0xd6, // ret                (offset 24)
        ];
        let instructions = decode(&code);
        let cfg = build_cfg(&instructions);
        let analyzer = StackAnalyzer::new(&instructions, &cfg);

        // Budget of 47 should fail (linear sum = 16 + 32 = 48)
        let result = analyzer.verify(47);
        assert!(
            matches!(
                result,
                Err(VerificationError::StackDepthExceeded {
                    max_depth: 48,
                    budget: 47
                })
            ),
            "linear sum should be 48: {:?}",
            result
        );

        // Budget of 48 should pass
        let result = analyzer.verify(48);
        assert!(result.is_ok(), "budget of 48 should pass: {:?}", result);
    }

    #[test]
    fn test_cycle_detection_via_bl() {
        // Two functions that call each other via bl:
        // func_a [0]: bl func_b (→8); ret
        // func_b [8]: bl func_a (→0); ret
        let code = [
            0x02, 0x00, 0x00, 0x94, // bl #2 (→8)          [0]
            0xc0, 0x03, 0x5f, 0xd6, // ret                  [4]
            0xfe, 0xff, 0xff, 0x97, // bl #-2 (→0)          [8]
            0xc0, 0x03, 0x5f, 0xd6, // ret                  [12]
        ];
        let instructions = decode(&code);
        let cfg = build_cfg(&instructions);
        let analyzer = StackAnalyzer::new(&instructions, &cfg);
        let result = analyzer.verify(DEFAULT_STACK_BUDGET);
        assert!(
            matches!(result, Err(VerificationError::RecursiveCallGraph { .. })),
            "should detect recursive call graph via bl"
        );
    }

    #[test]
    fn test_cycle_detection_via_tail_call() {
        // func_a calls func_b via bl, func_b tail-calls func_a via b.
        // This is a cycle: A → B → A (where B→A is a tail call).
        //
        // func_a [0]: bl func_b (→8)
        // func_a [4]: ret
        // func_b [8]: b func_a (→0)   ← tail call
        let code = [
            0x02, 0x00, 0x00, 0x94, // bl #2 (→8)          [0]
            0xc0, 0x03, 0x5f, 0xd6, // ret                  [4]
            0xfe, 0xff, 0xff, 0x17, // b #-2 (→0)           [8]
        ];
        let instructions = decode(&code);
        let cfg = build_cfg(&instructions);
        let analyzer = StackAnalyzer::new(&instructions, &cfg);
        let result = analyzer.verify(DEFAULT_STACK_BUDGET);
        assert!(
            matches!(result, Err(VerificationError::RecursiveCallGraph { .. })),
            "should detect recursive call graph via tail call: {:?}",
            result
        );
    }

    #[test]
    fn test_reachable_entries_returned() {
        // func1 calls func2; both should be reachable
        let code = [
            0x02, 0x00, 0x00, 0x94, // bl #8 (→ offset 8)  [0]
            0xc0, 0x03, 0x5f, 0xd6, // ret                  [4]
            0x00, 0x00, 0x80, 0xd2, // mov x0, #0           [8]
            0xc0, 0x03, 0x5f, 0xd6, // ret                  [12]
        ];
        let instructions = decode(&code);
        let cfg = build_cfg(&instructions);
        let analyzer = StackAnalyzer::new(&instructions, &cfg);
        let entries = analyzer.verify(DEFAULT_STACK_BUDGET).unwrap();

        // Should return instruction indices for both function entries
        assert!(entries.contains(&0), "entry function should be reachable");
        assert!(
            entries.contains(&2),
            "called function (instruction index 2) should be reachable"
        );
    }

    #[test]
    fn test_no_frame_passes() {
        // mov x0, #0; ret — no SP modifications at all
        let code = [
            0x00, 0x00, 0x80, 0xd2, // mov x0, #0
            0xc0, 0x03, 0x5f, 0xd6, // ret
        ];
        let instructions = decode(&code);
        let cfg = build_cfg(&instructions);
        let analyzer = StackAnalyzer::new(&instructions, &cfg);
        let result = analyzer.verify(DEFAULT_STACK_BUDGET);
        assert!(result.is_ok());
    }
}
