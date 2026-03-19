---
name: Compiler crate testing patterns
description: Test architecture and coverage patterns for crates/compiler, including key gaps identified
type: project
---

The compiler crate test suite uses a consistent pattern: build Move modules programmatically via `CompiledModuleBuilder`, compile to assembly, and assert on assembly text output (symbol names, instruction patterns, runtime call symbols).

**Key gaps identified (2026-03-19):**
- `emit_logical_binop` (Operation::And/Or on bools) has zero dedicated tests
- `mod_zero_emits_abort` -- Mod division-by-zero path untested (same logic as Div but distinct code path)
- `get_global` storage operation implemented but untested
- No arithmetic tests for small widths (u8, u16, u32)
- `erase_type_params` in state.rs has no direct unit tests for nested types

**Why:** This is a compiler for blockchain smart contracts where correctness is critical. Missing coverage on arithmetic overflow/error paths could lead to silent miscompilation.

**How to apply:** When reviewing changes to arithmetic.rs, check that all operations have both a "compiles correctly" test and an "emits error check" test. When adding new operations, add both types.
