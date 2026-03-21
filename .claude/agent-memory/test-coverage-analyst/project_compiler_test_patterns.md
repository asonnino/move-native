---
name: Compiler crate testing patterns
description: Test architecture, coverage patterns, and identified gaps for crates/compiler as of 2026-03-21
type: project
---

The compiler crate test suite uses a consistent pattern: build Move modules programmatically via `CompiledModuleBuilder`, compile to assembly, and assert on assembly text output (symbol names, instruction patterns, runtime call symbols).

**Critical gaps identified (2026-03-21):**

1. **Enum support (enums.rs)** -- NEW file with zero test coverage. PackVariant, UnpackVariant (by-value and by-ref) all untested. Blocker: `CompiledModuleBuilder` needs enum definition support.

2. **VariantSwitch control flow** -- New complex control flow in control_flow.rs with reference/by-value branching paths, completely untested.

3. **`erase_type_params` in state.rs** -- Critical pure function for phantom generic correctness. Trivially testable (no LLVM context needed), zero coverage.

4. **x23 gas register validation** -- `has_x23_misuse` in assembly.rs only runs as debug_assert (skipped in release). Should be a proper test.

5. **Enum equality comparison** -- `compare_enum_values` path in arithmetic.rs untested.

**Moderate gaps:**
- `get_global` storage operation untested
- `FreezeRef` and `GetField` struct ops untested
- `mod_zero_emits_abort` untested
- `root_cause` error peeling untested
- Cross-module and generic native call paths lack dedicated unit tests

**Why:** This is a compiler for blockchain consensus -- correctness bugs cause validator disagreement. Enum support is actively being added.

**How to apply:** When adding enum support to CompiledModuleBuilder, prioritize adding PackVariant/UnpackVariant/VariantSwitch tests immediately. The erase_type_params tests can be added without any builder changes. When reviewing arithmetic.rs changes, verify all operations have both "compiles" and "emits error check" tests.
