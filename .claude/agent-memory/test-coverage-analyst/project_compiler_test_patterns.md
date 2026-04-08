---
name: Compiler crate testing patterns
description: Test architecture, coverage patterns, and identified gaps for crates/compiler as of 2026-04-07
type: project
---

The compiler crate test suite uses a consistent pattern: build Move modules programmatically via `CompiledModuleBuilder`, compile to assembly, and assert on assembly text output (symbol names, instruction patterns, runtime call symbols).

**Critical gaps identified (2026-04-07):**

1. **object_file.rs** -- Zero test coverage. `linked_text()` and `apply_riscv_call()` are completely untested despite being the load-bearing path for the ZK pipeline. `apply_riscv_call` does bit manipulation on RISC-V auipc+jalr pairs -- a prime candidate for unit tests.

2. **emit_object path** -- Never exercised by any test. All integration tests go through `emit_assembly` via `compile_checked`. The `CodegenBackend::build_object` and `Compiler::emit_object` methods have zero coverage.

3. **set_module_assembly** -- Public API used by the ZK crate, never tested. Should have an integration test verifying that injected assembly symbols appear in the emitted output.

4. **RISC-V `compile_checked_for_target` checks `\tret`** -- This is aarch64 idiom; RISC-V emits `ret` as a pseudoinstruction. The check may pass incidentally but is not architecture-correct.

5. **Enum support (enums.rs)** -- PackVariant, UnpackVariant, VariantSwitch paths still lack dedicated unit tests.

6. **`erase_type_params` in state.rs** -- Critical pure function for phantom generic correctness. Trivially unit-testable, still has zero coverage.

**Moderate gaps:**
- Target methods (`features`, `check_gas_register`, `triple`) have no unit tests
- `has_x23_misuse` validation is well unit-tested but never tested end-to-end (producing assembly that triggers it)
- Error paths in `linked_text` (missing .text section, unresolved symbol, unsupported relocation) untested
- Cross-module and generic native call paths lack dedicated unit tests

**Why:** This is a compiler for blockchain consensus -- correctness bugs cause validator disagreement. The object file / relocation path is critical for the ZK pipeline.

**How to apply:** Prioritize `apply_riscv_call` unit tests and `emit_object` integration tests. These are the highest-risk untested paths.
