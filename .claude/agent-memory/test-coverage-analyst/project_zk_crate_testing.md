---
name: ZK crate test coverage analysis
description: Test gaps and patterns found in crates/zero-knowledge — build_elf untested, RISC-V rounding boundary untested, proof.rs tightly coupled to SP1 SDK
type: project
---

ZK crate (`crates/zero-knowledge/`) test coverage analysis completed 2026-04-09.

Key gaps found:
- `LinkedText::build_elf` has zero test coverage despite hand-constructing binary ELF headers
- RISC-V CALL relocation rounding boundary (the `+0x800` adjustment) never exercised by tests
- `apply_riscv_call` out-of-bounds error path untested
- `proof.rs` entirely untested but mostly justified (SP1 SDK coupling); return-value extraction logic could be extracted into a pure function

**Why:** This is a compiler/ZK pipeline where correctness is critical. Subtle encoding bugs in ELF construction or RISC-V relocations would manifest as opaque SP1 failures.

**How to apply:** When adding tests to this crate, prioritize build_elf header validation and rounding-boundary relocation tests. For proof.rs, suggest extracting pure logic before adding tests rather than trying to mock SP1.
