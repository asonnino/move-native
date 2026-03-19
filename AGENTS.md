# Repository Guidelines

## Project Structure & Module Organization
`move-native` is a Rust workspace for ahead-of-time Move compilation on Sui.
Core crates live under `crates/`:
- `compiler`: Move bytecode to LLVM/AArch64 assembly
- `graph`: CFG and Arm64 analysis helpers
- `instrumenter`: gas instrumentation over assembly
- `verifier`: deterministic Arm64 verifier
- `runtime`: executable memory, signals, and execution
- `runner`: end-to-end pipeline and CLI

Tests live in `tests/`: hand-written assembly in `tests/asm/` and
compiled Move fixtures in `tests/move/`. CI config is in
`.github/workflows/`.

## Architecture Notes
The pipeline is
`Move bytecode -> compiler -> instrumenter -> verifier -> runtime`.
This repo targets Arm64 and reserves register `x23` for gas metering.
Back-edge gas checks are a core invariant; changes touching control flow,
codegen, or assembly output must preserve verifier expectations and
deterministic execution.

## Build, Test, and Development Commands
- `cargo build --workspace`: build all crates
- `cargo test --workspace`: run the full workspace test suite
- `cargo test -p compiler`: iterate on compiler changes quickly
- `cargo test -p runtime`: run runtime and executor tests
- `cargo test -p instrumenter` / `cargo test -p verifier`:
  validate gas instrumentation or binary verification changes
- `cargo nextest run --workspace --profile ci`: match the main CI test runner
- `cargo fmt --all`: format Rust code
- `cargo clippy --workspace --all-features --tests --no-deps -- -D warnings`:
  run the same lint level as CI

LLVM 18 is required for `inkwell`; CI sets `LLVM_SYS_181_PREFIX=/usr/lib/llvm-18`.

## Coding Style & Naming Conventions
Use Rust 2021 defaults and `rustfmt` formatting. Prefer small, focused
modules and explicit error propagation with `thiserror`. Public APIs and
key lowering steps should have short doc comments. Follow existing naming:
- snake_case for functions/modules/tests
- UpperCamelCase for types/traits
- commit-visible runtime symbols like `__move_rt_*`

Keep files ASCII unless the file already uses Unicode.

## Testing Guidelines
Add unit tests next to the code they validate and integration tests under
`crates/*/tests` or `tests/`. Name tests by behavior, e.g.
`same_name_cross_module_no_collision`.

Keep compiler integration tests focused on emitted assembly and symbol shape.
Put actual execution tests in `runtime`, not `compiler`.
Prefer behavior-focused assertions when verifier or runtime coverage exists;
use string-matching only when assembly shape is the actual contract.

## Commit & Pull Request Guidelines
Recent history uses Conventional Commit prefixes such as `feat:`, `fix:`,
and `refactor:`. Keep subjects short and imperative, for example
`fix: qualify cross-module function symbols`.

PRs should explain the affected crate(s), the behavior change, and the
commands used for verification. Link issues when relevant. If output or
assembly shape changed, include a short before/after summary rather than
screenshots.
