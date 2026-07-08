# Move Native

> **Warning**
> This is experimental research code and should not be used in production.
> It is provided as-is for educational and research purposes only.

[![Rust](https://img.shields.io/badge/rust-1.93+-blue.svg)](https://www.rust-lang.org)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Ahead-of-time compilation of Move smart contracts to native Arm64 code, replacing the Move VM interpreter.
Deterministic execution is enforced through static verification of the compiled binary and gas metering
inserted at loop back-edges (using the reserved register `x23`), following the
[DeCl paper (OSDI 2025)](https://www.usenix.org/conference/osdi25/presentation/yedidia)
(local copy in [`docs/`](docs/osdi25-yedidia.pdf)).

## Quick Start

Requirements: an Arm64 machine, Rust nightly (pinned in `rust-toolchain.toml`, installed
automatically by rustup), and LLVM 18:

```bash
brew install llvm@18                                    # macOS
export LLVM_SYS_181_PREFIX=$(brew --prefix llvm@18)     # on Linux, e.g. /usr/lib/llvm-18
```

The `runner` CLI drives the pipeline stages (Move bytecode → native code → gas instrumentation → verification):

```bash
# compile Move bytecode to Arm64 assembly
cargo run -p runner -- compile tests/move/custom/add.mv

# instrument assembly with gas checks, then assemble and verify it
cargo run -p runner -- instrument tests/asm/simple_loop.s > loop_gas.s
as -o loop_gas.o loop_gas.s
cargo run -p runner -- verify loop_gas.o
```

Run the tests with `cargo test --workspace`.

## License

Apache-2.0
