# Move Native

> **Warning**
> This is experimental research code and should not be used in production. It is provided as-is for educational and research purposes only.

[![Rust](https://img.shields.io/badge/rust-1.84+-orange.svg)](https://www.rust-lang.org)
[![License](https://img.shields.io/badge/license-Apache--2.0-blue.svg)](LICENSE)

Ahead-of-time native compilation for Move smart contracts, replacing the Move VM interpreter with verified native code execution.

## Overview

Based on the [DeCl paper](https://www.usenix.org/conference/osdi25/presentation/yedidia) (OSDI 2025), this project enforces deterministic execution on native Arm64 code through static verification rather than interpretation.

## Usage

```bash
# Instrument assembly with gas checks
cat loop.s | cargo run -p gas-instrument > loop_instrumented.s

# Verify a compiled object file
cargo run -p native-verifier -- module.o
```

## License

Apache-2.0
