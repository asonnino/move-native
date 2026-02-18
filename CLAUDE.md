# Move Native Compilation for Sui

## Project Goal

Replace the Move VM interpreter on Sui with ahead-of-time compiled native code, eliminating VM overhead while maintaining deterministic execution across all blockchain validators.

## Key Insight

Based on the DeCl paper (OSDI 2025 - "Deterministic Client: Enforcing Determinism on Untrusted Machine Code"), we can enforce determinism on native machine code through static verification rather than interpretation. This gives ~20% overhead with metering vs 30x overhead with interpreters.

---

## Context: Sui/Move Specifics

- **Move bytecode** is the smart contract language for Sui
- **Move has no dynamic dispatch** - all call targets known at compile time
- **Move guarantees memory safety** through its type system - no need for software memory isolation
- **Native functions** (vector ops, crypto) are implemented in Rust and have fixed gas costs
- **Objects are provided upfront** through caches - no runtime storage access during execution
- **Loops are common** in Move programs

## Determinism Requirement

All validators must agree on **"completed" vs "aborted"** - they do NOT need to agree on exact instruction count at abort. If some validators do slightly more work before aborting, that's fine.

---

## Architecture Decisions

| Decision            | Choice                                 | Rationale                                                |
| ------------------- | -------------------------------------- | -------------------------------------------------------- |
| Compilation backend | Move → LLVM IR → Arm64                 | Leverage LLVM optimizations and codegen                  |
| Gas granularity     | Back-edge only                         | Minimal overhead; forward-only code bounded by code size |
| Memory isolation    | None                                   | Trust Move's type system                                 |
| Out-of-gas handling | `brk #0` + signal handler              | Overhead only on actual out-of-gas                       |
| Target architecture | Arm64 (macOS for dev)                  | Clean ISA, simpler than x86-64                           |
| Repository approach | Fresh repo, Sui crates as dependencies | Clean architecture, fast builds                          |

---

## Technical Design

### Reserved Registers

Only one register needed:

| Register | Purpose                                            |
| -------- | -------------------------------------------------- |
| `x23`    | Gas counter (callee-saved, preserved across calls) |

Standard Arm64 calling convention (AAPCS64) otherwise.

### Gas Instrumentation

At every back-edge (loop iteration):

```asm
sub x23, x23, #N      // decrement by N (instructions in block)
tbz x23, #63, .Look    // if bit 63 is 0 (positive), continue
brk #0                // trap - out of gas
.Look:
// ... continue execution ...
```

**Optimization**: Forward branches only need decrement, no check. Forward-only code is bounded by code size and will terminate.

### Verification Requirements

The verifier must confirm:

1. All instructions in deterministic whitelist (no atomics, no FP, no syscalls)
2. Every back-edge preceded by gas check sequence (`sub x23` + `tbz x23, #63` + `brk #0`)
3. `x23` only modified by gas decrements
4. All branch targets are valid instruction boundaries (trivial on Arm64)
5. No unreachable code (all basic blocks reachable from entry point) - prevents an unrelated bug from allowing the program to jump into uninstrumented dead code containing an infinite loop
6. No indirect branches (`br`, `blr`, `bra*`, `blra*`) - these have register targets that can't be statically verified; Move's lack of dynamic dispatch means they shouldn't appear in compiled output

### Runtime Entry Point

```rust
fn execute_move(entry: fn(), gas_limit: i64) -> Result {
    GAS.store(gas_limit);           // maps to x23
    install_sigtrap_handler();      // catches brk #0
    OUT_OF_GAS.store(false);

    entry();                        // call native Move code

    if OUT_OF_GAS.load() {
        Err(OutOfGas)
    } else {
        Ok(())
    }
}

// Signal handler for SIGTRAP:
fn sigtrap_handler(sig: i32, info: &siginfo_t, ctx: &mut ucontext_t) {
    OUT_OF_GAS.store(true);
    ctx.pc += 4;  // advance past brk instruction
    // Return from handler - execution continues but will exit
}
```

---

## Compilation Pipeline

```
Move Bytecode
     ↓
Move → LLVM IR Lowering
  - Monomorphize generics
  - Lower stack operations to SSA
     ↓
LLVM Optimization Passes (-O2/-O3)
     ↓
LLVM → Arm64 Assembly
     ↓
Gas Instrumentation Pass
  - Find back-edges in CFG
  - Insert sub/tbz/brk sequences
     ↓
Assemble + Link → module.so
     ↓
Verification Pass
  - Instruction whitelist
  - Gas check verification
  - x23 usage verification
     ↓
Ready for execution
```

---

## Repository Structure

```
move-native/
├── Cargo.toml
├── crates/
│   ├── move-to-llvm/          # Move bytecode → LLVM IR
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── lowering.rs    # Main translation logic
│   │   │   ├── types.rs       # Move types → LLVM types
│   │   │   └── intrinsics.rs  # Native function declarations
│   │   └── Cargo.toml
│   │
│   ├── gas-instrument/        # Arm64 assembly rewriter
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── parser.rs      # Parse Arm64 assembly
│   │   │   ├── cfg.rs         # Control flow graph, find back-edges
│   │   │   └── instrument.rs  # Insert gas checks
│   │   └── Cargo.toml
│   │
│   ├── native-verifier/       # Verify compiled modules
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── decode.rs      # Arm64 instruction decoder
│   │   │   ├── whitelist.rs   # Allowed instructions
│   │   │   └── gas_check.rs   # Verify gas instrumentation
│   │   └── Cargo.toml
│   │
│   ├── native-runtime/        # Execution runtime
│   │   ├── src/
│   │   │   ├── lib.rs
│   │   │   ├── entry.rs       # Entry point, gas setup
│   │   │   ├── signal.rs      # SIGTRAP handler
│   │   │   └── natives.rs     # Native function implementations
│   │   └── Cargo.toml
│   │
│   └── move-native-cli/       # CLI tool for testing
│       ├── src/
│       │   └── main.rs
│       └── Cargo.toml
│
├── tests/
│   ├── move_sources/          # Test Move programs
│   ├── asm_samples/           # Hand-written Arm64 for testing
│   └── integration/
│
└── README.md
```

---

## Implementation Phases

### Phase 1: Gas Instrumentation + Verifier (START HERE)

Build and test on hand-written Arm64 assembly. This proves the core DeCl mechanism without needing the Move compiler.

**gas-instrument crate:**

- Parse Arm64 assembly text (or use existing crate)
- Build control flow graph from instructions
- Identify back-edges (target address ≤ current address)
- Insert gas check sequences before back-edge branches
- Output instrumented assembly

**native-verifier crate:**

- Decode Arm64 binary (use `capstone` or `bad64` crate)
- Check each instruction against deterministic whitelist
- Verify gas sequences present at all back-edges
- Verify x23 only modified by gas decrements

**Test flow:**

```bash
# Hand-written test.s with a loop
cat test.s | gas-instrument > test_instrumented.s
as -o test.o test_instrumented.s
native-verifier test.o  # should pass
```

### Phase 2: Runtime (1 week)

**native-runtime crate:**

- Signal handler setup for SIGTRAP
- Entry point that sets x23 and calls native code
- Out-of-gas detection and error return

Test with hand-written instrumented assembly loaded via `dlopen`.

### Phase 3: Move → LLVM (4-8 weeks)

**move-to-llvm crate:**

- Parse Move bytecode using `move-binary-format`
- Lower to LLVM IR using `inkwell`
- Start with tiny subset: integers, arithmetic, loops
- Expand: locals, function calls, structs, references, generics

### Phase 4: Sui Integration (2-4 weeks)

- Connect to Sui execution engine
- Replace interpreter calls with native execution
- Benchmark against Move VM

---

## Dependencies

```toml
[dependencies]
# Move bytecode parsing (from Sui repo)
move-binary-format = { git = "https://github.com/MystenLabs/sui" }
move-core-types = { git = "https://github.com/MystenLabs/sui" }

# LLVM bindings (for move-to-llvm)
inkwell = { version = "0.2", features = ["llvm15-0"] }

# Arm64 disassembly (for native-verifier)
capstone = "0.12"
# Or: bad64 = "0.3"

# Signal handling (for native-runtime)
nix = { version = "0.27", features = ["signal"] }
libc = "0.2"
```

---

## Key References

### DeCl Paper (Primary Reference)

The attached `osdi25-yedidia.pdf` contains the core techniques. Key sections:

- **Section 3.1 (Arm64)**: Deterministic instruction subset, ~180 base + 430 SIMD instructions allowed
- **Section 4 (Deterministic Metering)**: Gas counter in reserved register
- **Section 4.2 (Branch-based Metering)**: The `sub/tbz/brk` sequence we use
- **Section 4.2.1 (Removing gas checks)**: Optimization for forward branches
- **Table 3**: Register reservations for different configurations

### Arm64 Architecture

- **AAPCS64 calling convention**: x0-x7 arguments, x0 return, x19-x28 callee-saved
- **x23 is callee-saved**: Preserved across function calls automatically
- **Fixed 4-byte instructions**: No alignment/bundling complexity like x86-64

### Sui/Move

- `move-binary-format` crate: Bytecode parsing and types
- `move-core-types` crate: Core Move types
- Move bytecode is stack-based with typed operands

---

## Arm64 Instruction Whitelist (Subset)

Based on DeCl, allow approximately:

**Base instructions (~180):**

- Arithmetic: `add`, `sub`, `mul`, `sdiv`, `udiv`, `neg`, etc.
- Logic: `and`, `orr`, `eor`, `bic`, `orn`, etc.
- Shifts: `lsl`, `lsr`, `asr`, `ror`
- Moves: `mov`, `movz`, `movn`, `movk`
- Loads/stores: `ldr`, `str`, `ldp`, `stp`, `ldrb`, `strb`, etc.
- Branches: `b`, `b.cond`, `bl`, `ret`, `cbz`, `cbnz`, `tbz`, `tbnz`
- Compare: `cmp`, `cmn`, `tst`
- Address: `adr`, `adrp`

**Reject:**

- Atomics: `ldxr`, `stxr`, `ldadd`, `cas`, etc.
- System: `svc`, `hvc`, `smc`, `msr`, `mrs`
- Floating point: `fadd`, `fmul`, `fcvt`, etc. (if desired)
- Barriers: `dmb`, `dsb`, `isb`
- Cache: `dc`, `ic`
- Unpredictable encodings

---

## Example: Hand-Written Test Assembly

```asm
// simple_loop.s - Simple loop for testing gas instrumentation
.global _simple_loop
.align 4

_simple_loop:
    mov x0, #0              // counter = 0
    mov x1, #1000000        // limit

.Lloop:
    add x0, x0, #1          // counter++
    cmp x0, x1
    b.lt .Lloop             // back-edge: needs gas check

    ret

// After gas instrumentation, .Lloop becomes:
// .Lloop:
//     add x0, x0, #1
//     cmp x0, x1
//     sub x23, x23, #3      // 3 instructions in block
//     tbz x23, #63, .Look
//     brk #0
// .Look:
//     b.lt .Lloop
```
