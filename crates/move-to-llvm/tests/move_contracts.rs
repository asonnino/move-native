// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tests that compile real Move bytecode (.mv files) through the full pipeline.
//!
//! ## Test tiers
//!
//! - **Tier 1 (must pass)**: Simple contracts that exercise currently-supported features.
//! - **Tier 2 (expected failures, `#[ignore]`)**: Real Sui framework modules that exercise
//!   features we haven't implemented yet. Each failure tells us what to implement next.
//! - **Tier 3 (aspirational, `#[ignore]`)**: Full DeFi protocols (DeepBook, SuiNS).
//!   These become graduation tests.
//!
//! ## Adding new contracts
//!
//! 1. Write or obtain the `.move` source
//! 2. Compile with `sui move build` to get `.mv` bytecode
//! 3. Place the `.mv` file in `tests/move_samples/`
//! 4. Add a test below using `include_bytes!`

// ===================================================================
// Tier 1: Simple contracts (must pass)
// ===================================================================

/// End-to-end from the checked-in add.mv (two-argument u64 addition).
#[test]
fn add_module_from_mv_file() {
    let bytecode = include_bytes!("../../../tests/move_samples/add.mv");

    let asm = move_to_llvm::compile(&move_to_llvm::Target::Aarch64, bytecode)
        .expect("compile from .mv file failed");

    assert!(asm.contains("add"), "assembly should contain 'add'");
    assert!(asm.contains("ret"), "assembly should contain ret");
}

/// Serialize → deserialize → compile: the true end-to-end path through `compile()`.
#[test]
fn add_module_round_trip_via_serialization() {
    use move_binary_format::file_format::*;
    use move_to_llvm::module::CompiledModuleBuilder;

    let module = CompiledModuleBuilder::new()
        .function(
            "add",
            vec![SignatureToken::U64, SignatureToken::U64],
            vec![SignatureToken::U64],
            vec![],
            vec![
                Bytecode::CopyLoc(0),
                Bytecode::CopyLoc(1),
                Bytecode::Add,
                Bytecode::Ret,
            ],
        )
        .build();

    let mut bytecode = Vec::new();
    module
        .serialize_with_version(module.version, &mut bytecode)
        .expect("serialization failed");

    let asm = move_to_llvm::compile(&move_to_llvm::Target::Aarch64, &bytecode)
        .expect("compile from bytecode failed");

    assert!(asm.contains("add"));
    assert!(asm.contains("ret"));
    assert!(
        !asm.contains("x23"),
        "should not reference reserved register x23"
    );
}

// ===================================================================
// Tier 2: Sui framework modules (expected failures — uncomment as supported)
// ===================================================================
//
// To add these tests:
// 1. Build Sui framework: `cd sui && cargo build -p sui-framework`
// 2. Find compiled .mv files in build artifacts
// 3. Copy to tests/move_samples/sui_framework/
//
// Alternatively, compile individual modules:
//   sui move build --path <module_dir>

// #[test]
// #[ignore = "requires balance.mv — not yet supported: phantom generics"]
// fn sui_framework_balance() {
//     let bytecode = include_bytes!("../../../tests/move_samples/sui_framework/balance.mv");
//     move_to_llvm::compile(&move_to_llvm::Target::Aarch64, bytecode)
//         .expect("balance.mv compilation failed");
// }

// #[test]
// #[ignore = "requires table.mv — not yet supported: dual phantom generics, trait bounds"]
// fn sui_framework_table() {
//     let bytecode = include_bytes!("../../../tests/move_samples/sui_framework/table.mv");
//     move_to_llvm::compile(&move_to_llvm::Target::Aarch64, bytecode)
//         .expect("table.mv compilation failed");
// }

// #[test]
// #[ignore = "requires coin.mv — not yet supported: events, dynamic fields"]
// fn sui_framework_coin() {
//     let bytecode = include_bytes!("../../../tests/move_samples/sui_framework/coin.mv");
//     move_to_llvm::compile(&move_to_llvm::Target::Aarch64, bytecode)
//         .expect("coin.mv compilation failed");
// }

// ===================================================================
// Tier 3: Real DeFi protocols (aspirational)
// ===================================================================
//
// To add DeepBook tests:
// 1. Clone https://github.com/MystenLabs/deepbookv3
// 2. Build: `cd deepbookv3/packages/deepbook && sui move build`
// 3. Copy .mv files from build/deepbook/bytecode_modules/ to
//    tests/move_samples/deepbook/
//
// DeepBook exercises:
// - Heavy dual phantom generics <BaseAsset, QuoteAsset>
// - Complex cross-module calls (pool → book → state → vault)
// - Custom data structures (BigVector)
// - Events, dynamic fields, governance/staking

// #[test]
// #[ignore = "requires deepbook .mv files — aspirational graduation test"]
// fn deepbook_pool() {
//     let bytecode = include_bytes!("../../../tests/move_samples/deepbook/pool.mv");
//     move_to_llvm::compile(&move_to_llvm::Target::Aarch64, bytecode)
//         .expect("deepbook pool.mv compilation failed");
// }

// SuiNS exercises:
// - Phantom type params for type-safe dynamic fields
// - Witness-based authorization pattern
// - Multiple interacting modules

// #[test]
// #[ignore = "requires suins .mv files — aspirational graduation test"]
// fn suins_core() {
//     let bytecode = include_bytes!("../../../tests/move_samples/suins/suins.mv");
//     move_to_llvm::compile(&move_to_llvm::Target::Aarch64, bytecode)
//         .expect("suins.mv compilation failed");
// }
