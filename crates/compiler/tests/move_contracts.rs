// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tests that compile real Move bytecode (.mv files) through the full pipeline.

use compiler::Target;

/// End-to-end from the checked-in add.mv (two-argument u64 addition).
#[test]
fn add_module_from_mv_file() {
    let bytecode = include_bytes!("../../../tests/move_samples/add.mv");

    let asm = compiler::compile(&Target::host(), bytecode).expect("compile from .mv file failed");

    assert!(
        asm.contains("\tadd\t"),
        "assembly should contain 'add' instruction"
    );
    assert!(
        asm.contains("\tret"),
        "assembly should contain ret instruction"
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
// #[ignore = "requires dependency .mv files (ascii, string, type_name, tx_context, object, ...)"]
// fn sui_framework_balance() {
//     let bytecode = include_bytes!("../../../tests/move_samples/sui_framework/balance.mv");
//     // TODO: use compile_module_with_dependencies once dependency loading is supported.
//     compiler::compile(&Target::host(), bytecode)
//         .expect("balance.mv compilation failed");
// }

// #[test]
// #[ignore = "requires table.mv — not yet supported: dual phantom generics, trait bounds"]
// fn sui_framework_table() {
//     let bytecode = include_bytes!("../../../tests/move_samples/sui_framework/table.mv");
//     compiler::compile(&compiler::Target::Aarch64, bytecode)
//         .expect("table.mv compilation failed");
// }

// #[test]
// #[ignore = "requires coin.mv — not yet supported: events, dynamic fields"]
// fn sui_framework_coin() {
//     let bytecode = include_bytes!("../../../tests/move_samples/sui_framework/coin.mv");
//     compiler::compile(&compiler::Target::Aarch64, bytecode)
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
//     compiler::compile(&compiler::Target::Aarch64, bytecode)
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
//     compiler::compile(&compiler::Target::Aarch64, bytecode)
//         .expect("suins.mv compilation failed");
// }
