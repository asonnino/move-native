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

/// Nested loops and if/else branches (control_flow.mv).
#[test]
fn control_flow_module_from_mv_file() {
    let bytecode = include_bytes!("../../../tests/move_samples/control_flow.mv");
    let asm =
        compiler::compile(&Target::host(), bytecode).expect("control_flow.mv compilation failed");
    assert!(asm.contains("sum_to"), "missing sum_to");
    assert!(asm.contains("sum_even"), "missing sum_even");
    assert!(asm.contains("nested_sum"), "missing nested_sum");
}

// Sui framework modules are tested in sui_framework.rs
