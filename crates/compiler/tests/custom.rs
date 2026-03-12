// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tests that compile real Move bytecode (.mv files) through the full pipeline.

use compiler::module::framework::ModuleFixture;

fn fixture() -> ModuleFixture {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/move_samples");
    ModuleFixture::from_dir(dir)
}

/// End-to-end from the checked-in add.mv (two-argument u64 addition).
#[test]
fn add_module_from_mv_file() {
    let asm = fixture().compile("M");
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
    let asm = fixture().compile("control_flow");
    assert!(asm.contains("sum_to"), "missing sum_to");
    assert!(asm.contains("sum_even"), "missing sum_even");
    assert!(asm.contains("nested_sum"), "missing nested_sum");
}
