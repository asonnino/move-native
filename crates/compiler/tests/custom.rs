// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tests that compile real Move bytecode (.mv files) through the full pipeline.

use compiler::module::framework::ModuleFixture;

fn fixture() -> ModuleFixture {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/move/custom");
    ModuleFixture::from_dir(dir)
}

fn fixture_with_dependencies() -> ModuleFixture {
    let base = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/move");
    ModuleFixture::from_dir(format!("{base}/custom"))
        .with_dependencies_from_dir(format!("{base}/stdlib"))
        .with_dependencies_from_dir(format!("{base}/sui"))
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

/// Struct pack/unpack, field borrows, ReadRef, WriteRef, FreezeRef,
/// intra-module calls, arithmetic (geometry.mv).
#[test]
fn geometry_module() {
    let asm = fixture().compile("geometry");
    assert!(asm.contains("new_point"), "missing new_point");
    assert!(asm.contains("sum_fields"), "missing sum_fields");
    assert!(asm.contains("distance_sq"), "missing distance_sq");
    assert!(asm.contains("translate"), "missing translate");
    assert!(asm.contains("midpoint"), "missing midpoint");
}

/// Bitwise ops, shifts, and integer width casts (bitmath.mv).
#[test]
fn bitmath_module() {
    let asm = fixture().compile("bitmath");
    assert!(asm.contains("mask_low_byte"), "missing mask_low_byte");
    assert!(asm.contains("set_bit"), "missing set_bit");
    assert!(asm.contains("rotate_left"), "missing rotate_left");
    assert!(asm.contains("cast_chain"), "missing cast_chain");
    assert!(asm.contains("add_u128"), "missing add_u128");
    assert!(asm.contains("xor_swap"), "missing xor_swap");
}

/// Abort, comparisons, multi-return, function chaining (checked_math.mv).
#[test]
fn checked_math_module() {
    let asm = fixture().compile("checked_math");
    assert!(asm.contains("checked_sub"), "missing checked_sub");
    assert!(asm.contains("safe_div"), "missing safe_div");
    assert!(asm.contains("divmod"), "missing divmod");
    assert!(asm.contains("clamp"), "missing clamp");
    assert!(asm.contains("abs_diff"), "missing abs_diff");
}

/// Generic structs + monomorphization via concrete callers (generics.mv).
#[test]
fn generics_module() {
    let asm = fixture().compile("generics");
    assert!(
        asm.contains("identity_u64"),
        "missing identity_u64 concrete caller"
    );
    assert!(
        asm.contains("swap_u64_pair"),
        "missing swap_u64_pair concrete caller"
    );
}

/// Vector operations via move-stdlib natives (vectors.mv).
#[test]
fn vectors_module() {
    let asm = fixture_with_dependencies().compile("vectors");
    assert!(asm.contains("sum_vec"), "missing sum_vec");
    assert!(asm.contains("contains"), "missing contains");
    assert!(asm.contains("make_range"), "missing make_range");
}

/// Sui objects with key ability, UID, transfer (objects.mv).
#[test]
fn objects_module() {
    let asm = fixture_with_dependencies().compile("objects");
    assert!(asm.contains("create"), "missing create");
    assert!(asm.contains("increment"), "missing increment");
    assert!(asm.contains("value"), "missing value");
}
