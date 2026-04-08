// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Tests that compile real Move bytecode (.mv files) through the full pipeline.

use compiler::Target;
use compiler::module::bundle::ModuleBundle;
use rstest::rstest;

fn fixture() -> ModuleBundle {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/move/custom");
    ModuleBundle::from_dir(dir)
}

fn fixture_with_dependencies() -> ModuleBundle {
    let base = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/move");
    ModuleBundle::from_dir(format!("{base}/custom"))
        .with_dependencies_from_dir(format!("{base}/stdlib"))
        .with_dependencies_from_dir(format!("{base}/sui"))
}

/// End-to-end from the checked-in add.mv (two-argument u64 addition).
#[rstest]
#[case::aarch64(Target::Aarch64)]
#[case::riscv64(Target::Riscv64)]
fn add_module_from_mv_file(#[case] target: Target) {
    let asm = fixture().compile_checked("M", &target);
    assert!(
        asm.contains("add") || asm.contains("addi"),
        "assembly should contain an add instruction"
    );
}

/// Nested loops and if/else branches (control_flow.mv).
#[rstest]
#[case::aarch64(Target::Aarch64)]
#[case::riscv64(Target::Riscv64)]
fn control_flow_module_from_mv_file(#[case] target: Target) {
    let asm = fixture().compile_checked("control_flow", &target);
    assert!(
        asm.contains("_mv_0x0_control_flow_sum_to"),
        "missing 0x0_control_flow_sum_to"
    );
    assert!(
        asm.contains("_mv_0x0_control_flow_sum_even"),
        "missing 0x0_control_flow_sum_even"
    );
    assert!(
        asm.contains("_mv_0x0_control_flow_nested_sum"),
        "missing 0x0_control_flow_nested_sum"
    );
}

/// Struct pack/unpack, field borrows, ReadRef, WriteRef, FreezeRef,
/// intra-module calls, arithmetic (geometry.mv).
#[rstest]
#[case::aarch64(Target::Aarch64)]
#[case::riscv64(Target::Riscv64)]
fn geometry_module(#[case] target: Target) {
    let asm = fixture().compile_checked("geometry", &target);
    assert!(
        asm.contains("_mv_0x0_geometry_new_point"),
        "missing 0x0_geometry_new_point"
    );
    assert!(
        asm.contains("_mv_0x0_geometry_sum_fields"),
        "missing 0x0_geometry_sum_fields"
    );
    assert!(
        asm.contains("_mv_0x0_geometry_distance_sq"),
        "missing 0x0_geometry_distance_sq"
    );
    assert!(
        asm.contains("_mv_0x0_geometry_translate"),
        "missing 0x0_geometry_translate"
    );
    assert!(
        asm.contains("_mv_0x0_geometry_midpoint"),
        "missing 0x0_geometry_midpoint"
    );
}

/// Bitwise ops, shifts, and integer width casts (bitmath.mv).
#[rstest]
#[case::aarch64(Target::Aarch64)]
#[case::riscv64(Target::Riscv64)]
fn bitmath_module(#[case] target: Target) {
    let asm = fixture().compile_checked("bitmath", &target);
    assert!(
        asm.contains("_mv_0x0_bitmath_mask_low_byte"),
        "missing 0x0_bitmath_mask_low_byte"
    );
    assert!(
        asm.contains("_mv_0x0_bitmath_set_bit"),
        "missing 0x0_bitmath_set_bit"
    );
    assert!(
        asm.contains("_mv_0x0_bitmath_rotate_left"),
        "missing 0x0_bitmath_rotate_left"
    );
    assert!(
        asm.contains("_mv_0x0_bitmath_cast_chain"),
        "missing 0x0_bitmath_cast_chain"
    );
    assert!(
        asm.contains("_mv_0x0_bitmath_add_u128"),
        "missing 0x0_bitmath_add_u128"
    );
    assert!(
        asm.contains("_mv_0x0_bitmath_xor_swap"),
        "missing 0x0_bitmath_xor_swap"
    );
}

/// Abort, comparisons, multi-return, function chaining (checked_math.mv).
#[rstest]
#[case::aarch64(Target::Aarch64)]
#[case::riscv64(Target::Riscv64)]
fn checked_math_module(#[case] target: Target) {
    let asm = fixture().compile_checked("checked_math", &target);
    assert!(
        asm.contains("_mv_0x0_checked_math_checked_sub"),
        "missing 0x0_checked_math_checked_sub"
    );
    assert!(
        asm.contains("_mv_0x0_checked_math_safe_div"),
        "missing 0x0_checked_math_safe_div"
    );
    assert!(
        asm.contains("_mv_0x0_checked_math_divmod"),
        "missing 0x0_checked_math_divmod"
    );
    assert!(
        asm.contains("_mv_0x0_checked_math_clamp"),
        "missing 0x0_checked_math_clamp"
    );
    assert!(
        asm.contains("_mv_0x0_checked_math_abs_diff"),
        "missing 0x0_checked_math_abs_diff"
    );
}

/// Generic structs + monomorphization via concrete callers (generics.mv).
#[rstest]
#[case::aarch64(Target::Aarch64)]
#[case::riscv64(Target::Riscv64)]
fn generics_module(#[case] target: Target) {
    let asm = fixture().compile_checked("generics", &target);
    assert!(
        asm.contains("_mv_0x0_generics_identity_u64"),
        "missing 0x0_generics_identity_u64 concrete caller"
    );
    assert!(
        asm.contains("_mv_0x0_generics_swap_u64_pair"),
        "missing 0x0_generics_swap_u64_pair concrete caller"
    );
}

/// Vector operations via move-stdlib natives (vectors.mv).
#[rstest]
#[case::aarch64(Target::Aarch64)]
#[case::riscv64(Target::Riscv64)]
fn vectors_module(#[case] target: Target) {
    let asm = fixture_with_dependencies().compile_checked("vectors", &target);
    assert!(
        asm.contains("_mv_0x0_vectors_sum_vec"),
        "missing 0x0_vectors_sum_vec"
    );
    assert!(
        asm.contains("_mv_0x0_vectors_contains"),
        "missing 0x0_vectors_contains"
    );
    assert!(
        asm.contains("_mv_0x0_vectors_make_range"),
        "missing 0x0_vectors_make_range"
    );
}

/// Sui objects with key ability, UID, transfer (objects.mv).
#[rstest]
#[case::aarch64(Target::Aarch64)]
#[case::riscv64(Target::Riscv64)]
fn objects_module(#[case] target: Target) {
    let asm = fixture_with_dependencies().compile_checked("objects", &target);
    assert!(
        asm.contains("_mv_0x0_objects_create"),
        "missing 0x0_objects_create"
    );
    assert!(
        asm.contains("_mv_0x0_objects_increment"),
        "missing 0x0_objects_increment"
    );
    assert!(
        asm.contains("_mv_0x0_objects_value"),
        "missing 0x0_objects_value"
    );
}
