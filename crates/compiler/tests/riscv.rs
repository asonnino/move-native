// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Compile Move contracts to RISC-V 64-bit assembly.

use compiler::Target;
use compiler::module::bundle::ModuleBundle;

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

static RISCV: Target = Target::Riscv64;

#[test]
fn add_module() {
    let asm = fixture().compile_checked_for_target("M", &RISCV);
    assert!(
        asm.contains("add") || asm.contains("addi"),
        "assembly should contain an add instruction"
    );
}

#[test]
fn control_flow_module() {
    let asm = fixture().compile_checked_for_target("control_flow", &RISCV);
    assert!(
        asm.contains("_mv_0x0_control_flow_sum_to"),
        "missing 0x0_control_flow_sum_to"
    );
}

#[test]
fn geometry_module() {
    let asm = fixture().compile_checked_for_target("geometry", &RISCV);
    assert!(
        asm.contains("_mv_0x0_geometry_new_point"),
        "missing 0x0_geometry_new_point"
    );
}

#[test]
fn bitmath_module() {
    let asm = fixture().compile_checked_for_target("bitmath", &RISCV);
    assert!(
        asm.contains("_mv_0x0_bitmath_mask_low_byte"),
        "missing 0x0_bitmath_mask_low_byte"
    );
}

#[test]
fn checked_math_module() {
    let asm = fixture().compile_checked_for_target("checked_math", &RISCV);
    assert!(
        asm.contains("_mv_0x0_checked_math_checked_sub"),
        "missing 0x0_checked_math_checked_sub"
    );
}

#[test]
fn generics_module() {
    let asm = fixture().compile_checked_for_target("generics", &RISCV);
    assert!(
        asm.contains("_mv_0x0_generics_identity_u64"),
        "missing 0x0_generics_identity_u64"
    );
}

#[test]
fn vectors_module() {
    let asm = fixture_with_dependencies().compile_checked_for_target("vectors", &RISCV);
    assert!(
        asm.contains("_mv_0x0_vectors_sum_vec"),
        "missing 0x0_vectors_sum_vec"
    );
}

#[test]
fn objects_module() {
    let asm = fixture_with_dependencies().compile_checked_for_target("objects", &RISCV);
    assert!(
        asm.contains("_mv_0x0_objects_create"),
        "missing 0x0_objects_create"
    );
}
