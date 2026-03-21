// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use compiler::module::bundle::ModuleBundle;

fn fixture() -> ModuleBundle {
    let base = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/move");
    ModuleBundle::from_dir(format!("{base}/stdlib"))
}

#[test]
fn address() {
    fixture().compile_checked("address");
}

#[test]
fn ascii() {
    fixture().compile_checked("ascii");
}

#[test]
fn bcs() {
    fixture().compile_checked("bcs");
}

#[test]
fn bit_vector() {
    fixture().compile_checked("bit_vector");
}

#[test]
fn bool() {
    fixture().compile_checked("bool");
}

#[test]
fn debug() {
    fixture().compile_checked("debug");
}

#[test]
fn fixed_point32() {
    fixture().compile_checked("fixed_point32");
}

#[test]
fn hash() {
    fixture().compile_checked("hash");
}

#[test]
fn internal() {
    fixture().compile_checked("internal");
}

#[test]
fn macros() {
    fixture().compile_checked("macros");
}

#[test]
fn option() {
    fixture().compile_checked("option");
}

#[test]
fn string() {
    fixture().compile_checked("string");
}

#[test]
fn type_name() {
    fixture().compile_checked("type_name");
}

#[test]
fn u128() {
    fixture().compile_checked("u128");
}

#[test]
fn u16() {
    fixture().compile_checked("u16");
}

#[test]
fn u256() {
    fixture().compile_checked("u256");
}

#[test]
fn u32() {
    fixture().compile_checked("u32");
}

#[test]
fn u64() {
    fixture().compile_checked("u64");
}

#[test]
fn u8() {
    fixture().compile_checked("u8");
}

#[test]
fn uq32_32() {
    fixture().compile_checked("uq32_32");
}

#[test]
fn uq64_64() {
    fixture().compile_checked("uq64_64");
}

#[test]
fn vector() {
    fixture().compile_checked("vector");
}
