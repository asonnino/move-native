// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! One test per MoveStdlib module. Tests that currently fail are `#[ignore]`d
//! with the error message so we can track compiler progress.

use compiler::module::framework::ModuleFixture;

fn fixture() -> ModuleFixture {
    let base = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/move_samples/sui_framework"
    );
    ModuleFixture::from_dir(format!("{base}/move_stdlib"))
}

#[test]
fn address() {
    fixture().compile("address");
}

#[test]
fn ascii() {
    fixture().compile("ascii");
}

#[test]
fn bcs() {
    fixture().compile("bcs");
}

#[test]
fn bit_vector() {
    fixture().compile("bit_vector");
}

#[test]
fn bool() {
    fixture().compile("bool");
}

#[test]
fn debug() {
    fixture().compile("debug");
}

#[test]
fn fixed_point32() {
    fixture().compile("fixed_point32");
}

#[test]
fn hash() {
    fixture().compile("hash");
}

#[test]
fn internal() {
    fixture().compile("internal");
}

#[test]
fn macros() {
    fixture().compile("macros");
}

#[test]
fn option() {
    fixture().compile("option");
}

#[test]
fn string() {
    fixture().compile("string");
}

#[test]
#[ignore = "expected integer for local, got PointerValue"]
fn type_name() {
    fixture().compile("type_name");
}

#[test]
fn u128() {
    fixture().compile("u128");
}

#[test]
fn u16() {
    fixture().compile("u16");
}

#[test]
fn u256() {
    fixture().compile("u256");
}

#[test]
fn u32() {
    fixture().compile("u32");
}

#[test]
fn u64() {
    fixture().compile("u64");
}

#[test]
fn u8() {
    fixture().compile("u8");
}

#[test]
fn uq32_32() {
    fixture().compile("uq32_32");
}

#[test]
fn uq64_64() {
    fixture().compile("uq64_64");
}

#[test]
fn vector() {
    fixture().compile("vector");
}
