// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Compilation tests for SuiNS (Sui Name Service).
//! Source: https://github.com/MystenLabs/suins-contracts  packages/suins

use compiler::module::bundle::ModuleBundle;

fn fixture() -> ModuleBundle {
    let base = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/move");
    ModuleBundle::from_dir(format!("{base}/popular/suins"))
        .with_dependencies_from_dir(format!("{base}/stdlib"))
        .with_dependencies_from_dir(format!("{base}/sui"))
}

#[test]
fn admin() {
    fixture().compile_checked("admin");
}

#[test]
fn auction() {
    fixture().compile_checked("auction");
}

// `config` is a deprecated stub module — every function body is `{ abort 1337 }`.
// Skipped because our testing framework (compile_checked) expects `ret`, which
// all-abort modules don't produce.

#[test]
fn constants() {
    fixture().compile_checked("constants");
}

#[test]
fn controller() {
    fixture().compile_checked("controller");
}

#[test]
fn core_config() {
    fixture().compile_checked("core_config");
}

#[test]
fn domain() {
    fixture().compile_checked("domain");
}

#[test]
fn name_record() {
    fixture().compile_checked("name_record");
}

#[test]
fn payment() {
    fixture().compile_checked("payment");
}

#[test]
fn pricing_config() {
    fixture().compile_checked("pricing_config");
}

#[test]
fn registry() {
    fixture().compile_checked("registry");
}

#[test]
fn subdomain_registration() {
    fixture().compile_checked("subdomain_registration");
}

#[test]
fn suins() {
    fixture().compile_checked("suins");
}

#[test]
fn suins_registration() {
    fixture().compile_checked("suins_registration");
}

#[test]
fn update_image() {
    fixture().compile_checked("update_image");
}
