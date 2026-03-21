// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Compilation tests for DeepBook V3 (Central Limit Order Book).
//! Source: https://github.com/MystenLabs/deepbookv3  packages/deepbook

use compiler::module::bundle::ModuleBundle;

fn fixture() -> ModuleBundle {
    let base = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/move");
    ModuleBundle::from_dir(format!("{base}/popular/deepbook"))
        .with_dependencies_from_dir(format!("{base}/stdlib"))
        .with_dependencies_from_dir(format!("{base}/sui"))
}

#[test]
fn account() {
    fixture().compile_checked("account");
}

#[test]
fn balance_manager() {
    fixture().compile_checked("balance_manager");
}

#[test]
fn balances() {
    fixture().compile_checked("balances");
}

#[test]
fn big_vector() {
    fixture().compile_checked("big_vector");
}

#[test]
fn book() {
    fixture().compile_checked("book");
}

#[test]
fn constants() {
    fixture().compile_checked("constants");
}

#[test]
fn deep_price() {
    fixture().compile_checked("deep_price");
}

#[test]
fn ewma() {
    fixture().compile_checked("ewma");
}

#[test]
fn fill() {
    fixture().compile_checked("fill");
}

#[test]
fn governance() {
    fixture().compile_checked("governance");
}

#[test]
fn history() {
    fixture().compile_checked("history");
}

#[test]
fn math() {
    fixture().compile_checked("math");
}

#[test]
fn order() {
    fixture().compile_checked("order");
}

#[test]
fn order_info() {
    fixture().compile_checked("order_info");
}

#[test]
fn order_query() {
    fixture().compile_checked("order_query");
}

#[test]
fn pool() {
    fixture().compile_checked("pool");
}

#[test]
fn registry() {
    fixture().compile_checked("registry");
}

#[test]
fn state() {
    fixture().compile_checked("state");
}

#[test]
fn trade_params() {
    fixture().compile_checked("trade_params");
}

#[test]
fn utils() {
    fixture().compile_checked("utils");
}

#[test]
fn vault() {
    fixture().compile_checked("vault");
}
