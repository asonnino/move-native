// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Compilation tests for DeepBook V3 (Central Limit Order Book).
//! Source: https://github.com/MystenLabs/deepbookv3  packages/deepbook

use compiler::Target;
use compiler::module::bundle::ModuleBundle;
use rstest::rstest;

fn fixture() -> ModuleBundle {
    let base = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/move");
    ModuleBundle::from_dir(format!("{base}/popular/deepbook"))
        .with_dependencies_from_dir(format!("{base}/stdlib"))
        .with_dependencies_from_dir(format!("{base}/sui"))
}

macro_rules! compile_tests {
    ($($name:ident),* $(,)?) => {
        $(
            #[rstest]
            #[case::aarch64(Target::Aarch64)]
            #[case::riscv64(Target::Riscv64)]
            fn $name(#[case] target: Target) {
                fixture().compile_checked(stringify!($name), &target);
            }
        )*
    };
}

compile_tests! {
    account,
    balance_manager,
    balances,
    big_vector,
    book,
    constants,
    deep_price,
    ewma,
    fill,
    governance,
    history,
    math,
    order,
    order_info,
    order_query,
    pool,
    registry,
    state,
    trade_params,
    utils,
    vault,
}
