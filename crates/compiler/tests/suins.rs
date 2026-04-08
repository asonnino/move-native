// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Compilation tests for SuiNS (Sui Name Service).
//! Source: https://github.com/MystenLabs/suins-contracts  packages/suins

use compiler::Target;
use compiler::module::bundle::ModuleBundle;
use rstest::rstest;

fn fixture() -> ModuleBundle {
    let base = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/move");
    ModuleBundle::from_dir(format!("{base}/popular/suins"))
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

// `config` is a deprecated stub module — every function body is `{ abort 1337 }`.
// Skipped because compile_checked expects `ret`, which all-abort modules don't produce.

compile_tests! {
    admin,
    auction,
    constants,
    controller,
    core_config,
    domain,
    name_record,
    payment,
    pricing_config,
    registry,
    subdomain_registration,
    suins,
    suins_registration,
    update_image,
}
