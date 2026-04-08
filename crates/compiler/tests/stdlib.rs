// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use compiler::Target;
use compiler::module::bundle::ModuleBundle;
use rstest::rstest;

fn fixture() -> ModuleBundle {
    let base = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/move");
    ModuleBundle::from_dir(format!("{base}/stdlib"))
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
    address,
    ascii,
    bcs,
    bit_vector,
    bool,
    debug,
    fixed_point32,
    hash,
    internal,
    macros,
    option,
    string,
    type_name,
    u128,
    u16,
    u256,
    u32,
    u64,
    u8,
    uq32_32,
    uq64_64,
    vector,
}
