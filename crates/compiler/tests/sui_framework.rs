// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use compiler::Target;
use compiler::module::bundle::ModuleBundle;
use rstest::rstest;

fn fixture() -> ModuleBundle {
    let base = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/move");
    ModuleBundle::from_dir(format!("{base}/sui"))
        .with_dependencies_from_dir(format!("{base}/stdlib"))
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
    accumulator,
    accumulator_metadata,
    accumulator_settlement,
    address,
    address_alias,
    authenticator_state,
    bag,
    balance,
    bcs,
    bls12381,
    borrow,
    clock,
    coin,
    config,
    deny_list,
    derived_object,
    display,
    dynamic_field,
    dynamic_object_field,
    ecdsa_k1,
    ecdsa_r1,
    ecvrf,
    ed25519,
    event,
    funds_accumulator,
    groth16,
    group_ops,
    hash,
    hex,
    hmac,
    kiosk,
    kiosk_extension,
    linked_table,
    math,
    nitro_attestation,
    object,
    object_bag,
    object_table,
    package,
    party,
    pay,
    poseidon,
    priority_queue,
    protocol_config,
    prover,
    random,
    sui,
    table,
    table_vec,
    token,
    transfer,
    transfer_policy,
    tx_context,
    types,
    url,
    vdf,
    vec_map,
    vec_set,
    versioned,
    zklogin_verified_id,
    zklogin_verified_issuer,
}

// `coin_registry` pattern-matches on an enum, which lowers to a `VariantSwitch`
// that panics in the pinned Sui move-stackless-bytecode (see #21).
#[rstest]
#[case::aarch64(Target::Aarch64)]
#[case::riscv64(Target::Riscv64)]
#[ignore = "upstream Sui move-stackless-bytecode panics lowering VariantSwitch; see #21"]
fn coin_registry(#[case] target: Target) {
    fixture().compile_checked("coin_registry", &target);
}
