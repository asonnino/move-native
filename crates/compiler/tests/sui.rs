// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! One test per Sui framework module. Tests that currently fail are `#[ignore]`d
//! with the error message so we can track compiler progress.

use compiler::module::framework::ModuleFixture;

fn fixture() -> ModuleFixture {
    let base = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/move_samples/sui_framework"
    );
    ModuleFixture::from_dir(format!("{base}/sui"))
        .with_dependencies_from_dir(format!("{base}/move_stdlib"))
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn accumulator() {
    fixture().compile("accumulator");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn accumulator_metadata() {
    fixture().compile("accumulator_metadata");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn accumulator_settlement() {
    fixture().compile("accumulator_settlement");
}

#[test]
fn address() {
    fixture().compile("address");
}

#[test]
#[ignore = "expected integer for local, got PointerValue"]
fn address_alias() {
    fixture().compile("address_alias");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn authenticator_state() {
    fixture().compile("authenticator_state");
}

#[test]
fn bag() {
    fixture().compile("bag");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn balance() {
    fixture().compile("balance");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn bcs() {
    fixture().compile("bcs");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn bls12381() {
    fixture().compile("bls12381");
}

#[test]
fn borrow() {
    fixture().compile("borrow");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn clock() {
    fixture().compile("clock");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn coin() {
    fixture().compile("coin");
}

#[test]
#[ignore = "panic in stackless_bytecode_generator"]
fn coin_registry() {
    fixture().compile("coin_registry");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn config() {
    fixture().compile("config");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn deny_list() {
    fixture().compile("deny_list");
}

#[test]
fn derived_object() {
    fixture().compile("derived_object");
}

#[test]
#[ignore = "expected integer for local, got PointerValue"]
fn display() {
    fixture().compile("display");
}

#[test]
fn dynamic_field() {
    fixture().compile("dynamic_field");
}

#[test]
fn dynamic_object_field() {
    fixture().compile("dynamic_object_field");
}

#[test]
fn ecdsa_k1() {
    fixture().compile("ecdsa_k1");
}

#[test]
fn ecdsa_r1() {
    fixture().compile("ecdsa_r1");
}

#[test]
fn ecvrf() {
    fixture().compile("ecvrf");
}

#[test]
fn ed25519() {
    fixture().compile("ed25519");
}

#[test]
fn event() {
    fixture().compile("event");
}

#[test]
fn funds_accumulator() {
    fixture().compile("funds_accumulator");
}

#[test]
fn groth16() {
    fixture().compile("groth16");
}

#[test]
#[ignore = "expected integer for local, got PointerValue"]
fn group_ops() {
    fixture().compile("group_ops");
}

#[test]
fn hash() {
    fixture().compile("hash");
}

#[test]
#[ignore = "unsupported constant: ByteArray"]
fn hex() {
    fixture().compile("hex");
}

#[test]
fn hmac() {
    fixture().compile("hmac");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn kiosk() {
    fixture().compile("kiosk");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn kiosk_extension() {
    fixture().compile("kiosk_extension");
}

#[test]
fn linked_table() {
    fixture().compile("linked_table");
}

#[test]
fn math() {
    fixture().compile("math");
}

#[test]
fn nitro_attestation() {
    fixture().compile("nitro_attestation");
}

#[test]
fn object() {
    fixture().compile("object");
}

#[test]
fn object_bag() {
    fixture().compile("object_bag");
}

#[test]
fn object_table() {
    fixture().compile("object_table");
}

#[test]
#[ignore = "expected integer for local, got StructValue"]
fn package() {
    fixture().compile("package");
}

#[test]
#[ignore = "expected integer for local, got PointerValue"]
fn party() {
    fixture().compile("party");
}

#[test]
#[ignore = "expected non-void return from call"]
fn pay() {
    fixture().compile("pay");
}

#[test]
fn poseidon() {
    fixture().compile("poseidon");
}

#[test]
fn priority_queue() {
    fixture().compile("priority_queue");
}

#[test]
fn protocol_config() {
    fixture().compile("protocol_config");
}

#[test]
fn prover() {
    fixture().compile("prover");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn random() {
    fixture().compile("random");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui() {
    fixture().compile("sui");
}

#[test]
fn table() {
    fixture().compile("table");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn table_vec() {
    fixture().compile("table_vec");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn token() {
    fixture().compile("token");
}

#[test]
fn transfer() {
    fixture().compile("transfer");
}

#[test]
#[ignore = "expected integer for local, got StructValue"]
fn transfer_policy() {
    fixture().compile("transfer_policy");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn tx_context() {
    fixture().compile("tx_context");
}

#[test]
fn types() {
    fixture().compile("types");
}

#[test]
fn url() {
    fixture().compile("url");
}

#[test]
fn vdf() {
    fixture().compile("vdf");
}

#[test]
fn vec_map() {
    fixture().compile("vec_map");
}

#[test]
fn vec_set() {
    fixture().compile("vec_set");
}

#[test]
fn versioned() {
    fixture().compile("versioned");
}

#[test]
fn zklogin_verified_id() {
    fixture().compile("zklogin_verified_id");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn zklogin_verified_issuer() {
    fixture().compile("zklogin_verified_issuer");
}
