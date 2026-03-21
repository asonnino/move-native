// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use compiler::module::bundle::ModuleBundle;

fn fixture() -> ModuleBundle {
    let base = concat!(env!("CARGO_MANIFEST_DIR"), "/../../tests/move");
    ModuleBundle::from_dir(format!("{base}/sui"))
        .with_dependencies_from_dir(format!("{base}/stdlib"))
}

#[test]
fn accumulator() {
    fixture().compile_checked("accumulator");
}

#[test]
fn accumulator_metadata() {
    fixture().compile_checked("accumulator_metadata");
}

#[test]
fn accumulator_settlement() {
    fixture().compile_checked("accumulator_settlement");
}

#[test]
fn address() {
    fixture().compile_checked("address");
}

#[test]
fn address_alias() {
    fixture().compile_checked("address_alias");
}

#[test]
fn authenticator_state() {
    fixture().compile_checked("authenticator_state");
}

#[test]
fn bag() {
    fixture().compile_checked("bag");
}

#[test]
fn balance() {
    fixture().compile_checked("balance");
}

#[test]
fn bcs() {
    fixture().compile_checked("bcs");
}

#[test]
fn bls12381() {
    fixture().compile_checked("bls12381");
}

#[test]
fn borrow() {
    fixture().compile_checked("borrow");
}

#[test]
fn clock() {
    fixture().compile_checked("clock");
}

#[test]
fn coin() {
    fixture().compile_checked("coin");
}

#[test]
fn coin_registry() {
    fixture().compile_checked("coin_registry");
}

#[test]
fn config() {
    fixture().compile_checked("config");
}

#[test]
fn deny_list() {
    fixture().compile_checked("deny_list");
}

#[test]
fn derived_object() {
    fixture().compile_checked("derived_object");
}

#[test]
fn display() {
    fixture().compile_checked("display");
}

#[test]
fn dynamic_field() {
    fixture().compile_checked("dynamic_field");
}

#[test]
fn dynamic_object_field() {
    fixture().compile_checked("dynamic_object_field");
}

#[test]
fn ecdsa_k1() {
    fixture().compile_checked("ecdsa_k1");
}

#[test]
fn ecdsa_r1() {
    fixture().compile_checked("ecdsa_r1");
}

#[test]
fn ecvrf() {
    fixture().compile_checked("ecvrf");
}

#[test]
fn ed25519() {
    fixture().compile_checked("ed25519");
}

#[test]
fn event() {
    fixture().compile_checked("event");
}

#[test]
fn funds_accumulator() {
    fixture().compile_checked("funds_accumulator");
}

#[test]
fn groth16() {
    fixture().compile_checked("groth16");
}

#[test]
fn group_ops() {
    fixture().compile_checked("group_ops");
}

#[test]
fn hash() {
    fixture().compile_checked("hash");
}

#[test]
fn hex() {
    fixture().compile_checked("hex");
}

#[test]
fn hmac() {
    fixture().compile_checked("hmac");
}

#[test]
fn kiosk() {
    fixture().compile_checked("kiosk");
}

#[test]
fn kiosk_extension() {
    fixture().compile_checked("kiosk_extension");
}

#[test]
fn linked_table() {
    fixture().compile_checked("linked_table");
}

#[test]
fn math() {
    fixture().compile_checked("math");
}

#[test]
fn nitro_attestation() {
    fixture().compile_checked("nitro_attestation");
}

#[test]
fn object() {
    fixture().compile_checked("object");
}

#[test]
fn object_bag() {
    fixture().compile_checked("object_bag");
}

#[test]
fn object_table() {
    fixture().compile_checked("object_table");
}

#[test]
fn package() {
    fixture().compile_checked("package");
}

#[test]
fn party() {
    fixture().compile_checked("party");
}

#[test]
fn pay() {
    fixture().compile_checked("pay");
}

#[test]
fn poseidon() {
    fixture().compile_checked("poseidon");
}

#[test]
fn priority_queue() {
    fixture().compile_checked("priority_queue");
}

#[test]
fn protocol_config() {
    fixture().compile_checked("protocol_config");
}

#[test]
fn prover() {
    fixture().compile_checked("prover");
}

#[test]
fn random() {
    fixture().compile_checked("random");
}

#[test]
fn sui() {
    fixture().compile_checked("sui");
}

#[test]
fn table() {
    fixture().compile_checked("table");
}

#[test]
fn table_vec() {
    fixture().compile_checked("table_vec");
}

#[test]
fn token() {
    fixture().compile_checked("token");
}

#[test]
fn transfer() {
    fixture().compile_checked("transfer");
}

#[test]
fn transfer_policy() {
    fixture().compile_checked("transfer_policy");
}

#[test]
fn tx_context() {
    fixture().compile_checked("tx_context");
}

#[test]
fn types() {
    fixture().compile_checked("types");
}

#[test]
fn url() {
    fixture().compile_checked("url");
}

#[test]
fn vdf() {
    fixture().compile_checked("vdf");
}

#[test]
fn vec_map() {
    fixture().compile_checked("vec_map");
}

#[test]
fn vec_set() {
    fixture().compile_checked("vec_set");
}

#[test]
fn versioned() {
    fixture().compile_checked("versioned");
}

#[test]
fn zklogin_verified_id() {
    fixture().compile_checked("zklogin_verified_id");
}

#[test]
fn zklogin_verified_issuer() {
    fixture().compile_checked("zklogin_verified_issuer");
}
