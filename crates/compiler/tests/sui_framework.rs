// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! One test per Sui framework module. Tests that currently fail are `#[ignore]`d
//! with the error message so we can track compiler progress.

use compiler::Target;
use move_binary_format::CompiledModule;

struct FrameworkFixture {
    modules: Vec<CompiledModule>,
    address_prefix: Option<&'static str>,
}

impl FrameworkFixture {
    /// Load and deserialize all framework `.mv` files.
    fn load() -> Self {
        let mut modules = Vec::new();
        let base = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../tests/move_samples/sui_framework"
        );
        let directories = [format!("{base}/move_stdlib"), format!("{base}/sui")];
        for directory in &directories {
            for entry in std::fs::read_dir(directory).unwrap() {
                let path = entry.unwrap().path();
                if path.extension().map_or(false, |e| e == "mv") {
                    let bytes = std::fs::read(&path).unwrap();
                    let module = CompiledModule::deserialize_with_defaults(&bytes).unwrap();
                    modules.push(module);
                }
            }
        }
        Self {
            modules,
            address_prefix: None,
        }
    }

    /// Filter by address prefix to disambiguate duplicates
    /// (e.g. "address" exists in both 0x1 and 0x2).
    fn with_address(mut self, prefix: &'static str) -> Self {
        self.address_prefix = Some(prefix);
        self
    }

    /// Find the named module, compile it with all others as deps.
    fn compile(&self, module_name: &str) {
        let target_idx = self
            .modules
            .iter()
            .position(|m| {
                m.self_id().name().as_str() == module_name
                    && self.address_prefix.map_or(true, |p| {
                        m.self_id().address().to_hex_literal().starts_with(p)
                    })
            })
            .unwrap_or_else(|| panic!("module {module_name} not found"));
        let target = &self.modules[target_idx];
        let dependencies: Vec<_> = self
            .modules
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != target_idx)
            .map(|(_, m)| m.clone())
            .collect();
        compiler::compile_module_with_deps(&Target::host(), target, &dependencies)
            .unwrap_or_else(|e| panic!("{module_name} compilation failed: {e}"));
    }
}

// ===================================================================
// MoveStdlib modules (22)
// ===================================================================

#[test]
fn move_stdlib_address() {
    FrameworkFixture::load()
        .with_address("0x1")
        .compile("address");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn move_stdlib_ascii() {
    FrameworkFixture::load().compile("ascii");
}

#[test]
fn move_stdlib_bcs() {
    FrameworkFixture::load().with_address("0x1").compile("bcs");
}

#[test]
fn move_stdlib_bit_vector() {
    FrameworkFixture::load().compile("bit_vector");
}

#[test]
fn move_stdlib_bool() {
    FrameworkFixture::load().compile("bool");
}

#[test]
fn move_stdlib_debug() {
    FrameworkFixture::load().compile("debug");
}

#[test]
fn move_stdlib_fixed_point32() {
    FrameworkFixture::load().compile("fixed_point32");
}

#[test]
fn move_stdlib_hash() {
    FrameworkFixture::load().with_address("0x1").compile("hash");
}

#[test]
fn move_stdlib_internal() {
    FrameworkFixture::load().compile("internal");
}

#[test]
fn move_stdlib_macros() {
    FrameworkFixture::load().compile("macros");
}

#[test]
fn move_stdlib_option() {
    FrameworkFixture::load().compile("option");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn move_stdlib_string() {
    FrameworkFixture::load().compile("string");
}

#[test]
#[ignore = "expected integer for local, got PointerValue"]
fn move_stdlib_type_name() {
    FrameworkFixture::load().compile("type_name");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn move_stdlib_u128() {
    FrameworkFixture::load().compile("u128");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn move_stdlib_u16() {
    FrameworkFixture::load().compile("u16");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn move_stdlib_u256() {
    FrameworkFixture::load().compile("u256");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn move_stdlib_u32() {
    FrameworkFixture::load().compile("u32");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn move_stdlib_u64() {
    FrameworkFixture::load().compile("u64");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn move_stdlib_u8() {
    FrameworkFixture::load().compile("u8");
}

#[test]
fn move_stdlib_uq32_32() {
    FrameworkFixture::load().compile("uq32_32");
}

#[test]
#[ignore = "compiler emitted x23 (reserved for gas metering)"]
fn move_stdlib_uq64_64() {
    FrameworkFixture::load().compile("uq64_64");
}

#[test]
fn move_stdlib_vector() {
    FrameworkFixture::load().compile("vector");
}

// ===================================================================
// Sui framework modules (62)
// ===================================================================

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_accumulator() {
    FrameworkFixture::load().compile("accumulator");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_accumulator_metadata() {
    FrameworkFixture::load().compile("accumulator_metadata");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_accumulator_settlement() {
    FrameworkFixture::load().compile("accumulator_settlement");
}

#[test]
fn sui_address() {
    FrameworkFixture::load()
        .with_address("0x2")
        .compile("address");
}

#[test]
#[ignore = "expected integer for local, got PointerValue"]
fn sui_address_alias() {
    FrameworkFixture::load().compile("address_alias");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_authenticator_state() {
    FrameworkFixture::load().compile("authenticator_state");
}

#[test]
fn sui_bag() {
    FrameworkFixture::load().compile("bag");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_balance() {
    FrameworkFixture::load().compile("balance");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_bcs() {
    FrameworkFixture::load().with_address("0x2").compile("bcs");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_bls12381() {
    FrameworkFixture::load().compile("bls12381");
}

#[test]
fn sui_borrow() {
    FrameworkFixture::load().compile("borrow");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_clock() {
    FrameworkFixture::load().compile("clock");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_coin() {
    FrameworkFixture::load().compile("coin");
}

#[test]
#[ignore = "panic in stackless_bytecode_generator"]
fn sui_coin_registry() {
    FrameworkFixture::load().compile("coin_registry");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_config() {
    FrameworkFixture::load().compile("config");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_deny_list() {
    FrameworkFixture::load().compile("deny_list");
}

#[test]
fn sui_derived_object() {
    FrameworkFixture::load().compile("derived_object");
}

#[test]
#[ignore = "expected integer for local, got PointerValue"]
fn sui_display() {
    FrameworkFixture::load().compile("display");
}

#[test]
fn sui_dynamic_field() {
    FrameworkFixture::load().compile("dynamic_field");
}

#[test]
fn sui_dynamic_object_field() {
    FrameworkFixture::load().compile("dynamic_object_field");
}

#[test]
fn sui_ecdsa_k1() {
    FrameworkFixture::load().compile("ecdsa_k1");
}

#[test]
fn sui_ecdsa_r1() {
    FrameworkFixture::load().compile("ecdsa_r1");
}

#[test]
fn sui_ecvrf() {
    FrameworkFixture::load().compile("ecvrf");
}

#[test]
fn sui_ed25519() {
    FrameworkFixture::load().compile("ed25519");
}

#[test]
fn sui_event() {
    FrameworkFixture::load().compile("event");
}

#[test]
#[ignore = "compiler emitted x23 (reserved for gas metering)"]
fn sui_funds_accumulator() {
    FrameworkFixture::load().compile("funds_accumulator");
}

#[test]
fn sui_growth16() {
    FrameworkFixture::load().compile("growth16");
}

#[test]
#[ignore = "expected integer for local, got PointerValue"]
fn sui_group_ops() {
    FrameworkFixture::load().compile("group_ops");
}

#[test]
fn sui_hash() {
    FrameworkFixture::load().with_address("0x2").compile("hash");
}

#[test]
#[ignore = "unsupported constant: ByteArray"]
fn sui_hex() {
    FrameworkFixture::load().compile("hex");
}

#[test]
fn sui_hmac() {
    FrameworkFixture::load().compile("hmac");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_kiosk() {
    FrameworkFixture::load().compile("kiosk");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_kiosk_extension() {
    FrameworkFixture::load().compile("kiosk_extension");
}

#[test]
fn sui_linked_table() {
    FrameworkFixture::load().compile("linked_table");
}

#[test]
fn sui_math() {
    FrameworkFixture::load().compile("math");
}

#[test]
fn sui_nitro_attestation() {
    FrameworkFixture::load().compile("nitro_attestation");
}

#[test]
fn sui_object() {
    FrameworkFixture::load().compile("object");
}

#[test]
fn sui_object_bag() {
    FrameworkFixture::load().compile("object_bag");
}

#[test]
fn sui_object_table() {
    FrameworkFixture::load().compile("object_table");
}

#[test]
#[ignore = "expected integer for local, got StructValue"]
fn sui_package() {
    FrameworkFixture::load().compile("package");
}

#[test]
#[ignore = "expected integer for local, got PointerValue"]
fn sui_party() {
    FrameworkFixture::load().compile("party");
}

#[test]
#[ignore = "expected non-void return from call"]
fn sui_pay() {
    FrameworkFixture::load().compile("pay");
}

#[test]
#[ignore = "compiler emitted x23 (reserved for gas metering)"]
fn sui_poseidon() {
    FrameworkFixture::load().compile("poseidon");
}

#[test]
fn sui_priority_queue() {
    FrameworkFixture::load().compile("priority_queue");
}

#[test]
fn sui_protocol_config() {
    FrameworkFixture::load().compile("protocol_config");
}

#[test]
fn sui_prover() {
    FrameworkFixture::load().compile("prover");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_random() {
    FrameworkFixture::load().compile("random");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_sui() {
    FrameworkFixture::load().compile("sui");
}

#[test]
fn sui_table() {
    FrameworkFixture::load().compile("table");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_table_vec() {
    FrameworkFixture::load().compile("table_vec");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_token() {
    FrameworkFixture::load().compile("token");
}

#[test]
fn sui_transfer() {
    FrameworkFixture::load().compile("transfer");
}

#[test]
#[ignore = "expected integer for local, got StructValue"]
fn sui_transfer_policy() {
    FrameworkFixture::load().compile("transfer_policy");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_tx_context() {
    FrameworkFixture::load().compile("tx_context");
}

#[test]
fn sui_types() {
    FrameworkFixture::load().compile("types");
}

#[test]
fn sui_url() {
    FrameworkFixture::load().compile("url");
}

#[test]
fn sui_vdf() {
    FrameworkFixture::load().compile("vdf");
}

#[test]
fn sui_vec_map() {
    FrameworkFixture::load().compile("vec_map");
}

#[test]
fn sui_vec_set() {
    FrameworkFixture::load().compile("vec_set");
}

#[test]
fn sui_versioned() {
    FrameworkFixture::load().compile("versioned");
}

#[test]
fn sui_zklogin_verified_id() {
    FrameworkFixture::load().compile("zklogin_verified_id");
}

#[test]
#[ignore = "unresolved TypeParameter(0)"]
fn sui_zklogin_verified_issuer() {
    FrameworkFixture::load().compile("zklogin_verified_issuer");
}
