// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! End-to-end ZK proof tests for custom Move modules.
//!
//! Each test compiles a Move module to RISC-V, links it into an SP1-compatible
//! ELF, proves execution with the mock prover, and verifies the proof.

use zero_knowledge::pipeline::CompiledElf;

/// Compile a Move function, prove it with the given inputs, verify the
/// proof, and return the result.
async fn prove_and_verify(module_file: &str, function_name: &str, inputs: &[u64]) -> Option<u64> {
    let path = format!(
        "{}/../../tests/move/custom/{module_file}",
        env!("CARGO_MANIFEST_DIR")
    );
    let compiled = CompiledElf::from_file(path, function_name).unwrap();
    let proof = compiled.prove(inputs, true).await.unwrap();
    proof.verify().await.unwrap();
    proof.return_value
}

#[tokio::test]
async fn prove_add() {
    assert_eq!(prove_and_verify("add.mv", "add", &[2, 3]).await, Some(5));
}

#[tokio::test]
#[ignore = "LLVM emits __multi3 (128-bit multiply) which is not yet provided"]
async fn prove_sum_to() {
    assert_eq!(
        prove_and_verify("control_flow.mv", "sum_to", &[10]).await,
        Some(55)
    );
}

#[tokio::test]
#[ignore = "LLVM emits __multi3 (128-bit multiply) which is not yet provided"]
async fn prove_sum_even() {
    assert_eq!(
        prove_and_verify("control_flow.mv", "sum_even", &[10]).await,
        Some(30)
    );
}

#[tokio::test]
#[ignore = "LLVM emits __multi3 (128-bit multiply) which is not yet provided"]
async fn prove_nested_sum() {
    assert_eq!(
        prove_and_verify("control_flow.mv", "nested_sum", &[3, 4]).await,
        Some(12)
    );
}

#[tokio::test]
async fn prove_mask_low_byte() {
    assert_eq!(
        prove_and_verify("bitmath.mv", "mask_low_byte", &[0xABCD]).await,
        Some(0xCD)
    );
}

#[tokio::test]
#[ignore = "LLVM emits __udivdi3 (compiler-rt) which is not yet provided"]
async fn prove_checked_sub() {
    assert_eq!(
        prove_and_verify("checked_math.mv", "checked_sub", &[10, 3]).await,
        Some(7)
    );
}

#[tokio::test]
#[ignore = "LLVM emits __udivdi3 (compiler-rt) which is not yet provided"]
async fn prove_abs_diff() {
    assert_eq!(
        prove_and_verify("checked_math.mv", "abs_diff", &[3, 10]).await,
        Some(7)
    );
}

#[tokio::test]
async fn prove_identity_u64() {
    assert_eq!(
        prove_and_verify("generics.mv", "identity_u64", &[42]).await,
        Some(42)
    );
}

#[tokio::test]
#[ignore = "stub generator does not support u8 arguments yet"]
async fn prove_set_bit() {
    assert_eq!(
        prove_and_verify("bitmath.mv", "set_bit", &[0, 3]).await,
        Some(8)
    );
}

#[tokio::test]
#[ignore = "stub generator does not support u128 return values yet"]
async fn prove_cast_chain() {
    assert_eq!(
        prove_and_verify("bitmath.mv", "cast_chain", &[42]).await,
        Some(42)
    );
}

#[tokio::test]
#[ignore = "stub generator does not support struct arguments yet"]
async fn prove_geometry_sum_fields() {
    prove_and_verify("geometry.mv", "sum_fields", &[]).await;
}
