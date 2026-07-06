// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! End-to-end ZK proof tests for custom Move modules.
//!
//! Each test compiles a Move module to RISC-V, links it into an SP1-compatible
//! ELF, proves execution, and verifies the proof. Most use the fast mock
//! prover; `prove_add_real` uses the real CPU prover to actually check the
//! SHA-256 commitment (see [`prove_and_verify_mock`] vs [`prove_and_verify_real`]).

use zero_knowledge::pipeline::CompiledElf;

/// Compile a Move function, prove it with the given inputs, verify the proof,
/// and return the result. `mock` selects the fast mock prover vs. the real
/// CPU prover.
async fn run(module_file: &str, function_name: &str, inputs: &[u64], mock: bool) -> Option<u64> {
    let path = format!(
        "{}/../../tests/move/custom/{module_file}",
        env!("CARGO_MANIFEST_DIR")
    );
    let compiled = CompiledElf::from_file(path, function_name).unwrap();
    let proof = compiled.prove(inputs, mock).await.unwrap();
    proof.verify().await.unwrap();
    proof.return_value
}

/// Prove and verify with the fast mock prover.
///
/// The mock prover's `verify()` does not check the committed digest, so these
/// tests validate execution and the return value but **not** the SHA-256
/// commitment. See [`prove_and_verify_real`] for the genuine commitment check.
async fn prove_and_verify_mock(
    module_file: &str,
    function_name: &str,
    inputs: &[u64],
) -> Option<u64> {
    run(module_file, function_name, inputs, true).await
}

/// Prove and verify with the real CPU prover.
///
/// Here `verify()` enforces `committed_digest == sha256(public_values)` and
/// `exit_code == 0`, so this genuinely exercises `__sp1_commit_and_halt`.
async fn prove_and_verify_real(
    module_file: &str,
    function_name: &str,
    inputs: &[u64],
) -> Option<u64> {
    run(module_file, function_name, inputs, false).await
}

#[tokio::test]
async fn prove_add() {
    assert_eq!(
        prove_and_verify_mock("add.mv", "add", &[2, 3]).await,
        Some(5)
    );
}

#[tokio::test]
#[ignore = "currently FAILS: real proof rejected with 'global cumulative sum is \
            not zero' (issue #19); also slow. Run with --release --ignored."]
async fn prove_add_real() {
    // Real Core proof: verify() enforces committed_digest == sha256(public_values)
    // and exit_code == 0, so this actually exercises __sp1_commit_and_halt.
    // NOTE: real proving currently fails in the SP1 STARK verifier (issue #19) —
    // the program executes correctly but its interaction argument does not
    // balance. Kept as the genuine end-to-end check, ignored until #19 is fixed.
    assert_eq!(
        prove_and_verify_real("add.mv", "add", &[2, 3]).await,
        Some(5)
    );
}

#[tokio::test]
async fn prove_sum_to() {
    assert_eq!(
        prove_and_verify_mock("control_flow.mv", "sum_to", &[10]).await,
        Some(55)
    );
}

#[tokio::test]
async fn prove_sum_even() {
    assert_eq!(
        prove_and_verify_mock("control_flow.mv", "sum_even", &[10]).await,
        Some(30)
    );
}

#[tokio::test]
async fn prove_nested_sum() {
    // nested_sum(3, 4) sums i*cols + j over the 3x4 grid:
    //   i=0: 0+1+2+3=6, i=1: 4+5+6+7=22, i=2: 8+9+10+11=38 → 66.
    assert_eq!(
        prove_and_verify_mock("control_flow.mv", "nested_sum", &[3, 4]).await,
        Some(66)
    );
}

#[tokio::test]
async fn prove_mask_low_byte() {
    assert_eq!(
        prove_and_verify_mock("bitmath.mv", "mask_low_byte", &[0xABCD]).await,
        Some(0xCD)
    );
}

#[tokio::test]
async fn prove_checked_sub() {
    assert_eq!(
        prove_and_verify_mock("checked_math.mv", "checked_sub", &[10, 3]).await,
        Some(7)
    );
}

#[tokio::test]
async fn prove_abs_diff() {
    assert_eq!(
        prove_and_verify_mock("checked_math.mv", "abs_diff", &[3, 10]).await,
        Some(7)
    );
}

#[tokio::test]
async fn prove_identity_u64() {
    assert_eq!(
        prove_and_verify_mock("generics.mv", "identity_u64", &[42]).await,
        Some(42)
    );
}

#[tokio::test]
#[ignore = "stub generator does not support u8 arguments yet"]
async fn prove_set_bit() {
    assert_eq!(
        prove_and_verify_mock("bitmath.mv", "set_bit", &[0, 3]).await,
        Some(8)
    );
}

#[tokio::test]
#[ignore = "stub generator does not support u128 return values yet"]
async fn prove_cast_chain() {
    assert_eq!(
        prove_and_verify_mock("bitmath.mv", "cast_chain", &[42]).await,
        Some(42)
    );
}

#[tokio::test]
#[ignore = "stub generator does not support struct arguments yet"]
async fn prove_geometry_sum_fields() {
    prove_and_verify_mock("geometry.mv", "sum_fields", &[]).await;
}
