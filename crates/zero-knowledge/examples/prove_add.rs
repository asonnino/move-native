// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Prove a simple Move addition function and verify the proof.
//!
//! Usage:
//!   cargo run --release --example prove_add

use zero_knowledge::pipeline::CompiledElf;

#[tokio::main]
async fn main() {
    let path = concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/move/custom/add.mv"
    );

    let compiled = CompiledElf::from_file(path, "add").unwrap();
    println!("ELF: {} bytes", compiled.elf_bytes.len());

    println!("Proving add(2, 3)...");
    let proof = compiled.prove(&[2, 3], false).await.unwrap();
    println!("Cycles: {}", proof.cycles);
    println!("Result: {:?}", proof.return_value);

    proof.verify().await.unwrap();
    println!("Proof verified!");
}
