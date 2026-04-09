// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! SP1 proof generation and verification for compiled Move programs.

use sp1_sdk::{
    Prover as Sp1Prover, ProverClient, ProvingKey as _, SP1ProofWithPublicValues, SP1Stdin,
};

use crate::error::{ZkError, ZkResult};

/// A proven execution: holds the proof, verifying key, and execution metadata.
pub struct Proof {
    pub proof: SP1ProofWithPublicValues,
    pub verifying_key: sp1_sdk::SP1VerifyingKey,
    /// Number of VM cycles consumed during execution.
    pub cycles: u64,
    /// Return value (first u64), if the function returns one.
    pub return_value: Option<u64>,
    mock: bool,
}

impl Proof {
    /// Verify this proof.
    pub async fn verify(&self) -> ZkResult<()> {
        if self.mock {
            let client = ProverClient::builder().mock().build().await;
            self.verify_with(&client)
        } else {
            let client = ProverClient::builder().cpu().build().await;
            self.verify_with(&client)
        }
    }

    fn verify_with(&self, client: &impl Sp1Prover) -> ZkResult<()> {
        client
            .verify(&self.proof, &self.verifying_key, None)
            .map_err(|e| ZkError::Sp1(e.to_string()))
    }
}

/// Generates ZK proofs of Move program execution via SP1.
pub struct Prover<P> {
    client: P,
    mock: bool,
}

impl Prover<()> {
    /// Create a prover using the mock backend (fast, no real proof).
    pub async fn mock() -> Prover<impl Sp1Prover> {
        Prover {
            client: ProverClient::builder().mock().build().await,
            mock: true,
        }
    }

    /// Create a prover using the CPU backend (real proof).
    pub async fn cpu() -> Prover<impl Sp1Prover> {
        Prover {
            client: ProverClient::builder().cpu().build().await,
            mock: false,
        }
    }
}

impl<P: Sp1Prover> Prover<P> {
    /// Execute the program and generate a proof.
    pub async fn prove(
        &self,
        elf: sp1_sdk::Elf,
        stdin: SP1Stdin,
        ret_count: usize,
    ) -> ZkResult<Proof> {
        let (public_values, report) = self
            .client
            .execute(elf.clone(), stdin.clone())
            .await
            .map_err(|e| ZkError::Sp1(e.to_string()))?;

        let cycles = report.total_instruction_count();

        let return_value = if ret_count > 0 {
            let bytes = public_values.as_slice();
            if bytes.len() >= 8 {
                Some(u64::from_le_bytes(bytes[..8].try_into().unwrap()))
            } else {
                None
            }
        } else {
            None
        };

        let proving_key = self
            .client
            .setup(elf)
            .await
            .map_err(|e| ZkError::Sp1(format!("{e}")))?;

        let proof = self
            .client
            .prove(&proving_key, stdin)
            .await
            .map_err(|e| ZkError::Sp1(format!("{e}")))?;

        Ok(Proof {
            proof,
            verifying_key: proving_key.verifying_key().clone(),
            cycles,
            return_value,
            mock: self.mock,
        })
    }
}
