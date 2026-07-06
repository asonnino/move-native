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
    ///
    /// The real (CPU) prover enforces `committed_digest == sha256(public_values)`
    /// and `exit_code == 0`, so it genuinely checks the SHA-256 commitment. The
    /// mock prover's verification is a no-op for Core proofs: it validates
    /// neither the digest nor the exit code, so mock proofs only attest that the
    /// program executed and returned a value, not that the commitment is correct.
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

    /// Decode the first `u64` return value from the committed public-values
    /// bytes (little-endian). Returns `None` when the function returns nothing
    /// or fewer than 8 bytes were committed.
    fn decode_return_value(public_values: &[u8], ret_count: usize) -> Option<u64> {
        if ret_count == 0 {
            return None;
        }
        let bytes: [u8; 8] = public_values.get(..8)?.try_into().ok()?;
        Some(u64::from_le_bytes(bytes))
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

        let return_value = Proof::decode_return_value(public_values.as_slice(), ret_count);

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

#[cfg(test)]
mod tests {
    use super::Proof;

    #[test]
    fn decode_return_value_reads_first_le_u64() {
        let pv = 5u64.to_le_bytes();
        assert_eq!(Proof::decode_return_value(&pv, 1), Some(5));
    }

    #[test]
    fn decode_return_value_ignores_bytes_past_the_first_word() {
        let mut pv = 42u64.to_le_bytes().to_vec();
        pv.extend_from_slice(&[0xff; 8]);
        assert_eq!(Proof::decode_return_value(&pv, 1), Some(42));
    }

    #[test]
    fn decode_return_value_none_when_no_return() {
        assert_eq!(Proof::decode_return_value(&5u64.to_le_bytes(), 0), None);
    }

    #[test]
    fn decode_return_value_none_when_too_few_bytes() {
        assert_eq!(Proof::decode_return_value(&[1, 2, 3], 1), None);
        assert_eq!(Proof::decode_return_value(&[], 1), None);
    }
}
