// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! SHA-256 of the public values, computed with SP1's SHA precompiles.

use inkwell::types::ArrayType;
use inkwell::values::{IntValue, PointerValue};

use compiler::CompileResult;

use super::ir::Ir;
use super::syscall::Sp1Syscall;

/// SHA-256 initial hash values (FIPS 180-4, section 5.3.3).
const SHA256_H: [u32; 8] = [
    0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
];

/// SHA-256("") digest, byte-swapped for SP1's COMMIT convention.
///
/// The verifier decomposes each committed u32 in LE byte order, so we pre-swap
/// each word of the standard SHA-256("") digest.
const SHA256_EMPTY_SWAPPED: [u32; 8] = [
    0x42c4b0e3, 0x141cfc98, 0xc8f4fb9a, 0x24b96f99, 0xe441ae27, 0x4c939b64, 0x1b9995a4, 0x55b85278,
];

/// Emits SHA-256 of the public values into the hash-state buffer `h`.
pub(crate) struct Sha256<'a, 'ctx> {
    ir: Ir<'a, 'ctx>,
}

impl<'a, 'ctx> Sha256<'a, 'ctx> {
    pub(crate) fn new(ir: Ir<'a, 'ctx>) -> Self {
        Self { ir }
    }

    /// Store the precomputed SHA-256("") digest into `h`, for the empty
    /// public-values case.
    pub(crate) fn store_empty_digest(
        &self,
        h_ptr: PointerValue<'ctx>,
        h_ty: ArrayType<'ctx>,
    ) -> CompileResult<()> {
        for (i, word) in SHA256_EMPTY_SWAPPED.iter().enumerate() {
            self.ir.store_const(h_ty, h_ptr, i as u64, *word as u64)?;
        }
        Ok(())
    }

    /// Hash the single-block, 8-byte message at `pv_ptr` (using `w` as the
    /// message-schedule scratch) and leave the byte-swapped digest in `h`.
    pub(crate) fn digest(
        &self,
        pv_ptr: PointerValue<'ctx>,
        w_ptr: PointerValue<'ctx>,
        w_ty: ArrayType<'ctx>,
        h_ptr: PointerValue<'ctx>,
        h_ty: ArrayType<'ctx>,
    ) -> CompileResult<()> {
        let b = self.ir.builder();

        // The two big-endian message words.
        for i in 0..2u64 {
            let word = self.load_be_u32(pv_ptr, i * 4)?;
            let slot = self.ir.array_slot(w_ty, w_ptr, i)?;
            b.build_store(slot, word)?;
        }

        // Padding: the 0x80 terminator, zeros, then the 64-bit message length.
        self.ir.store_const(w_ty, w_ptr, 2, 0x8000_0000)?;
        for i in 3..15u64 {
            self.ir.store_const(w_ty, w_ptr, i, 0)?;
        }
        self.ir.store_const(w_ty, w_ptr, 15, 64)?;

        // Seed the hash state with the SHA-256 initial constants.
        for (i, value) in SHA256_H.iter().enumerate() {
            self.ir.store_const(h_ty, h_ptr, i as u64, *value as u64)?;
        }

        // Expand the schedule and compress it into the hash state.
        let syscall = Sp1Syscall::new(self.ir);
        syscall.sha_extend(w_ptr)?;
        syscall.sha_compress(w_ptr, h_ptr)?;

        // Byte-swap each digest word for the COMMIT convention.
        for i in 0..8u64 {
            let slot = self.ir.array_slot(h_ty, h_ptr, i)?;
            let word = b.build_load(self.ir.i64_type(), slot, "")?.into_int_value();
            let swapped = self.bswap32(word)?;
            b.build_store(slot, swapped)?;
        }

        Ok(())
    }

    /// Load 4 little-endian bytes at `base + byte_offset`, packed big-endian
    /// into an `i64` (the canonical SHA-256 word packing).
    fn load_be_u32(
        &self,
        base: PointerValue<'ctx>,
        byte_offset: u64,
    ) -> CompileResult<IntValue<'ctx>> {
        let b = self.ir.builder();
        let mut result = self.ir.const_i64(0);

        for byte_idx in 0..4u64 {
            let gep = unsafe {
                b.build_gep(
                    self.ir.i8_type(),
                    base,
                    &[self.ir.const_i64(byte_offset + byte_idx)],
                    "",
                )?
            };
            let byte = b.build_load(self.ir.i8_type(), gep, "")?.into_int_value();
            let extended = b.build_int_z_extend(byte, self.ir.i64_type(), "")?;
            let shift = self.ir.const_i64((3 - byte_idx) * 8);
            let shifted = b.build_left_shift(extended, shift, "")?;
            result = b.build_or(result, shifted, "")?;
        }

        Ok(result)
    }

    /// Byte-swap the low 32 bits of an `i64` (big-endian digest to the
    /// little-endian words COMMIT expects).
    fn bswap32(&self, value: IntValue<'ctx>) -> CompileResult<IntValue<'ctx>> {
        let b = self.ir.builder();
        let mask = self.ir.const_i64(0xff);

        let b0 = b.build_and(value, mask, "")?;
        let b1 = b.build_and(
            b.build_right_shift(value, self.ir.const_i64(8), false, "")?,
            mask,
            "",
        )?;
        let b2 = b.build_and(
            b.build_right_shift(value, self.ir.const_i64(16), false, "")?,
            mask,
            "",
        )?;
        let b3 = b.build_right_shift(value, self.ir.const_i64(24), false, "")?;

        let r = b.build_left_shift(b0, self.ir.const_i64(24), "")?;
        let r = b.build_or(r, b.build_left_shift(b1, self.ir.const_i64(16), "")?, "")?;
        let r = b.build_or(r, b.build_left_shift(b2, self.ir.const_i64(8), "")?, "")?;
        Ok(b.build_or(r, b3, "")?)
    }
}
