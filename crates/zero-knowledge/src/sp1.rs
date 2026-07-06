// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! The `__sp1_commit_and_halt` function: hash the public values, commit the
//! digest, and halt.
//!
//! SP1's verifier requires the guest to commit a SHA-256 digest of its public
//! values before halting. Emitting this as LLVM IR (rather than hand-written
//! assembly) lets the entry stub simply `call __sp1_commit_and_halt`.

mod ir;
mod sha256;
mod syscall;

use inkwell::context::Context;
use inkwell::types::FunctionType;
use inkwell::values::FunctionValue;
use inkwell::{AddressSpace, IntPredicate};

use compiler::{CompileResult, InjectedFn};

use self::ir::Ir;
use self::sha256::Sha256;
use self::syscall::Sp1Syscall;

/// Builds the `__sp1_commit_and_halt` function as LLVM IR.
pub(crate) struct Sp1Commit<'a, 'ctx> {
    ir: Ir<'a, 'ctx>,
}

impl<'a, 'ctx> Sp1Commit<'a, 'ctx> {
    /// Linker symbol name of the emitted commitment function. The single
    /// source of truth shared with the assembly stub (via `InjectedSymbol`).
    pub(crate) const SYMBOL: &'static str = "__sp1_commit_and_halt";

    pub(crate) fn new(injected: &'a InjectedFn<'a, 'ctx>) -> Self {
        Self {
            ir: Ir::new(injected),
        }
    }

    /// Signature of `__sp1_commit_and_halt`: `void(pv_ptr: *u8, pv_len: i64)`.
    pub(crate) fn signature(context: &'ctx Context) -> FunctionType<'ctx> {
        let ptr_ty = context.ptr_type(AddressSpace::default());
        let i64_ty = context.i64_type();
        context
            .void_type()
            .fn_type(&[ptr_ty.into(), i64_ty.into()], false)
    }

    /// Emit the function body into `function`.
    ///
    /// If `pv_len == 0`, commits the precomputed SHA-256("") digest; otherwise
    /// hashes the bytes at `pv_ptr` (single block, up to 55 bytes). Always
    /// commits 8 zero words for deferred proofs, then halts.
    pub(crate) fn build(&self, function: FunctionValue<'ctx>) -> CompileResult<()> {
        let ir = self.ir;
        let b = ir.builder();

        let entry = ir.context().append_basic_block(function, "entry");
        let empty_pv = ir.context().append_basic_block(function, "empty_pv");
        let compute_sha = ir.context().append_basic_block(function, "compute_sha");
        let commit_digest = ir.context().append_basic_block(function, "commit_digest");
        let deferred = ir.context().append_basic_block(function, "deferred");

        let w_ty = ir.i64_type().array_type(64);
        let h_ty = ir.i64_type().array_type(8);
        let sha = Sha256::new(ir);
        let syscall = Sp1Syscall::new(ir);

        // Allocate the SHA-256 scratch buffers and dispatch on whether there
        // are any public values to hash.
        b.position_at_end(entry);
        let pv_ptr = function.get_nth_param(0).unwrap().into_pointer_value();
        let pv_len = function.get_nth_param(1).unwrap().into_int_value();
        let w_ptr = b.build_alloca(w_ty, "w")?;
        let h_ptr = b.build_alloca(h_ty, "h")?;
        let is_empty =
            b.build_int_compare(IntPredicate::EQ, pv_len, ir.const_i64(0), "is_empty")?;
        b.build_conditional_branch(is_empty, empty_pv, compute_sha)?;

        // With no public values, the digest is the precomputed SHA-256("").
        b.position_at_end(empty_pv);
        sha.store_empty_digest(h_ptr, h_ty)?;
        b.build_unconditional_branch(commit_digest)?;

        // Otherwise hash the public values into `h`, byte-swapped for COMMIT.
        b.position_at_end(compute_sha);
        sha.digest(pv_ptr, w_ptr, w_ty, h_ptr, h_ty)?;
        b.build_unconditional_branch(commit_digest)?;

        // Commit the eight digest words.
        b.position_at_end(commit_digest);
        for i in 0..8u64 {
            let slot = ir.array_slot(h_ty, h_ptr, i)?;
            let word = b.build_load(ir.i64_type(), slot, "")?.into_int_value();
            syscall.commit(i, word)?;
        }
        b.build_unconditional_branch(deferred)?;

        // Commit the (all-zero) deferred-proof digest, then halt.
        b.position_at_end(deferred);
        for i in 0..8u64 {
            syscall.commit_deferred(i)?;
        }
        syscall.halt()?;
        b.build_unreachable()?;

        Ok(())
    }
}
