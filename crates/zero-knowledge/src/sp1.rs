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

        let w_ty = ir.i32_type().array_type(64);
        let h_ty = ir.i32_type().array_type(8);
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
            let word = b.build_load(ir.i32_type(), slot, "")?.into_int_value();
            // COMMIT carries the digest word in a 64-bit register; zero-extend.
            let word = b.build_int_z_extend(word, ir.i64_type(), "")?;
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

#[cfg(test)]
mod tests {
    use compiler::{Compiler, Target};
    use inkwell::context::Context;
    use inkwell::values::AnyValue;

    use super::Sp1Commit;

    /// Emit `__sp1_commit_and_halt` over an empty test module and return its
    /// unoptimized LLVM IR text.
    fn commit_ir() -> String {
        let ctx = Context::create();
        let compiler = Compiler::new_for_test(&Target::Riscv64, &ctx).unwrap();
        let ir = std::cell::RefCell::new(String::new());
        compiler
            .inject_function(
                Sp1Commit::SYMBOL,
                Sp1Commit::signature(&ctx),
                |injected, f| {
                    Sp1Commit::new(injected).build(f)?;
                    *ir.borrow_mut() = f.print_to_string().to_string();
                    Ok(())
                },
            )
            .unwrap();
        ir.into_inner()
    }

    #[test]
    fn signature_is_void_ptr_i64() {
        let ctx = Context::create();
        let sig = Sp1Commit::signature(&ctx);
        assert_eq!(sig.get_return_type(), None, "returns void");
        assert_eq!(sig.count_param_types(), 2);
        let params = sig.get_param_types();
        assert!(params[0].is_pointer_type());
        assert!(params[1].into_int_type().get_bit_width() == 64);
    }

    #[test]
    fn emits_the_five_named_blocks() {
        let ir = commit_ir();
        for block in [
            "entry:",
            "empty_pv:",
            "compute_sha:",
            "commit_digest:",
            "deferred:",
        ] {
            assert!(ir.contains(block), "missing basic block `{block}`");
        }
    }

    #[test]
    fn allocates_the_sha_scratch_buffers() {
        let ir = commit_ir();
        assert!(ir.contains("%w = alloca [64 x i32]"));
        assert!(ir.contains("%h = alloca [8 x i32]"));
    }

    #[test]
    fn branches_on_empty_public_values() {
        let ir = commit_ir();
        assert!(ir.contains("icmp eq i64 %1, 0"));
        assert!(ir.contains("br i1 %is_empty, label %empty_pv, label %compute_sha"));
    }

    #[test]
    fn computes_sha_via_the_two_precompiles() {
        let ir = commit_ir();
        // t0 immediates: SHA_EXTEND = 0x300105 = 3145989, SHA_COMPRESS = 0x10106 = 65798.
        assert!(
            ir.contains("(i64 3145989, ptr %w, i64 0)"),
            "SHA_EXTEND ecall"
        );
        assert!(
            ir.contains("(i64 65798, ptr %w, ptr %h)"),
            "SHA_COMPRESS ecall"
        );
    }

    #[test]
    fn commits_eight_digest_words() {
        // 8 COMMIT (t0 = 0x10 = 16) ecalls in commit_digest.
        assert_eq!(commit_ir().matches("(i64 16, i64 ").count(), 8);
    }

    #[test]
    fn commits_eight_deferred_words_then_halts() {
        let ir = commit_ir();
        // 8 COMMIT_DEFERRED (t0 = 0x1a = 26), then 1 HALT (t0 = 0).
        assert_eq!(ir.matches("(i64 26, i64 ").count(), 8);
        assert_eq!(ir.matches("(i64 0, i64 0, i64 0)").count(), 1);
        assert!(ir.contains("unreachable"));
    }

    #[test]
    fn total_ecall_count_is_nineteen() {
        // 2 SHA + 8 COMMIT + 8 COMMIT_DEFERRED + 1 HALT.
        assert_eq!(commit_ir().matches("asm sideeffect \"ecall\"").count(), 19);
    }

    #[test]
    fn ecalls_declare_a_memory_clobber() {
        // The SHA precompiles write guest memory; every ecall must clobber it
        // so LLVM keeps loads/stores ordered across the syscall (issue #10).
        let ir = commit_ir();
        assert!(
            ir.contains("~{memory}"),
            "ecall is missing a ~{{memory}} clobber"
        );
        assert_eq!(
            ir.matches("asm sideeffect \"ecall\"").count(),
            ir.matches("~{memory}").count(),
            "every ecall should carry the clobber",
        );
    }
}
