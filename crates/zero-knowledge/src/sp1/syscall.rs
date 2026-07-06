// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! The SP1 `ecall` ABI, exposed as intent-named operations.
//!
//! Each public method emits one SP1 syscall; the argument marshalling (which
//! registers carry pointers vs. integers) is hidden behind [`emit_ecall`].
//!
//! [`emit_ecall`]: Sp1Syscall::emit_ecall

use inkwell::types::BasicMetadataTypeEnum;
use inkwell::values::{BasicMetadataValueEnum, IntValue, PointerValue};

use compiler::CompileResult;

use super::ir::Ir;

/// SP1 syscall codes (loaded into register `t0` before `ecall`).
const SYSCALL_HALT: u64 = 0x00;
const SYSCALL_COMMIT: u64 = 0x10;
const SYSCALL_COMMIT_DEFERRED: u64 = 0x1A;
const SYSCALL_SHA_EXTEND: u64 = 0x00_30_01_05;
const SYSCALL_SHA_COMPRESS: u64 = 0x00_01_01_06;

/// Emits SP1 syscalls as `ecall` inline assembly.
pub(crate) struct Sp1Syscall<'a, 'ctx> {
    ir: Ir<'a, 'ctx>,
}

impl<'a, 'ctx> Sp1Syscall<'a, 'ctx> {
    pub(crate) fn new(ir: Ir<'a, 'ctx>) -> Self {
        Self { ir }
    }

    /// Commit the `index`-th public-value digest word.
    pub(crate) fn commit(&self, index: u64, word: IntValue<'ctx>) -> CompileResult<()> {
        let i64 = self.ir.i64_type();
        self.emit_ecall(
            &[i64.into(), i64.into(), i64.into()],
            &[
                self.ir.const_i64(SYSCALL_COMMIT).into(),
                self.ir.const_i64(index).into(),
                word.into(),
            ],
        )
    }

    /// Commit the `index`-th deferred-proof digest word (always zero).
    pub(crate) fn commit_deferred(&self, index: u64) -> CompileResult<()> {
        let i64 = self.ir.i64_type();
        self.emit_ecall(
            &[i64.into(), i64.into(), i64.into()],
            &[
                self.ir.const_i64(SYSCALL_COMMIT_DEFERRED).into(),
                self.ir.const_i64(index).into(),
                self.ir.const_i64(0).into(),
            ],
        )
    }

    /// Halt the guest program with exit code 0.
    pub(crate) fn halt(&self) -> CompileResult<()> {
        let i64 = self.ir.i64_type();
        self.emit_ecall(
            &[i64.into(), i64.into(), i64.into()],
            &[
                self.ir.const_i64(SYSCALL_HALT).into(),
                self.ir.const_i64(0).into(),
                self.ir.const_i64(0).into(),
            ],
        )
    }

    /// Expand the first 16 message-schedule words at `w_ptr` into all 64.
    pub(crate) fn sha_extend(&self, w_ptr: PointerValue<'ctx>) -> CompileResult<()> {
        let (i64, ptr) = (self.ir.i64_type(), self.ir.ptr_type());
        self.emit_ecall(
            &[i64.into(), ptr.into(), i64.into()],
            &[
                self.ir.const_i64(SYSCALL_SHA_EXTEND).into(),
                w_ptr.into(),
                self.ir.const_i64(0).into(),
            ],
        )
    }

    /// Compress the schedule at `w_ptr` into the hash state at `h_ptr`.
    pub(crate) fn sha_compress(
        &self,
        w_ptr: PointerValue<'ctx>,
        h_ptr: PointerValue<'ctx>,
    ) -> CompileResult<()> {
        let (i64, ptr) = (self.ir.i64_type(), self.ir.ptr_type());
        self.emit_ecall(
            &[i64.into(), ptr.into(), ptr.into()],
            &[
                self.ir.const_i64(SYSCALL_SHA_COMPRESS).into(),
                w_ptr.into(),
                h_ptr.into(),
            ],
        )
    }

    /// Emit a single `ecall` with `t0`/`a0`/`a1` bound to `operands`.
    fn emit_ecall(
        &self,
        param_types: &[BasicMetadataTypeEnum<'ctx>],
        operands: &[BasicMetadataValueEnum<'ctx>],
    ) -> CompileResult<()> {
        let context = self.ir.context();
        let fn_ty = context.void_type().fn_type(param_types, false);
        let asm = context.create_inline_asm(
            fn_ty,
            "ecall".to_string(),
            "{t0},{a0},{a1}".to_string(),
            true,
            false,
            None,
            false,
        );
        self.ir
            .builder()
            .build_indirect_call(fn_ty, asm, operands, "")?;
        Ok(())
    }
}
