// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Shared codegen handle for the SP1 commitment layers.
//!
//! [`Ir`] wraps the compiler's [`InjectedFn`] facade and adds the few generic
//! LLVM-IR primitives the [`syscall`](super::syscall), [`sha256`](super::sha256)
//! and [`commit`](super::commit) layers are written in terms of. It is `Copy`,
//! so every layer just holds one by value.

use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::types::{ArrayType, IntType, PointerType};
use inkwell::values::{IntValue, PointerValue};

use compiler::{CompileResult, InjectedFn};

#[derive(Clone, Copy)]
pub(crate) struct Ir<'a, 'ctx> {
    injected: &'a InjectedFn<'a, 'ctx>,
}

impl<'a, 'ctx> Ir<'a, 'ctx> {
    pub(crate) fn new(injected: &'a InjectedFn<'a, 'ctx>) -> Self {
        Self { injected }
    }

    /// An unsigned `i64` constant.
    pub(crate) fn const_i64(&self, value: u64) -> IntValue<'ctx> {
        self.injected.i64_type().const_int(value, false)
    }

    /// Pointer to `array[index]` of an aggregate `alloca`.
    pub(crate) fn array_slot(
        &self,
        array_ty: ArrayType<'ctx>,
        ptr: PointerValue<'ctx>,
        index: u64,
    ) -> CompileResult<PointerValue<'ctx>> {
        let zero = self.const_i64(0);
        let idx = self.const_i64(index);
        Ok(unsafe {
            self.builder()
                .build_in_bounds_gep(array_ty, ptr, &[zero, idx], "")?
        })
    }

    /// Store a constant `i64` into `array[index]`.
    pub(crate) fn store_const(
        &self,
        array_ty: ArrayType<'ctx>,
        ptr: PointerValue<'ctx>,
        index: u64,
        value: u64,
    ) -> CompileResult<()> {
        let slot = self.array_slot(array_ty, ptr, index)?;
        self.builder().build_store(slot, self.const_i64(value))?;
        Ok(())
    }

    pub(crate) fn context(&self) -> &'ctx Context {
        self.injected.context()
    }

    pub(crate) fn builder(&self) -> &Builder<'ctx> {
        self.injected.builder()
    }

    pub(crate) fn i8_type(&self) -> IntType<'ctx> {
        self.injected.i8_type()
    }

    pub(crate) fn i64_type(&self) -> IntType<'ctx> {
        self.injected.i64_type()
    }

    pub(crate) fn ptr_type(&self) -> PointerType<'ctx> {
        self.injected.ptr_type()
    }
}
