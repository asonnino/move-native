// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Auxiliary-function injection.
//!
//! [`Compiler::inject_function`](crate::Compiler::inject_function) splices an
//! extra, hand-written function into the module being compiled, at the LLVM-IR
//! level. It is the IR-level counterpart to
//! [`Compiler::set_module_assembly`](crate::Compiler::set_module_assembly),
//! which injects raw assembly. Both let a caller add support routines (e.g. an
//! entry harness or an SP1 commitment) alongside the functions lowered from
//! Move bytecode.
//!
//! The caller's build closure receives an [`InjectedFn`] facade — scoped access
//! to the context, builder, and cached integer/pointer types — rather than the
//! compiler's private module, and the call returns a typed [`InjectedSymbol`]
//! that downstream code (assembly stubs) can reference by name.

use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::types::{IntType, PointerType};

use crate::context::LlvmContext;

/// A function injected into the module on a caller's behalf.
///
/// Threaded to assembly stubs so the definition site and the call site share
/// one typed handle instead of a duplicated string literal.
#[derive(Debug, Clone)]
pub struct InjectedSymbol {
    /// The linker symbol name of the injected function.
    pub name: String,
}

/// Scoped facade for building a single injected function's body.
///
/// Hands out controlled access to the IR context, builder, and cached types —
/// but never the module itself, so callers cannot mutate the compiler's
/// function list except through the [`FunctionValue`](inkwell::values::FunctionValue)
/// they are given.
pub struct InjectedFn<'a, 'ctx> {
    ctx: &'a LlvmContext<'ctx>,
}

impl<'a, 'ctx> InjectedFn<'a, 'ctx> {
    pub(crate) fn new(ctx: &'a LlvmContext<'ctx>) -> Self {
        Self { ctx }
    }

    /// The LLVM context, for appending basic blocks and creating inline asm.
    pub fn context(&self) -> &'ctx Context {
        self.ctx.context
    }

    /// The IR builder for emitting instructions.
    pub fn builder(&self) -> &Builder<'ctx> {
        self.ctx.builder()
    }

    /// Cached `i8` type.
    pub fn i8_type(&self) -> IntType<'ctx> {
        self.ctx.i8_type
    }

    /// Cached `i64` type.
    pub fn i64_type(&self) -> IntType<'ctx> {
        self.ctx.i64_type
    }

    /// Cached opaque pointer type.
    pub fn ptr_type(&self) -> PointerType<'ctx> {
        self.ctx.ptr_type
    }
}
