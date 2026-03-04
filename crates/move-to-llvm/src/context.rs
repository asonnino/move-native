// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::AddressSpace;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{FunctionType, IntType, PointerType};
use inkwell::values::FunctionValue;

/// Wraps the LLVM Context, Module, and Builder for a single compilation unit.
pub(crate) struct LlvmContext<'ctx> {
    pub(crate) context: &'ctx Context,
    pub(crate) module: Module<'ctx>,
    pub(crate) builder: Builder<'ctx>,
    // Cached integer types
    pub(crate) i8_type: IntType<'ctx>,
    pub(crate) i16_type: IntType<'ctx>,
    pub(crate) i32_type: IntType<'ctx>,
    pub(crate) i64_type: IntType<'ctx>,
    pub(crate) i128_type: IntType<'ctx>,
    pub(crate) i256_type: IntType<'ctx>,
    pub(crate) ptr_type: PointerType<'ctx>,
}

impl<'ctx> LlvmContext<'ctx> {
    pub fn new(context: &'ctx Context, module_name: &str) -> Self {
        let module = context.create_module(module_name);
        let builder = context.create_builder();

        Self {
            context,
            module,
            builder,
            i8_type: context.i8_type(),
            i16_type: context.i16_type(),
            i32_type: context.i32_type(),
            i64_type: context.i64_type(),
            i128_type: context.i128_type(),
            i256_type: context.custom_width_int_type(256),
            ptr_type: context.ptr_type(AddressSpace::default()),
        }
    }

    /// Add a function defined in this module.
    pub fn add_function(&self, name: &str, fn_type: FunctionType<'ctx>) -> FunctionValue<'ctx> {
        self.module.add_function(name, fn_type, None)
    }

    /// Declare an external function (defined elsewhere, resolved at link time).
    pub fn declare_extern(&self, name: &str, fn_type: FunctionType<'ctx>) -> FunctionValue<'ctx> {
        self.module
            .add_function(name, fn_type, Some(Linkage::External))
    }

    /// Get an existing function or declare it as external.
    pub fn get_or_declare_extern(
        &self,
        name: &str,
        fn_type: FunctionType<'ctx>,
    ) -> FunctionValue<'ctx> {
        match self.module.get_function(name) {
            Some(f) => f,
            None => self.declare_extern(name, fn_type),
        }
    }
}
