// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::AddressSpace;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::types::{FunctionType, IntType, PointerType};
use inkwell::values::FunctionValue;
use move_binary_format::CompiledModule;
use move_model::model::{GlobalEnv, ModuleEnv};

use move_model::model::FunctionEnv;
use move_model::ty::Type;

use crate::error::{CompileError, CompileResult};
use crate::mangle::Mangler;

/// Wraps the LLVM Context, Module, and Builder for a single compilation unit.
///
/// Also owns the Move `GlobalEnv` (semantic model) so that all central
/// infrastructure lives in one place.
pub(crate) struct LlvmContext<'ctx> {
    pub(crate) env: GlobalEnv,
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
    pub fn new(
        context: &'ctx Context,
        module: &CompiledModule,
        dependencies: &[CompiledModule],
    ) -> CompileResult<Self> {
        let all_modules: Vec<&CompiledModule> =
            dependencies.iter().chain(std::iter::once(module)).collect();
        let env = move_model::run_bytecode_model_builder(all_modules)
            .map_err(|e| CompileError::ModelBuilder(e.to_string()))?;
        let module_name = env
            .get_modules()
            .last()
            .expect("env always contains at least the target module")
            .get_full_name_str();
        let llvm_module = context.create_module(&module_name);
        let builder = context.create_builder();

        Ok(Self {
            env,
            context,
            module: llvm_module,
            builder,
            i8_type: context.i8_type(),
            i16_type: context.i16_type(),
            i32_type: context.i32_type(),
            i64_type: context.i64_type(),
            i128_type: context.i128_type(),
            i256_type: context.custom_width_int_type(256),
            ptr_type: context.ptr_type(AddressSpace::default()),
        })
    }

    pub fn env(&self) -> &GlobalEnv {
        &self.env
    }

    /// The module being compiled (always the last one added to the environment).
    pub fn target_module(&self) -> ModuleEnv<'_> {
        self.env
            .get_modules()
            .last()
            .expect("env always contains at least the target module")
    }

    /// Look up an already-declared function by name.
    pub fn get_function(&self, name: &str) -> Option<FunctionValue<'ctx>> {
        self.module.get_function(name)
    }

    /// Define an internal function in this module.
    pub fn add_function(
        &self,
        name: &str,
        function_type: FunctionType<'ctx>,
    ) -> FunctionValue<'ctx> {
        self.module.add_function(name, function_type, None)
    }

    /// Declare an external function (defined elsewhere, resolved at link time), idempotent.
    pub fn add_external_function(
        &self,
        name: &str,
        function_type: FunctionType<'ctx>,
    ) -> FunctionValue<'ctx> {
        self.module.get_function(name).unwrap_or_else(|| {
            self.module
                .add_function(name, function_type, Some(Linkage::External))
        })
    }

    /// Mangle a Move type into a symbol-safe string.
    pub fn mangle_type(&self, ty: &Type) -> CompileResult<String> {
        Mangler::new(&self.env).mangle_type(ty)
    }

    /// Mangle type arguments into a `$`-separated string.
    pub fn mangle_type_args(&self, type_args: &[Type]) -> CompileResult<String> {
        Mangler::new(&self.env).mangle_type_args(type_args)
    }

    /// Build the mangled symbol name for a native function call.
    pub fn mangle_native_symbol(
        &self,
        callee_env: &FunctionEnv<'_>,
        type_args: &[Type],
    ) -> CompileResult<String> {
        Mangler::new(&self.env).mangle_native_symbol(callee_env, type_args)
    }
}
