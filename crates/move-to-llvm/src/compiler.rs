// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::context::Context;
use inkwell::values::FunctionValue;
use move_binary_format::CompiledModule;
use move_model::model::FunctionEnv;
use move_stackless_bytecode::function_target::FunctionData;
use move_stackless_bytecode::stackless_bytecode_generator::StacklessBytecodeGenerator;

use crate::assembly::{Assembly, AssemblyBuilder};
use crate::context::LlvmContext;
use crate::error::{CompileError, CompileResult};
use crate::function::FunctionLowering;
use crate::mangle::Mangler;
use crate::types::TypeLowering;

/// Top-level compiler that owns the full Move -> AArch64 pipeline.
///
/// Bundles the LLVM context, the Move model environment (via `Mangler`),
/// and the code generator so that callers never need to thread
/// `(ctx, env)` pairs through every function call.
pub struct Compiler<'ctx> {
    pub(crate) ctx: LlvmContext<'ctx>,
    pub(crate) mangler: Mangler,
    asm_builder: AssemblyBuilder,
}

impl<'ctx> Compiler<'ctx> {
    /// Compile serialized Move bytecode to assembly.
    pub fn compile(bytecode: &[u8]) -> CompileResult<Assembly> {
        let module = CompiledModule::deserialize_with_defaults(bytecode)
            .map_err(|e| CompileError::Deserialize(e.to_string()))?;
        Self::compile_module(&module)
    }

    /// Compile an already-deserialized Move module to assembly.
    pub fn compile_module(module: &CompiledModule) -> CompileResult<Assembly> {
        Self::compile_module_with_dependencies(module, &[])
    }

    /// Compile a Move module to assembly, with dependency modules
    /// visible for resolving cross-module function signatures.
    pub fn compile_module_with_dependencies(
        module: &CompiledModule,
        dependencies: &[CompiledModule],
    ) -> CompileResult<Assembly> {
        let context = Context::create();
        Self::compile_with_dependencies_and_context(module, dependencies, &context)
    }

    /// Compile using an externally-owned LLVM context.
    fn compile_with_dependencies_and_context(
        module: &CompiledModule,
        dependencies: &[CompiledModule],
        context: &Context,
    ) -> CompileResult<Assembly> {
        let compiler = Compiler::new(context, module, dependencies)?;
        compiler.emit()
    }

    fn new(
        context: &'ctx Context,
        module: &CompiledModule,
        dependencies: &[CompiledModule],
    ) -> CompileResult<Self> {
        let mangler = Mangler::new(module, dependencies)?;
        let module_name = mangler.target_module().get_full_name_str();
        let ctx = LlvmContext::new(context, &module_name);
        let asm_builder = AssemblyBuilder::new()?;

        Ok(Self {
            ctx,
            mangler,
            asm_builder,
        })
    }

    fn emit(&self) -> CompileResult<Assembly> {
        let target_module_env = self.mangler.target_module();

        // Collect non-generic, non-native functions — the ones we compile
        // directly. Natives are implemented in Rust; generics are monomorphized
        // on demand at call sites (see CallEmitter::emit_generic).
        let targets: Vec<_> = target_module_env
            .into_functions()
            .filter(|t| !t.is_native() && t.get_type_parameter_count() == 0)
            .map(|function_env| {
                let generator = StacklessBytecodeGenerator::new(&function_env);
                let function_data = generator.generate_function();
                (function_env, function_data)
            })
            .collect();

        // Pass 1: declare all functions (so callees are visible).
        let declarations: Vec<_> = targets
            .iter()
            .map(|(function_env, _)| self.declare_function(function_env))
            .collect::<Result<_, _>>()?;

        // Pass 2: compile function bodies.
        // Emits IR into `self.ctx.module` via LLVM's interior-mutable FFI.
        for ((function_env, function_data), declaration) in targets.iter().zip(declarations) {
            self.compile_function(declaration, function_env, function_data)?;
        }

        self.asm_builder.optimize(&self.ctx.module)?;
        let mut asm = self.asm_builder.emit_assembly(&self.ctx.module)?;
        asm.add_symbol_aliases();
        Ok(asm)
    }

    /// Declare an LLVM function (signature only, no body) for the given Move function.
    fn declare_function(
        &self,
        function_env: &FunctionEnv<'_>,
    ) -> CompileResult<FunctionValue<'ctx>> {
        let name = function_env.get_name_str();
        let function_type = TypeLowering::new(&self.ctx, &self.mangler).lower_function_type(
            &function_env.get_parameter_types(),
            &function_env.get_return_types(),
        )?;
        Ok(self.ctx.add_function(&name, function_type))
    }

    /// Compile the body of an already-declared LLVM function.
    fn compile_function(
        &self,
        declaration: FunctionValue<'ctx>,
        function_env: &FunctionEnv<'_>,
        function_data: &FunctionData,
    ) -> CompileResult<()> {
        FunctionLowering::new(
            &self.ctx,
            &self.mangler,
            declaration,
            function_env.get_parameter_count(),
            function_data,
            Vec::new(),
        )?
        .lower_function(function_data)
    }
}
