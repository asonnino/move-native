// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::context::Context;
use inkwell::values::FunctionValue;
use move_binary_format::CompiledModule;
use move_model::model::FunctionEnv;
use move_model::ty::Type;
use move_stackless_bytecode::function_target::FunctionData;
use move_stackless_bytecode::stackless_bytecode_generator::StacklessBytecodeGenerator;

use crate::assembly::{Assembly, AssemblyBuilder};
use crate::context::LlvmContext;
use crate::error::{CompileError, CompileResult};
use crate::function::FunctionLowering;
use crate::target::Target;
use crate::types::TypeLowering;

/// Top-level compiler that owns the full Move -> AArch64 pipeline.
///
/// Bundles the LLVM context (which includes the Move `GlobalEnv`)
/// and the code generator so that callers never need to thread
/// infrastructure through every function call.
pub struct Compiler<'ctx> {
    pub(crate) ctx: LlvmContext<'ctx>,
    asm_builder: AssemblyBuilder,
}

impl<'ctx> Compiler<'ctx> {
    /// Compile serialized Move bytecode to assembly.
    pub fn compile(target: &Target, bytecode: &[u8]) -> CompileResult<Assembly> {
        let module = CompiledModule::deserialize_with_defaults(bytecode)
            .map_err(|e| CompileError::deserialize(e.to_string()))?;
        Self::compile_module(target, &module)
    }

    /// Compile an already-deserialized Move module to assembly.
    pub fn compile_module(target: &Target, module: &CompiledModule) -> CompileResult<Assembly> {
        Self::compile_module_with_dependencies(target, module, &[])
    }

    /// Compile a Move module to assembly, with dependency modules
    /// visible for resolving cross-module function signatures.
    pub fn compile_module_with_dependencies(
        target: &Target,
        module: &CompiledModule,
        dependencies: &[CompiledModule],
    ) -> CompileResult<Assembly> {
        let context = Context::create();
        let compiler = Compiler::new(target, &context, module, dependencies)?;
        compiler.emit()
    }

    fn new(
        target: &Target,
        context: &'ctx Context,
        module: &CompiledModule,
        dependencies: &[CompiledModule],
    ) -> CompileResult<Self> {
        let ctx = LlvmContext::new(context, module, dependencies)?;
        let asm_builder = AssemblyBuilder::new(target)?;

        Ok(Self { ctx, asm_builder })
    }

    fn emit(&self) -> CompileResult<Assembly> {
        let target_module_env = self.ctx.target_module();

        // Collect non-native functions that we can compile directly:
        // - Non-generic functions (no type params)
        // - Phantom-only generic functions (all type params are phantom)
        //
        // Truly generic functions are monomorphized on demand at call sites
        // (see CallEmitter::emit_generic). Natives are implemented in Rust.
        let targets: Vec<_> = target_module_env
            .into_functions()
            .filter(|t| !t.is_native() && self.has_only_phantom_type_params(t))
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
        let mut asm = self.asm_builder.build(&self.ctx.module)?;
        asm.add_symbol_aliases();
        Ok(asm)
    }

    /// Declare an LLVM function (signature only, no body) for the given Move function.
    fn declare_function(
        &self,
        function_env: &FunctionEnv<'_>,
    ) -> CompileResult<FunctionValue<'ctx>> {
        let name = function_env.get_name_str();
        let function_type = TypeLowering::new(&self.ctx).lower_function_type(
            &function_env.get_parameter_types(),
            &function_env.get_return_types(),
        )?;
        Ok(self.ctx.add_function(&name, function_type))
    }

    /// Returns true if the function has no type parameters, or all of its
    /// type parameters only appear in phantom positions of struct type arguments.
    ///
    /// Phantom-only generic functions can be compiled as-if non-generic because
    /// the phantom type parameters don't affect memory layout or code generation.
    fn has_only_phantom_type_params(&self, function_env: &FunctionEnv<'_>) -> bool {
        let count = function_env.get_type_parameter_count();
        if count == 0 {
            return true;
        }
        // We only need to check the function signature (parameters + returns).
        // Move's bytecode verifier guarantees that phantom type parameters cannot
        // appear in non-phantom positions anywhere in the function body either,
        // so the signature check is sufficient.
        let param_types = function_env.get_parameter_types();
        let return_types = function_env.get_return_types();
        let all_types: Vec<&Type> = param_types.iter().chain(return_types.iter()).collect();

        (0..count as u16).all(|idx| all_types.iter().all(|ty| self.is_phantom_in_type(idx, ty)))
    }

    /// Check that `TypeParameter(param_idx)` only appears in phantom positions within `ty`.
    ///
    /// Returns `true` if the type parameter is either absent or only used as a
    /// type argument in a phantom position of a struct.
    fn is_phantom_in_type(&self, param_idx: u16, ty: &Type) -> bool {
        match ty {
            Type::TypeParameter(idx) => *idx != param_idx,
            Type::Primitive(_) => true,
            Type::Reference(_, inner) | Type::Vector(inner) => {
                self.is_phantom_in_type(param_idx, inner)
            }
            Type::Datatype(module_id, datatype_id, type_args) => {
                let struct_env = self.ctx.get_struct_env(*module_id, *datatype_id);
                type_args.iter().enumerate().all(|(i, arg)| {
                    struct_env.is_phantom_parameter(i) || self.is_phantom_in_type(param_idx, arg)
                })
            }
            _ => true,
        }
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
            declaration,
            function_env.get_parameter_count(),
            function_data,
            Vec::new(),
        )?
        .lower_function(function_data)
    }
}

#[cfg(test)]
mod tests {
    use move_binary_format::file_format::{
        AbilitySet, Bytecode, DatatypeHandleIndex, FieldHandleIndex, SignatureToken,
        StructDefinitionIndex,
    };

    use crate::{Compiler, Target, module::CompiledModuleBuilder};

    #[test]
    fn empty_bytecode_is_error() {
        let result = Compiler::compile(&Target::host(), &[]);
        assert!(result.is_err(), "empty bytecode should fail");
    }

    #[test]
    fn garbage_bytecode_is_error() {
        let result = Compiler::compile(&Target::host(), &[0xDE, 0xAD]);
        assert!(result.is_err(), "garbage bytecode should fail");
    }

    #[test]
    fn missing_dependency_is_error() {
        let (module, _deps) = CompiledModuleBuilder::kitchen_sink();
        // Pass empty deps — dependency validation catches missing modules.
        let result = Compiler::compile_module_with_dependencies(&Target::host(), &module, &[]);
        assert!(result.is_err(), "missing dependencies should fail");
    }

    #[test]
    fn phantom_generic_value_compiles() {
        // value<T>(self: &Balance<T>): u64 { self.value }
        let balance_t = SignatureToken::DatatypeInstantiation(Box::new((
            DatatypeHandleIndex(0),
            vec![SignatureToken::TypeParameter(0)],
        )));
        let ref_balance_t = SignatureToken::Reference(Box::new(balance_t));

        let module = CompiledModuleBuilder::balance()
            .field_handle(StructDefinitionIndex(0), 0)
            .generic_function(
                "value",
                vec![AbilitySet::EMPTY],
                vec![ref_balance_t],
                vec![SignatureToken::U64],
                vec![],
                vec![
                    Bytecode::MoveLoc(0),                          // push &self
                    Bytecode::ImmBorrowField(FieldHandleIndex(0)), // &self.value
                    Bytecode::ReadRef,                             // *(&self.value)
                    Bytecode::Ret,
                ],
            )
            .build();

        let asm = Compiler::compile_module(&Target::host(), &module).unwrap();
        assert!(
            asm.contains("value"),
            "phantom-generic 'value' should be compiled\n{asm}"
        );
        assert!(asm.contains("ret"), "should contain ret\n{asm}");
    }

    #[test]
    fn phantom_generic_zero_compiles() {
        // zero<T>(): Balance<T> { Balance { value: 0 } }
        let balance_t = SignatureToken::DatatypeInstantiation(Box::new((
            DatatypeHandleIndex(0),
            vec![SignatureToken::TypeParameter(0)],
        )));

        let module = CompiledModuleBuilder::balance()
            .generic_function(
                "zero",
                vec![AbilitySet::EMPTY],
                vec![],
                vec![balance_t],
                vec![],
                vec![
                    Bytecode::LdU64(0),
                    Bytecode::PackGeneric(
                        move_binary_format::file_format::StructDefInstantiationIndex(0),
                    ),
                    Bytecode::Ret,
                ],
            )
            .struct_def_instantiation(
                StructDefinitionIndex(0),
                vec![SignatureToken::TypeParameter(0)],
            )
            .build();

        let asm = Compiler::compile_module(&Target::host(), &module).unwrap();
        assert!(
            asm.contains("zero"),
            "phantom-generic 'zero' should be compiled\n{asm}"
        );
    }

    #[test]
    fn non_phantom_generic_not_compiled_at_top_level() {
        // identity<T>(x: T): T — T is NOT phantom (bare usage in params/returns).
        // This function should NOT be compiled at the top level.
        let module = CompiledModuleBuilder::new()
            .generic_function(
                "identity",
                vec![AbilitySet::EMPTY],
                vec![SignatureToken::TypeParameter(0)],
                vec![SignatureToken::TypeParameter(0)],
                vec![],
                vec![Bytecode::MoveLoc(0), Bytecode::Ret],
            )
            .build();

        let asm = Compiler::compile_module(&Target::host(), &module).unwrap();
        assert!(
            !asm.contains("identity"),
            "non-phantom generic 'identity' should NOT be compiled at top level\n{asm}"
        );
    }
}
