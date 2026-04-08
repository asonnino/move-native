// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::context::Context;
use inkwell::values::FunctionValue;
use move_binary_format::CompiledModule;
use move_model::model::FunctionEnv;
use move_model::ty::Type;
use move_stackless_bytecode::function_target::FunctionData;
use move_stackless_bytecode::stackless_bytecode_generator::StacklessBytecodeGenerator;

use crate::assembly::Assembly;
use crate::codegen::CodegenBackend;
use crate::context::{DatatypeHandle, LlvmContext};
use crate::error::{CompileContext, CompileResult, catch_panic};
use crate::function::FunctionLowering;
use crate::mangle::Mangler;
use crate::object_file::ObjectFile;
use crate::target::Target;
use crate::types::TypeLowering;

/// Move bytecode compiler.
///
/// Builder-style API: create with [`new`](Self::new), optionally inject extra
/// assembly with [`set_module_assembly`](Self::set_module_assembly), then call
/// [`emit_assembly`](Self::emit_assembly) or [`emit_object`](Self::emit_object).
pub struct Compiler<'ctx> {
    pub(crate) ctx: LlvmContext<'ctx>,
    codegen: CodegenBackend,
}

impl<'ctx> Compiler<'ctx> {
    /// Create a compiler for a Move module.
    pub fn new(
        target: &Target,
        context: &'ctx Context,
        module: &CompiledModule,
        dependencies: &[CompiledModule],
    ) -> CompileResult<Self> {
        let ctx = LlvmContext::new(context, module, dependencies)?;
        let codegen = CodegenBackend::new(target)?;
        Ok(Self { ctx, codegen })
    }

    /// Inject raw assembly that LLVM's integrated assembler will compile
    /// alongside the Move functions. Use this to provide runtime stubs
    /// (e.g., `_start`, `__move_rt_arithmetic_error`) for freestanding
    /// execution modes.
    pub fn set_module_assembly(&self, asm: &str) {
        self.ctx.module.set_inline_assembly(asm);
    }

    /// Compile and emit as assembly text.
    ///
    /// Used by the hosted pipeline (runner → instrumenter → assembler).
    pub fn emit_assembly(&self) -> CompileResult<Assembly> {
        self.lower()?;
        self.codegen.build_assembly(&self.ctx.module)
    }

    /// Compile and emit as an ELF object file.
    ///
    /// Used by the freestanding pipeline (ZK prover). All symbols —
    /// including any injected via [`set_module_assembly`](Self::set_module_assembly) —
    /// are resolved by LLVM's integrated assembler.
    pub fn emit_object(&self) -> CompileResult<ObjectFile> {
        self.lower()?;
        self.codegen.build_object(&self.ctx.module)
    }

    /// Compile Move functions to LLVM IR and optimize.
    fn lower(&self) -> CompileResult<()> {
        let target_module_env = self.ctx.target_module()?;

        // Collect non-native functions that we can compile directly:
        // - Non-generic functions (no type params)
        // - Phantom-only generic functions (all type params are phantom)
        //
        // Truly generic functions are monomorphized on demand at call sites
        // (see CallEmitter::emit_generic). Natives are implemented in Rust.
        let targets: Vec<_> = target_module_env
            .into_functions()
            .filter(|t| !t.is_native())
            .map(|function_env| {
                let dominated_by_phantom = self.has_only_phantom_type_params(&function_env)?;
                Ok((function_env, dominated_by_phantom))
            })
            .collect::<CompileResult<Vec<_>>>()?
            .into_iter()
            .filter(|(_, phantom)| *phantom)
            .map(|(function_env, _)| {
                let name = function_env.get_name_str().to_string();
                let generator = StacklessBytecodeGenerator::new(&function_env);
                let function_data = catch_panic(&name, || generator.generate_function())?;
                Ok((function_env, function_data))
            })
            .collect::<CompileResult<Vec<_>>>()?;

        // Pass 1: declare all functions (so callees are visible).
        let declarations: Vec<_> = targets
            .iter()
            .map(|(function_env, _)| self.declare_function(function_env))
            .collect::<Result<_, _>>()?;

        // Pass 2: compile function bodies.
        for ((function_env, function_data), declaration) in targets.iter().zip(declarations) {
            let name = function_env.get_name_str();
            self.compile_function(declaration, function_env, function_data)
                .with_context(|| format!("in function '{name}'"))?;
        }

        self.codegen.optimize(&self.ctx.module)?;
        Ok(())
    }

    /// Declare an LLVM function (signature only, no body) for the given Move function.
    fn declare_function(
        &self,
        function_env: &FunctionEnv<'_>,
    ) -> CompileResult<FunctionValue<'ctx>> {
        let name = Mangler::qualified_function_name(function_env);
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
    fn has_only_phantom_type_params(&self, function_env: &FunctionEnv<'_>) -> CompileResult<bool> {
        let count = function_env.get_type_parameter_count();
        if count == 0 {
            return Ok(true);
        }
        // We only need to check the function signature (parameters + returns).
        // Move's bytecode verifier guarantees that phantom type parameters cannot
        // appear in non-phantom positions anywhere in the function body either,
        // so the signature check is sufficient.
        let param_types = function_env.get_parameter_types();
        let return_types = function_env.get_return_types();
        let all_types: Vec<&Type> = param_types.iter().chain(return_types.iter()).collect();

        for idx in 0..count as u16 {
            for ty in &all_types {
                if !self.is_phantom_in_type(idx, ty)? {
                    return Ok(false);
                }
            }
        }
        Ok(true)
    }

    /// Check that `TypeParameter(param_idx)` only appears in phantom positions within `ty`.
    ///
    /// Returns `true` if the type parameter is either absent or only used as a
    /// type argument in a phantom position of a struct.
    fn is_phantom_in_type(&self, param_idx: u16, ty: &Type) -> CompileResult<bool> {
        match ty {
            Type::TypeParameter(idx) => Ok(*idx != param_idx),
            Type::Primitive(_) => Ok(true),
            Type::Reference(_, inner) | Type::Vector(inner) => {
                self.is_phantom_in_type(param_idx, inner)
            }
            Type::Datatype(module_id, datatype_id, type_args) => {
                let handle = DatatypeHandle::new(*module_id, *datatype_id);
                let datatype_env = self.ctx.get_datatype_env(handle)?;
                for (i, arg) in type_args.iter().enumerate() {
                    let is_phantom = datatype_env.is_phantom_parameter(i);
                    if !is_phantom && !self.is_phantom_in_type(param_idx, arg)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(true),
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

    use crate::{Target, module::CompiledModuleBuilder};

    #[test]
    fn empty_bytecode_is_error() {
        let result = crate::compile(&Target::host(), &[]);
        assert!(result.is_err(), "empty bytecode should fail");
    }

    #[test]
    fn garbage_bytecode_is_error() {
        let result = crate::compile(&Target::host(), &[0xDE, 0xAD]);
        assert!(result.is_err(), "garbage bytecode should fail");
    }

    #[test]
    fn missing_dependency_is_error() {
        let (module, _deps) = CompiledModuleBuilder::kitchen_sink();
        // Pass empty deps — dependency validation catches missing modules.
        let result = crate::compile_module_with_deps(&Target::host(), &module, &[]);
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

        let asm = CompiledModuleBuilder::balance()
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
            .compile();
        assert!(
            asm.contains("_mv_0x0_M_value"),
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

        let asm = CompiledModuleBuilder::balance()
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
            .compile();
        assert!(
            asm.contains("_mv_0x0_M_zero"),
            "phantom-generic 'zero' should be compiled\n{asm}"
        );
    }

    #[test]
    fn phantom_generic_calls_phantom_generic() {
        // phantom_read_x<T>(b: &Balance<T>): u64 { b.value }
        // phantom_proxy<T>(b: &Balance<T>): u64 { phantom_read_x<T>(b) }
        //
        // phantom_proxy calls phantom_read_x via CallGeneric with [TypeParameter(0)].
        // TypeParameter(0) must be erased to produce phantom_read_x$u64.
        let balance_t = SignatureToken::DatatypeInstantiation(Box::new((
            DatatypeHandleIndex(0),
            vec![SignatureToken::TypeParameter(0)],
        )));
        let ref_balance_t = SignatureToken::Reference(Box::new(balance_t));

        let asm = CompiledModuleBuilder::balance()
            .field_handle(StructDefinitionIndex(0), 0)
            // FunctionHandleIndex(0): phantom_read_x<T>
            .generic_function(
                "phantom_read_x",
                vec![AbilitySet::EMPTY],
                vec![ref_balance_t.clone()],
                vec![SignatureToken::U64],
                vec![],
                vec![
                    Bytecode::MoveLoc(0),
                    Bytecode::ImmBorrowField(FieldHandleIndex(0)),
                    Bytecode::ReadRef,
                    Bytecode::Ret,
                ],
            )
            // FunctionInstantiationIndex(0): phantom_read_x<TypeParameter(0)>
            .function_instantiation(
                move_binary_format::file_format::FunctionHandleIndex(0),
                vec![SignatureToken::TypeParameter(0)],
            )
            // FunctionHandleIndex(1): phantom_proxy<T>
            .generic_function(
                "phantom_proxy",
                vec![AbilitySet::EMPTY],
                vec![ref_balance_t],
                vec![SignatureToken::U64],
                vec![],
                vec![
                    Bytecode::MoveLoc(0),
                    Bytecode::CallGeneric(
                        move_binary_format::file_format::FunctionInstantiationIndex(0),
                    ),
                    Bytecode::Ret,
                ],
            )
            .compile();
        assert!(
            asm.contains("_mv_0x0_M_phantom_read_x$u64"),
            "should contain erased monomorphization phantom_read_x$u64\n{asm}"
        );
        assert!(
            asm.contains("_mv_0x0_M_phantom_proxy"),
            "phantom_proxy should be compiled\n{asm}"
        );
    }

    #[test]
    fn phantom_generic_with_type_param_local() {
        // use_local<T>(x: &Balance<T>): u64 { let tmp: T; tmp = 42; tmp }
        let balance_t = SignatureToken::DatatypeInstantiation(Box::new((
            DatatypeHandleIndex(0),
            vec![SignatureToken::TypeParameter(0)],
        )));
        let ref_balance_t = SignatureToken::Reference(Box::new(balance_t));

        let asm = CompiledModuleBuilder::balance()
            .generic_function(
                "use_local",
                vec![AbilitySet::EMPTY],
                vec![ref_balance_t],
                vec![SignatureToken::U64],
                // Explicit local of type TypeParameter(0) — the crux of this test.
                vec![SignatureToken::TypeParameter(0)],
                vec![
                    Bytecode::LdU64(42),
                    Bytecode::StLoc(1), // store into the TypeParameter(0) local
                    Bytecode::MoveLoc(1),
                    Bytecode::Ret,
                ],
            )
            .compile();
        assert!(
            asm.contains("_mv_0x0_M_use_local"),
            "phantom-generic with T-typed local should compile\n{asm}"
        );
    }

    #[test]
    fn non_phantom_generic_not_compiled_at_top_level() {
        // identity<T>(x: T): T — T is NOT phantom (bare usage in params/returns).
        // This function should NOT be compiled at the top level.
        let asm = CompiledModuleBuilder::new()
            .generic_function(
                "identity",
                vec![AbilitySet::EMPTY],
                vec![SignatureToken::TypeParameter(0)],
                vec![SignatureToken::TypeParameter(0)],
                vec![],
                vec![Bytecode::MoveLoc(0), Bytecode::Ret],
            )
            .compile();
        assert!(
            !asm.contains("_mv_0x0_M_identity"),
            "non-phantom generic 'identity' should NOT be compiled at top level\n{asm}"
        );
    }

    #[test]
    fn set_module_assembly_injects_symbols() {
        let module = CompiledModuleBuilder::new()
            .function(
                "add",
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CopyLoc(1),
                    Bytecode::Add,
                    Bytecode::Ret,
                ],
            )
            .build();

        let context = inkwell::context::Context::create();
        let compiler = super::Compiler::new(&Target::Riscv64, &context, &module, &[]).unwrap();
        compiler.set_module_assembly(".globl _start\n_start:\n\tret\n");
        let object = compiler.emit_object().unwrap();

        let parsed = object::File::parse(object.as_bytes()).unwrap();
        use object::{Object, ObjectSymbol};
        let symbols: Vec<String> = parsed
            .symbols()
            .filter_map(|s| s.name().ok().map(|n| n.to_string()))
            .collect();

        assert!(
            symbols.iter().any(|s| s == "_start"),
            "injected _start missing: {symbols:?}"
        );
        assert!(
            symbols.iter().any(|s| s.contains("_mv_0x0_M_add")),
            "Move function symbol missing: {symbols:?}"
        );
    }
}
