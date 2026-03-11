// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::values::{BasicValueEnum, FunctionValue};
use move_model::model::{FunId, ModuleId};
use move_model::ty::Type;
use move_stackless_bytecode::stackless_bytecode_generator::StacklessBytecodeGenerator;

use super::FunctionLowering;
use super::state::{CallSiteValueExt, FunctionState};
use crate::error::{CompileError, CompileResult};

/// Emits LLVM call instructions for Move function calls.
///
/// Handles three cases: native functions (extern declarations),
/// generic functions (monomorphization), and non-generic calls.
pub(crate) struct CallEmitter<'a, 'b, 'ctx> {
    state: &'a FunctionState<'b, 'ctx>,
}

impl<'a, 'b, 'ctx> CallEmitter<'a, 'b, 'ctx> {
    pub(super) fn new(state: &'a FunctionState<'b, 'ctx>) -> Self {
        Self { state }
    }

    pub(super) fn emit(
        &self,
        destinations: &[usize],
        module_id: ModuleId,
        function_id: FunId,
        type_args: &[Type],
        sources: &[usize],
    ) -> CompileResult<()> {
        let llvm = &self.state.ctx;
        let callee_env = self.state.ctx.get_function_env(module_id, function_id);

        let (callee_fn, call_name) = if callee_env.is_native() {
            self.emit_native(&callee_env, type_args)?
        } else if !type_args.is_empty() {
            self.emit_generic(&callee_env, type_args)?
        } else {
            self.emit_non_generic(&callee_env)?
        };

        let args: Vec<_> = sources
            .iter()
            .map(|s| self.state.load_value(*s).map(|v| v.into()))
            .collect::<Result<_, _>>()?;

        let call = llvm.builder.build_call(callee_fn, &args, &call_name)?;

        if !destinations.is_empty() {
            let return_value = call.into_basic_value()?;
            if destinations.len() == 1 {
                self.state.store(destinations[0], return_value)?;
            } else {
                let BasicValueEnum::StructValue(struct_val) = return_value else {
                    return Err(CompileError::malformed_module(format!(
                        "expected struct return for multi-value call, got {return_value:?}"
                    )));
                };
                for (i, destination) in destinations.iter().enumerate() {
                    let field = llvm.builder.build_extract_value(
                        struct_val,
                        i as u32,
                        &format!("call_ret_{i}"),
                    )?;
                    self.state.store(*destination, field)?;
                }
            }
        }
        Ok(())
    }

    /// Native function: declare as extern with monomorphized symbol.
    fn emit_native(
        &self,
        callee_env: &move_model::model::FunctionEnv<'_>,
        type_args: &[Type],
    ) -> CompileResult<(FunctionValue<'ctx>, String)> {
        let llvm = &self.state.ctx;
        let mangled = self.state.mangle_native_symbol(callee_env, type_args)?;
        let inst_params: Vec<Type> = callee_env
            .get_parameter_types()
            .iter()
            .map(|t: &Type| t.instantiate(type_args))
            .collect();
        let inst_rets: Vec<Type> = callee_env
            .get_return_types()
            .iter()
            .map(|t: &Type| t.instantiate(type_args))
            .collect();
        let fn_type = self.state.lower_function_type(&inst_params, &inst_rets)?;
        let f = llvm.add_external_function(&mangled, fn_type);
        Ok((f, mangled))
    }

    /// Monomorphize: compile a specialized copy of the callee
    /// with TypeParameters replaced by concrete types.
    fn emit_generic(
        &self,
        callee_env: &move_model::model::FunctionEnv<'_>,
        type_args: &[Type],
    ) -> CompileResult<(FunctionValue<'ctx>, String)> {
        let llvm = &self.state.ctx;
        let inst_args = self.state.instantiate_types(type_args);
        let callee_name = callee_env.get_name_str();
        let args = self.state.mangle_type_args(&inst_args)?;
        let mangled = format!("{callee_name}${args}");
        let f = match llvm.get_function(&mangled) {
            Some(f) => f,
            None => {
                let inst_params: Vec<Type> = callee_env
                    .get_parameter_types()
                    .iter()
                    .map(|t: &Type| t.instantiate(&inst_args))
                    .collect();
                let inst_rets: Vec<Type> = callee_env
                    .get_return_types()
                    .iter()
                    .map(|t: &Type| t.instantiate(&inst_args))
                    .collect();
                let fn_type = self.state.lower_function_type(&inst_params, &inst_rets)?;
                let function = llvm.add_function(&mangled, fn_type);

                let saved_block = llvm
                    .builder
                    .get_insert_block()
                    .ok_or(CompileError::llvm("no insert block"))?;

                let generator = StacklessBytecodeGenerator::new(callee_env);
                let func_data = generator.generate_function();
                let param_count = callee_env.get_parameter_count();
                let callee_lowering = FunctionLowering::new(
                    self.state.ctx,
                    function,
                    param_count,
                    &func_data,
                    inst_args,
                )?;
                callee_lowering.lower_function(&func_data)?;

                llvm.builder.position_at_end(saved_block);
                function
            }
        };
        Ok((f, mangled))
    }

    /// Non-generic, non-native: look up in current LLVM module first
    /// (intra-module calls declared in pass 1), then fall back to an
    /// extern declaration for cross-module calls resolved at link time.
    fn emit_non_generic(
        &self,
        callee_env: &move_model::model::FunctionEnv<'_>,
    ) -> CompileResult<(FunctionValue<'ctx>, String)> {
        let llvm = &self.state.ctx;
        let callee_name = callee_env.get_name_str();
        let f = match llvm.get_function(&callee_name) {
            Some(f) => f,
            None => {
                let fn_type = self.state.lower_function_type(
                    &callee_env.get_parameter_types(),
                    &callee_env.get_return_types(),
                )?;
                llvm.add_external_function(&callee_name, fn_type)
            }
        };
        Ok((f, callee_name))
    }
}

#[cfg(test)]
mod tests {
    use move_binary_format::file_format::{
        AbilitySet, Bytecode, FunctionHandleIndex, FunctionInstantiationIndex, SignatureToken,
    };

    use crate::compiler::Compiler;
    use crate::module::CompiledModuleBuilder;

    #[test]
    fn call_non_generic() {
        let module = CompiledModuleBuilder::new()
            .function(
                "double",
                vec![SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CopyLoc(0),
                    Bytecode::Add,
                    Bytecode::Ret,
                ],
            )
            .function(
                "caller",
                vec![SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::Call(FunctionHandleIndex(0)),
                    Bytecode::Ret,
                ],
            )
            .build();

        let asm = Compiler::compile_to_asm(&module);
        assert!(asm.contains("double"), "missing 'double' symbol\n{asm}");
        assert!(asm.contains("caller"), "missing 'caller' symbol\n{asm}");
        assert!(asm.contains("bl"), "missing 'bl' call instruction\n{asm}");
    }

    #[test]
    fn call_generic() {
        let module = CompiledModuleBuilder::new()
            .generic_function(
                "identity",
                vec![AbilitySet::EMPTY],
                vec![SignatureToken::TypeParameter(0)],
                vec![SignatureToken::TypeParameter(0)],
                vec![],
                vec![Bytecode::MoveLoc(0), Bytecode::Ret],
            )
            .function(
                "caller",
                vec![SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CallGeneric(FunctionInstantiationIndex(0)),
                    Bytecode::Ret,
                ],
            )
            .function_instantiation(FunctionHandleIndex(0), vec![SignatureToken::U64])
            .build();

        let asm = Compiler::compile_to_asm(&module);
        assert!(
            asm.contains("identity$u64"),
            "missing monomorphized 'identity$u64' symbol\n{asm}"
        );
        assert!(asm.contains("caller"), "missing 'caller' symbol\n{asm}");
    }

    #[test]
    fn call_native() {
        let module = CompiledModuleBuilder::new()
            .native_function(
                "native_add",
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![SignatureToken::U64],
            )
            .function(
                "caller",
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CopyLoc(1),
                    Bytecode::Call(FunctionHandleIndex(0)),
                    Bytecode::Ret,
                ],
            )
            .build();

        let asm = Compiler::compile_to_asm(&module);
        assert!(asm.contains("caller"), "missing 'caller' symbol\n{asm}");
        assert!(
            asm.contains("__move_rt_0x0_M_native_add"),
            "missing mangled native symbol\n{asm}"
        );
    }
}
