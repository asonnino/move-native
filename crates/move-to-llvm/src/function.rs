// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

mod arithmetic;
mod calls;
mod constants;
mod control_flow;
mod state;
mod storage;
mod structs;

use inkwell::values::FunctionValue;
use move_model::ty::Type;
use move_stackless_bytecode::function_target::FunctionData;
use move_stackless_bytecode::stackless_bytecode::{Bytecode, Operation};

use crate::context::LlvmContext;
use crate::error::{CompileError, CompileResult};

pub(crate) use state::FunctionState;

use arithmetic::ArithmeticEmitter;
use calls::CallEmitter;
use constants::ConstantEmitter;
use control_flow::ControlFlowEmitter;
use storage::StorageEmitter;
use structs::StructEmitter;

/// Per-function lowering orchestrator.
///
/// Uses the alloca/mem2reg pattern: each stackless bytecode temp is mapped to
/// an LLVM `alloca` in the entry block. LLVM's `mem2reg` pass later promotes
/// these to SSA registers.
pub(crate) struct FunctionLowering<'a, 'ctx> {
    state: FunctionState<'a, 'ctx>,
}

impl<'a, 'ctx> FunctionLowering<'a, 'ctx> {
    pub(crate) fn new(
        ctx: &'a LlvmContext<'ctx>,
        function: FunctionValue<'ctx>,
        parameter_count: usize,
        function_data: &FunctionData,
        type_params: Vec<Type>,
    ) -> CompileResult<Self> {
        let entry = ctx.context.append_basic_block(function, "entry");
        ctx.builder.position_at_end(entry);

        let state = FunctionState::new(ctx, function, parameter_count, function_data, type_params)?;

        Ok(Self { state })
    }

    pub(crate) fn lower_function(&self, function_data: &FunctionData) -> CompileResult<()> {
        for byte_code in &function_data.code {
            self.lower_bytecode(byte_code)?;
        }
        Ok(())
    }

    fn lower_bytecode(&self, byte_code: &Bytecode) -> CompileResult<()> {
        match byte_code {
            Bytecode::Assign(_, destination, source, _kind) => {
                let value = self.state.load_value(*source)?;
                self.state.store(*destination, value)?;
            }
            Bytecode::Load(_, destination, constant) => {
                ConstantEmitter::new(&self.state).emit(*destination, constant)?;
            }
            Bytecode::Call(_, destinations, operation, sources, _) => {
                self.lower_operation(destinations, operation, sources)?;
            }
            Bytecode::Nop(_) => {}
            Bytecode::Ret(..)
            | Bytecode::Label(..)
            | Bytecode::Jump(..)
            | Bytecode::Branch(..)
            | Bytecode::Abort(..) => ControlFlowEmitter::new(&self.state).emit(byte_code)?,
            other => {
                return Err(CompileError::unsupported_bytecode(other.clone()));
            }
        }
        Ok(())
    }

    fn lower_operation(
        &self,
        destinations: &[usize],
        operation: &Operation,
        sources: &[usize],
    ) -> CompileResult<()> {
        match operation {
            // Arithmetic, comparisons, bitwise, shifts, logical, casts
            Operation::Add
            | Operation::Sub
            | Operation::Mul
            | Operation::Div
            | Operation::Mod
            | Operation::Lt
            | Operation::Gt
            | Operation::Le
            | Operation::Ge
            | Operation::Eq
            | Operation::Neq
            | Operation::BitAnd
            | Operation::BitOr
            | Operation::Xor
            | Operation::Shl
            | Operation::Shr
            | Operation::And
            | Operation::Or
            | Operation::Not
            | Operation::CastU8
            | Operation::CastU16
            | Operation::CastU32
            | Operation::CastU64
            | Operation::CastU128
            | Operation::CastU256 => {
                ArithmeticEmitter::new(&self.state).emit(destinations, operation, sources)
            }

            // Struct and reference operations
            Operation::Pack(..)
            | Operation::Unpack(..)
            | Operation::BorrowLoc
            | Operation::BorrowField(..)
            | Operation::GetField(..)
            | Operation::ReadRef
            | Operation::WriteRef
            | Operation::FreezeRef
            | Operation::Destroy => {
                StructEmitter::new(&self.state).emit(destinations, operation, sources)
            }

            // Function calls
            Operation::Function(module_id, function_id, type_args) => CallEmitter::new(&self.state)
                .emit(destinations, *module_id, *function_id, type_args, sources),

            // Global storage operations
            Operation::MoveTo(module_id, datatype_id, type_args) => StorageEmitter::new(
                &self.state,
            )
            .emit_move_to(*module_id, *datatype_id, type_args, destinations, sources),
            Operation::MoveFrom(module_id, datatype_id, type_args) => StorageEmitter::new(
                &self.state,
            )
            .emit_move_from(*module_id, *datatype_id, type_args, destinations, sources),
            Operation::Exists(module_id, datatype_id, type_args) => StorageEmitter::new(
                &self.state,
            )
            .emit_exists(*module_id, *datatype_id, type_args, destinations, sources),
            Operation::BorrowGlobal(module_id, datatype_id, type_args) => StorageEmitter::new(
                &self.state,
            )
            .emit_borrow_global(*module_id, *datatype_id, type_args, destinations, sources),
            Operation::GetGlobal(module_id, datatype_id, type_args) => StorageEmitter::new(
                &self.state,
            )
            .emit_get_global(*module_id, *datatype_id, type_args, destinations, sources),

            other => Err(CompileError::unsupported_operation(other.clone())),
        }
    }
}

#[cfg(test)]
pub(crate) mod test_helpers {
    use move_binary_format::file_format::{AbilitySet, DatatypeHandleIndex, SignatureToken};

    use crate::module::CompiledModuleBuilder;

    pub(crate) fn point_token() -> SignatureToken {
        SignatureToken::Datatype(DatatypeHandleIndex(0))
    }

    pub(crate) fn point_module() -> CompiledModuleBuilder {
        CompiledModuleBuilder::new().struct_definition(
            "Point",
            AbilitySet::PRIMITIVES,
            vec![("x", SignatureToken::U64), ("y", SignatureToken::U64)],
        )
    }
}

#[cfg(test)]
mod tests {
    use move_binary_format::file_format::{
        Bytecode, FieldHandleIndex, FunctionHandleIndex, SignatureToken, StructDefinitionIndex,
    };

    use crate::compiler::Compiler;
    use crate::module::CompiledModuleBuilder;
    use crate::target::Target;

    use super::test_helpers::{point_module, point_token};

    #[test]
    fn assign_copies_local() {
        // f(x: u64): u64 { let y = x; y }
        let module = CompiledModuleBuilder::new()
            .function(
                "copy_local",
                vec![SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![
                    Bytecode::CopyLoc(0), // push x
                    Bytecode::StLoc(1),   // y = x
                    Bytecode::MoveLoc(1), // push y
                    Bytecode::Ret,
                ],
            )
            .build();

        let asm = Compiler::compile_module(&Target::Aarch64, &module)
            .unwrap()
            .to_string();
        assert!(asm.contains("copy_local"), "missing symbol\n{asm}");
        assert!(asm.contains("ret"), "missing ret\n{asm}");
    }

    #[test]
    fn load_integer_constant() {
        // f(): u64 { 42 }
        let module = CompiledModuleBuilder::new()
            .function(
                "forty_two",
                vec![],
                vec![SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![
                    Bytecode::LdU64(42),
                    Bytecode::StLoc(0),
                    Bytecode::MoveLoc(0),
                    Bytecode::Ret,
                ],
            )
            .build();

        let asm = Compiler::compile_module(&Target::Aarch64, &module)
            .unwrap()
            .to_string();
        assert!(asm.contains("forty_two"), "missing symbol\n{asm}");
        // 42 = 0x2A, should appear as a mov immediate
        assert!(asm.contains("#42"), "missing immediate #42\n{asm}");
    }

    #[test]
    fn load_bool_constant() {
        // f(): bool { true }
        let module = CompiledModuleBuilder::new()
            .function(
                "always_true",
                vec![],
                vec![SignatureToken::Bool],
                vec![SignatureToken::Bool],
                vec![
                    Bytecode::LdTrue,
                    Bytecode::StLoc(0),
                    Bytecode::MoveLoc(0),
                    Bytecode::Ret,
                ],
            )
            .build();

        let asm = Compiler::compile_module(&Target::Aarch64, &module)
            .unwrap()
            .to_string();
        assert!(asm.contains("always_true"), "missing symbol\n{asm}");
        assert!(asm.contains("#1"), "missing #1 immediate for LdTrue\n{asm}");
    }

    #[test]
    fn arithmetic_on_struct_local_is_error() {
        // f(p: Point): Point { p + p } — Add on a struct should fail in load_int
        let module = point_module()
            .function(
                "bad_add",
                vec![point_token()],
                vec![point_token()],
                vec![point_token()],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CopyLoc(0),
                    Bytecode::Add,
                    Bytecode::StLoc(1),
                    Bytecode::MoveLoc(1),
                    Bytecode::Ret,
                ],
            )
            .build();

        let Err(err) = Compiler::compile_module(&Target::Aarch64, &module) else {
            panic!("expected MalformedModule error for Add on struct");
        };
        let message = err.to_string();
        assert!(
            message.contains("malformed module"),
            "unexpected error: {message}"
        );
        assert!(
            message.contains("expected integer"),
            "unexpected error: {message}"
        );
    }

    #[test]
    fn unpack_on_integer_local_is_error() {
        // f(x: u64): u64 { Unpack(x) } — Unpack on an integer should fail in load_struct
        let module = point_module()
            .function(
                "bad_unpack",
                vec![SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::Unpack(StructDefinitionIndex(0)),
                    Bytecode::StLoc(1),
                    Bytecode::MoveLoc(1),
                    Bytecode::Ret,
                ],
            )
            .build();

        let Err(err) = Compiler::compile_module(&Target::Aarch64, &module) else {
            panic!("expected MalformedModule error for Unpack on integer");
        };
        let message = err.to_string();
        assert!(
            message.contains("malformed module"),
            "unexpected error: {message}"
        );
        assert!(
            message.contains("expected struct"),
            "unexpected error: {message}"
        );
    }

    #[test]
    fn borrow_field_on_integer_local_is_error() {
        // f(x: u64): u64 { ImmBorrowField(x) } — BorrowField on an integer should fail
        let module = point_module()
            .field_handle(StructDefinitionIndex(0), 0)
            .function(
                "bad_borrow_field",
                vec![SignatureToken::U64],
                vec![SignatureToken::U64],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::ImmBorrowField(FieldHandleIndex(0)),
                    Bytecode::ReadRef,
                    Bytecode::Ret,
                ],
            )
            .build();

        let Err(err) = Compiler::compile_module(&Target::Aarch64, &module) else {
            panic!("expected MalformedModule error for BorrowField on integer");
        };
        let message = err.to_string();
        assert!(
            message.contains("malformed module"),
            "unexpected error: {message}"
        );
        assert!(
            message.contains("expected pointer"),
            "unexpected error: {message}"
        );
    }

    #[test]
    fn call_multi_return() {
        // swap(a: u64, b: u64): (u64, u64) { b, a }
        // call_swap(x: u64, y: u64): (u64, u64) { swap(x, y) }
        // Tests the destinations.len() > 1 branch in CallEmitter::emit
        let module = CompiledModuleBuilder::new()
            .function(
                "swap",
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![],
                vec![Bytecode::MoveLoc(1), Bytecode::MoveLoc(0), Bytecode::Ret],
            )
            .function(
                "call_swap",
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![SignatureToken::U64, SignatureToken::U64],
                vec![],
                vec![
                    Bytecode::CopyLoc(0),
                    Bytecode::CopyLoc(1),
                    Bytecode::Call(FunctionHandleIndex(0)),
                    Bytecode::Ret,
                ],
            )
            .build();

        let asm = Compiler::compile_module(&Target::Aarch64, &module)
            .unwrap()
            .to_string();
        assert!(asm.contains("swap"), "missing 'swap' symbol\n{asm}");
        assert!(
            asm.contains("call_swap"),
            "missing 'call_swap' symbol\n{asm}"
        );
        assert!(asm.contains("bl"), "missing 'bl' call instruction\n{asm}");
    }
}
