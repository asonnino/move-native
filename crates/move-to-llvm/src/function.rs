use inkwell::values::{FunctionValue, IntValue, PointerValue};

use move_binary_format::file_format::{Bytecode, CodeUnit, FunctionDefinition, SignatureToken};

use crate::context::LlvmContext;
use crate::error::CompileError;
use crate::types::lower_type;

/// Per-function lowering state.
///
/// Uses the alloca/mem2reg pattern: each Move local is mapped to an LLVM
/// `alloca` in the entry block. LLVM's `mem2reg` pass later promotes these
/// to SSA registers.
pub struct FunctionLowering<'a, 'ctx> {
    ctx: &'a LlvmContext<'ctx>,
    function: FunctionValue<'ctx>,
    /// Allocas for each local (parameters + locals from CodeUnit).
    locals: Vec<PointerValue<'ctx>>,
    /// Operand stack (mirrors the Move VM's value stack).
    stack: Vec<IntValue<'ctx>>,
}

impl<'a, 'ctx> FunctionLowering<'a, 'ctx> {
    /// Create a new function lowering, emitting the entry block with allocas
    /// for all locals and stores for the parameter values.
    pub fn new(
        ctx: &'a LlvmContext<'ctx>,
        function: FunctionValue<'ctx>,
        param_types: &[SignatureToken],
        local_types: &[SignatureToken],
    ) -> Result<Self, CompileError> {
        let entry = ctx.context.append_basic_block(function, "entry");
        ctx.builder.position_at_end(entry);

        let mut locals = Vec::with_capacity(param_types.len() + local_types.len());

        // Allocas for parameters
        for (i, tok) in param_types.iter().enumerate() {
            let ty = lower_type(ctx, tok)?;
            let alloca = ctx.builder.build_alloca(ty, &format!("p{i}")).unwrap();
            // Store the parameter value into its alloca
            let param = function.get_nth_param(i as u32).unwrap().into_int_value();
            ctx.builder.build_store(alloca, param).unwrap();
            locals.push(alloca);
        }

        // Allocas for non-parameter locals
        for (i, tok) in local_types.iter().enumerate() {
            let ty = lower_type(ctx, tok)?;
            let alloca = ctx
                .builder
                .build_alloca(ty, &format!("l{i}"))
                .unwrap();
            locals.push(alloca);
        }

        Ok(Self {
            ctx,
            function,
            locals,
            stack: Vec::new(),
        })
    }

    /// Lower all bytecodes in a CodeUnit.
    pub fn lower_code(&mut self, code: &CodeUnit) -> Result<(), CompileError> {
        for (offset, bc) in code.code.iter().enumerate() {
            self.lower_bytecode(bc, offset)?;
        }
        Ok(())
    }

    fn lower_bytecode(&mut self, bc: &Bytecode, _offset: usize) -> Result<(), CompileError> {
        match bc {
            Bytecode::CopyLoc(idx) => {
                let ptr = self.locals[*idx as usize];
                let val = self
                    .ctx
                    .builder
                    .build_load(self.ctx.i64_type, ptr, "copy")
                    .unwrap()
                    .into_int_value();
                self.stack.push(val);
            }
            Bytecode::MoveLoc(idx) => {
                // For Milestone 1, MoveLoc is identical to CopyLoc (integers are Copy).
                let ptr = self.locals[*idx as usize];
                let val = self
                    .ctx
                    .builder
                    .build_load(self.ctx.i64_type, ptr, "move")
                    .unwrap()
                    .into_int_value();
                self.stack.push(val);
            }
            Bytecode::StLoc(idx) => {
                let val = self.pop()?;
                let ptr = self.locals[*idx as usize];
                self.ctx.builder.build_store(ptr, val).unwrap();
            }
            Bytecode::LdU64(imm) => {
                let val = self.ctx.i64_type.const_int(*imm, false);
                self.stack.push(val);
            }
            Bytecode::Add => self.int_binop(BinOp::Add)?,
            Bytecode::Sub => self.int_binop(BinOp::Sub)?,
            Bytecode::Mul => self.int_binop(BinOp::Mul)?,
            Bytecode::Div => self.int_binop(BinOp::Div)?,
            Bytecode::Mod => self.int_binop(BinOp::Mod)?,
            Bytecode::Ret => {
                if self.function.get_type().get_return_type().is_some() {
                    let val = self.pop()?;
                    self.ctx.builder.build_return(Some(&val)).unwrap();
                } else {
                    self.ctx.builder.build_return(None).unwrap();
                }
            }
            other => {
                return Err(CompileError::UnsupportedBytecode(format!("{:?}", other)));
            }
        }
        Ok(())
    }

    fn pop(&mut self) -> Result<IntValue<'ctx>, CompileError> {
        self.stack
            .pop()
            .ok_or_else(|| CompileError::Llvm("stack underflow".into()))
    }

    fn int_binop(&mut self, op: BinOp) -> Result<(), CompileError> {
        let rhs = self.pop()?;
        let lhs = self.pop()?;
        let result = match op {
            BinOp::Add => self.ctx.builder.build_int_add(lhs, rhs, "add").unwrap(),
            BinOp::Sub => self.ctx.builder.build_int_sub(lhs, rhs, "sub").unwrap(),
            BinOp::Mul => self.ctx.builder.build_int_mul(lhs, rhs, "mul").unwrap(),
            BinOp::Div => self
                .ctx
                .builder
                .build_int_unsigned_div(lhs, rhs, "div")
                .unwrap(),
            BinOp::Mod => self
                .ctx
                .builder
                .build_int_unsigned_rem(lhs, rhs, "mod")
                .unwrap(),
        };
        self.stack.push(result);
        Ok(())
    }
}

enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

/// Lower a single function definition into the LLVM module.
///
/// Resolves the function handle, builds the LLVM function signature, creates
/// the function, and lowers all bytecodes.
pub fn lower_function<'ctx>(
    ctx: &LlvmContext<'ctx>,
    module: &move_binary_format::CompiledModule,
    func_def: &FunctionDefinition,
) -> Result<(), CompileError> {
    let code = func_def.code.as_ref().ok_or(CompileError::NoCode)?;
    let handle = module.function_handle_at(func_def.function);
    let name = module.identifier_at(handle.name).as_str();

    let param_sig = module.signature_at(handle.parameters);
    let return_sig = module.signature_at(handle.return_);
    let local_sig = module.signature_at(code.locals);

    // Build LLVM function type
    let param_llvm_types: Vec<_> = param_sig
        .0
        .iter()
        .map(|tok| lower_type(ctx, tok).map(|t| t.into()))
        .collect::<Result<_, _>>()?;

    let fn_type = if return_sig.0.is_empty() {
        ctx.context.void_type().fn_type(&param_llvm_types, false)
    } else if return_sig.0.len() == 1 {
        let ret_type = lower_type(ctx, &return_sig.0[0])?;
        ret_type.fn_type(&param_llvm_types, false)
    } else {
        return Err(CompileError::UnsupportedType(
            "multi-value return".to_string(),
        ));
    };

    let function = ctx.module.add_function(name, fn_type, None);

    let mut lowering = FunctionLowering::new(ctx, function, &param_sig.0, &local_sig.0)?;
    lowering.lower_code(code)?;

    Ok(())
}
