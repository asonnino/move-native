use inkwell::types::IntType;
use move_binary_format::file_format::SignatureToken;

use crate::context::LlvmContext;
use crate::error::CompileError;

/// Lower a Move `SignatureToken` to an LLVM integer type.
///
/// Milestone 1 supports `U64` only; other integer widths will be added later.
pub fn lower_type<'ctx>(
    ctx: &LlvmContext<'ctx>,
    token: &SignatureToken,
) -> Result<IntType<'ctx>, CompileError> {
    match token {
        SignatureToken::U8 => Ok(ctx.i8_type),
        SignatureToken::U16 => Ok(ctx.i16_type),
        SignatureToken::U32 => Ok(ctx.i32_type),
        SignatureToken::U64 => Ok(ctx.i64_type),
        SignatureToken::U128 => Ok(ctx.i128_type),
        SignatureToken::U256 => Ok(ctx.i256_type),
        SignatureToken::Bool => Ok(ctx.i8_type),
        other => Err(CompileError::UnsupportedType(format!("{:?}", other))),
    }
}
