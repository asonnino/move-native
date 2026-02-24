// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::values::BasicValueEnum;
use move_stackless_bytecode::stackless_bytecode::Constant;

use super::FunctionLowering;
use crate::error::{CompileError, CompileResult};

/// Emits LLVM IR for Move constant values.
pub(crate) struct ConstantEmitter<'a, 'b, 'ctx> {
    fl: &'a FunctionLowering<'b, 'ctx>,
}

impl<'a, 'b, 'ctx> ConstantEmitter<'a, 'b, 'ctx> {
    pub fn new(fl: &'a FunctionLowering<'b, 'ctx>) -> Self {
        Self { fl }
    }

    pub fn lower(&self, constant: &Constant) -> CompileResult<BasicValueEnum<'ctx>> {
        let ctx = &self.fl.compiler.ctx;
        match constant {
            Constant::Bool(v) => Ok(ctx.i8_type.const_int(*v as u64, false).into()),
            Constant::U8(v) => Ok(ctx.i8_type.const_int(*v as u64, false).into()),
            Constant::U16(v) => Ok(ctx.i16_type.const_int(*v as u64, false).into()),
            Constant::U32(v) => Ok(ctx.i32_type.const_int(*v as u64, false).into()),
            Constant::U64(v) => Ok(ctx.i64_type.const_int(*v, false).into()),
            Constant::U128(v) => {
                let words = [*v as u64, (*v >> 64) as u64];
                Ok(ctx.i128_type.const_int_arbitrary_precision(&words).into())
            }
            Constant::Address(big) => {
                let bytes = big.to_bytes_le();
                let mut buf = [0u8; 32];
                let len = bytes.len().min(32);
                buf[..len].copy_from_slice(&bytes[..len]);
                let words: [u64; 4] = [
                    u64::from_le_bytes(buf[0..8].try_into().unwrap()),
                    u64::from_le_bytes(buf[8..16].try_into().unwrap()),
                    u64::from_le_bytes(buf[16..24].try_into().unwrap()),
                    u64::from_le_bytes(buf[24..32].try_into().unwrap()),
                ];
                Ok(ctx.i256_type.const_int_arbitrary_precision(&words).into())
            }
            Constant::U256(v) => {
                let (hi, lo) = v.into_words();
                let words: [u64; 4] = [lo as u64, (lo >> 64) as u64, hi as u64, (hi >> 64) as u64];
                Ok(ctx.i256_type.const_int_arbitrary_precision(&words).into())
            }
            Constant::ByteArray(bytes) => {
                let id = self.fl.next_const_id();
                let global = self
                    .fl
                    .emit_const_global(&format!("const_bytes_{id}"), bytes);
                let func = self.fl.compiler.get_or_declare_extern(
                    "__move_rt_const_vec_u8",
                    ctx.ptr_type
                        .fn_type(&[ctx.ptr_type.into(), ctx.i64_type.into()], false),
                );
                let ptr = global.as_pointer_value();
                let len = ctx.i64_type.const_int(bytes.len() as u64, false);
                let call = ctx
                    .builder
                    .build_call(func, &[ptr.into(), len.into()], "const_vec_u8")
                    .unwrap();
                match call.try_as_basic_value() {
                    inkwell::values::ValueKind::Basic(v) => Ok(v),
                    _ => unreachable!("const vec runtime function must return a value"),
                }
            }
            Constant::AddressArray(addrs) => {
                let id = self.fl.next_const_id();
                let buf = serialize_address_array(addrs);
                let global = self
                    .fl
                    .emit_const_global(&format!("const_addrs_{id}"), &buf);
                let func = self.fl.compiler.get_or_declare_extern(
                    "__move_rt_const_vec_address",
                    ctx.ptr_type
                        .fn_type(&[ctx.ptr_type.into(), ctx.i64_type.into()], false),
                );
                let ptr = global.as_pointer_value();
                let count = ctx.i64_type.const_int(addrs.len() as u64, false);
                let call = ctx
                    .builder
                    .build_call(func, &[ptr.into(), count.into()], "const_vec_addr")
                    .unwrap();
                match call.try_as_basic_value() {
                    inkwell::values::ValueKind::Basic(v) => Ok(v),
                    _ => unreachable!("const vec runtime function must return a value"),
                }
            }
            Constant::Vector(elems) => {
                let fn_type = ctx.ptr_type.fn_type(
                    &[
                        ctx.ptr_type.into(),
                        ctx.i64_type.into(),
                        ctx.i64_type.into(),
                    ],
                    false,
                );
                if elems.is_empty() {
                    let func = self
                        .fl
                        .compiler
                        .get_or_declare_extern("__move_rt_const_vec", fn_type);
                    let null = ctx.ptr_type.const_null();
                    let zero = ctx.i64_type.const_zero();
                    let call = ctx
                        .builder
                        .build_call(
                            func,
                            &[null.into(), zero.into(), zero.into()],
                            "const_vec_empty",
                        )
                        .unwrap();
                    return match call.try_as_basic_value() {
                        inkwell::values::ValueKind::Basic(v) => Ok(v),
                        _ => unreachable!("const vec runtime function must return a value"),
                    };
                }
                let (elem_size, buf) = serialize_scalar_vector(elems)?;
                let id = self.fl.next_const_id();
                let global = self.fl.emit_const_global(&format!("const_vec_{id}"), &buf);
                let func = self
                    .fl
                    .compiler
                    .get_or_declare_extern("__move_rt_const_vec", fn_type);
                let ptr = global.as_pointer_value();
                let count = ctx.i64_type.const_int(elems.len() as u64, false);
                let esz = ctx.i64_type.const_int(elem_size as u64, false);
                let call = ctx
                    .builder
                    .build_call(func, &[ptr.into(), count.into(), esz.into()], "const_vec")
                    .unwrap();
                match call.try_as_basic_value() {
                    inkwell::values::ValueKind::Basic(v) => Ok(v),
                    _ => unreachable!("const vec runtime function must return a value"),
                }
            }
        }
    }
}

/// Serialize an `AddressArray` into a flat buffer of 32-byte little-endian addresses.
pub(super) fn serialize_address_array(addrs: &[num_bigint::BigUint]) -> Vec<u8> {
    let mut buf = Vec::with_capacity(addrs.len() * 32);
    for addr in addrs {
        let bytes = addr.to_bytes_le();
        let mut padded = [0u8; 32];
        let len = bytes.len().min(32);
        padded[..len].copy_from_slice(&bytes[..len]);
        buf.extend_from_slice(&padded);
    }
    buf
}

/// Serialize a `Vector` of scalar constants into a flat byte buffer.
pub(super) fn serialize_scalar_vector(elems: &[Constant]) -> CompileResult<(usize, Vec<u8>)> {
    let elem_size = match &elems[0] {
        Constant::Bool(_) | Constant::U8(_) => 1,
        Constant::U16(_) => 2,
        Constant::U32(_) => 4,
        Constant::U64(_) => 8,
        Constant::U128(_) => 16,
        Constant::U256(_) | Constant::Address(_) => 32,
        other => {
            return Err(CompileError::UnsupportedOperation(format!(
                "vector constant with non-scalar element: {:?}",
                other
            )));
        }
    };

    let mut buf = Vec::with_capacity(elems.len() * elem_size);
    for elem in elems {
        match elem {
            Constant::Bool(v) => buf.push(*v as u8),
            Constant::U8(v) => buf.push(*v),
            Constant::U16(v) => buf.extend_from_slice(&v.to_le_bytes()),
            Constant::U32(v) => buf.extend_from_slice(&v.to_le_bytes()),
            Constant::U64(v) => buf.extend_from_slice(&v.to_le_bytes()),
            Constant::U128(v) => buf.extend_from_slice(&v.to_le_bytes()),
            Constant::U256(v) => {
                let (hi, lo) = v.into_words();
                buf.extend_from_slice(&lo.to_le_bytes());
                buf.extend_from_slice(&hi.to_le_bytes());
            }
            Constant::Address(big) => {
                let bytes = big.to_bytes_le();
                let mut padded = [0u8; 32];
                let len = bytes.len().min(32);
                padded[..len].copy_from_slice(&bytes[..len]);
                buf.extend_from_slice(&padded);
            }
            other => {
                return Err(CompileError::UnsupportedOperation(format!(
                    "vector constant with non-scalar element: {:?}",
                    other
                )));
            }
        }
    }
    Ok((elem_size, buf))
}
