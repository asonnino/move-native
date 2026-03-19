// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use move_stackless_bytecode::stackless_bytecode::Constant;

use super::state::{CallSiteValueExt, FunctionState};
use crate::error::{CompileError, CompileResult};

/// Emits LLVM IR for Move constant values.
pub(crate) struct ConstantEmitter<'a, 'b, 'ctx> {
    state: &'a FunctionState<'b, 'ctx>,
}

impl<'a, 'b, 'ctx> ConstantEmitter<'a, 'b, 'ctx> {
    pub(super) fn new(state: &'a FunctionState<'b, 'ctx>) -> Self {
        Self { state }
    }

    pub(super) fn emit(&self, destination: usize, constant: &Constant) -> CompileResult<()> {
        let llvm = &self.state.ctx;
        let val = match constant {
            Constant::Bool(v) => llvm.i8_type.const_int(*v as u64, false).into(),
            Constant::U8(v) => llvm.i8_type.const_int(*v as u64, false).into(),
            Constant::U16(v) => llvm.i16_type.const_int(*v as u64, false).into(),
            Constant::U32(v) => llvm.i32_type.const_int(*v as u64, false).into(),
            Constant::U64(v) => llvm.i64_type.const_int(*v, false).into(),
            Constant::U128(v) => {
                let words = [*v as u64, (*v >> 64) as u64];
                llvm.i128_type.const_int_arbitrary_precision(&words).into()
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
                llvm.i256_type.const_int_arbitrary_precision(&words).into()
            }
            Constant::U256(v) => {
                let (hi, lo) = v.into_words();
                let words: [u64; 4] = [lo as u64, (lo >> 64) as u64, hi as u64, (hi >> 64) as u64];
                llvm.i256_type.const_int_arbitrary_precision(&words).into()
            }
            Constant::ByteArray(bytes) => {
                let id = self.state.next_const_id();
                let global = self
                    .state
                    .emit_const_global(&format!("const_bytes_{id}"), bytes);
                let func = self.state.declare_external(
                    "__move_rt_const_vec_u8",
                    llvm.ptr_type
                        .fn_type(&[llvm.ptr_type.into(), llvm.i64_type.into()], false),
                );
                let ptr = global.as_pointer_value();
                let len = llvm.i64_type.const_int(bytes.len() as u64, false);
                let call =
                    llvm.builder
                        .build_call(func, &[ptr.into(), len.into()], "const_vec_u8")?;
                call.into_basic_value()?
            }
            Constant::AddressArray(addresses) => {
                let id = self.state.next_const_id();
                let buf = Self::serialize_address_array(addresses);
                let global = self
                    .state
                    .emit_const_global(&format!("const_addrs_{id}"), &buf);
                let func = self.state.declare_external(
                    "__move_rt_const_vec_address",
                    llvm.ptr_type
                        .fn_type(&[llvm.ptr_type.into(), llvm.i64_type.into()], false),
                );
                let ptr = global.as_pointer_value();
                let count = llvm.i64_type.const_int(addresses.len() as u64, false);
                let call =
                    llvm.builder
                        .build_call(func, &[ptr.into(), count.into()], "const_vec_addr")?;
                call.into_basic_value()?
            }
            Constant::Vector(elements) => {
                if elements.is_empty() {
                    let function_type = llvm.ptr_type.fn_type(
                        &[
                            llvm.ptr_type.into(),
                            llvm.i64_type.into(),
                            llvm.i64_type.into(),
                        ],
                        false,
                    );
                    let function = self
                        .state
                        .declare_external("__move_rt_const_vec", function_type);
                    let null = llvm.ptr_type.const_null();
                    let zero = llvm.i64_type.const_zero();
                    let call = llvm.builder.build_call(
                        function,
                        &[null.into(), zero.into(), zero.into()],
                        "const_vec_empty",
                    )?;
                    return self.state.store(destination, call.into_basic_value()?);
                }
                // Vector of ByteArrays → vector<vector<u8>>, needs a dedicated
                // runtime helper because elements are variable-length.
                if matches!(elements[0], Constant::ByteArray(_)) {
                    let buf = Self::serialize_byte_array_vector(elements)?;
                    let id = self.state.next_const_id();
                    let global = self
                        .state
                        .emit_const_global(&format!("const_vec_bytes_{id}"), &buf);
                    let function_type = llvm
                        .ptr_type
                        .fn_type(&[llvm.ptr_type.into(), llvm.i64_type.into()], false);
                    let function = self
                        .state
                        .declare_external("__move_rt_const_vec_vec_u8", function_type);
                    let ptr = global.as_pointer_value();
                    let count = llvm.i64_type.const_int(elements.len() as u64, false);
                    let call = llvm.builder.build_call(
                        function,
                        &[ptr.into(), count.into()],
                        "const_vec_vec_u8",
                    )?;
                    call.into_basic_value()?
                } else {
                    let function_type = llvm.ptr_type.fn_type(
                        &[
                            llvm.ptr_type.into(),
                            llvm.i64_type.into(),
                            llvm.i64_type.into(),
                        ],
                        false,
                    );
                    let (elem_size, buf) = Self::serialize_scalar_vector(elements)?;
                    let id = self.state.next_const_id();
                    let global = self
                        .state
                        .emit_const_global(&format!("const_vec_{id}"), &buf);
                    let function = self
                        .state
                        .declare_external("__move_rt_const_vec", function_type);
                    let ptr = global.as_pointer_value();
                    let count = llvm.i64_type.const_int(elements.len() as u64, false);
                    let esz = llvm.i64_type.const_int(elem_size as u64, false);
                    let call = llvm.builder.build_call(
                        function,
                        &[ptr.into(), count.into(), esz.into()],
                        "const_vec",
                    )?;
                    call.into_basic_value()?
                }
            }
        };
        self.state.store(destination, val)
    }

    /// Serialize an `AddressArray` into a flat buffer of 32-byte little-endian addresses.
    fn serialize_address_array(addresses: &[num_bigint::BigUint]) -> Vec<u8> {
        let mut buf = Vec::with_capacity(addresses.len() * 32);
        for addr in addresses {
            let bytes = addr.to_bytes_le();
            let mut padded = [0u8; 32];
            let len = bytes.len().min(32);
            padded[..len].copy_from_slice(&bytes[..len]);
            buf.extend_from_slice(&padded);
        }
        buf
    }

    /// Serialize a `Vector` of `ByteArray` constants into a length-prefixed format.
    ///
    /// Layout: for each element, `[len: u64 LE, bytes...]`.
    /// The runtime reads `count` length-prefixed entries to build `vector<vector<u8>>`.
    fn serialize_byte_array_vector(elements: &[Constant]) -> CompileResult<Vec<u8>> {
        let mut buf = Vec::new();
        for element in elements {
            match element {
                Constant::ByteArray(bytes) => {
                    buf.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
                    buf.extend_from_slice(bytes);
                }
                other => return Err(CompileError::unsupported(other)),
            }
        }
        Ok(buf)
    }

    /// Serialize a `Vector` of scalar constants into a flat byte buffer.
    ///
    /// Returns `(element_size, flat_buffer)`.
    fn serialize_scalar_vector(elements: &[Constant]) -> CompileResult<(usize, Vec<u8>)> {
        let element_size = match &elements[0] {
            Constant::Bool(_) | Constant::U8(_) => 1,
            Constant::U16(_) => 2,
            Constant::U32(_) => 4,
            Constant::U64(_) => 8,
            Constant::U128(_) => 16,
            Constant::U256(_) | Constant::Address(_) => 32,
            other => return Err(CompileError::unsupported(other)),
        };

        let mut buf = Vec::with_capacity(elements.len() * element_size);
        for element in elements {
            match element {
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
                other => return Err(CompileError::unsupported(other)),
            }
        }
        Ok((element_size, buf))
    }
}

#[cfg(test)]
mod tests {
    use move_stackless_bytecode::stackless_bytecode::Constant;
    use num_bigint::BigUint;

    use super::ConstantEmitter;
    use crate::compiler::Compiler;
    use crate::module::CompiledModuleBuilder;
    use crate::target::Target;

    #[test]
    fn address_single() {
        let addr = BigUint::from(0x42u64);
        let buf = ConstantEmitter::serialize_address_array(&[addr]);
        assert_eq!(buf.len(), 32);
        assert_eq!(buf[0], 0x42);
        assert!(buf[1..].iter().all(|&b| b == 0));
    }

    #[test]
    fn address_multiple() {
        let a = BigUint::from(1u64);
        let b = BigUint::from(2u64);
        let buf = ConstantEmitter::serialize_address_array(&[a, b]);
        assert_eq!(buf.len(), 64);
        assert_eq!(buf[0], 1);
        assert_eq!(buf[32], 2);
    }

    #[test]
    fn address_zero() {
        let buf = ConstantEmitter::serialize_address_array(&[BigUint::ZERO]);
        assert_eq!(buf, vec![0u8; 32]);
    }

    #[test]
    fn address_max() {
        let addr = BigUint::from_bytes_le(&[0xFF; 32]);
        let buf = ConstantEmitter::serialize_address_array(&[addr]);
        assert_eq!(buf, vec![0xFF; 32]);
    }

    #[test]
    fn address_small_is_le_padded() {
        let addr = BigUint::from(1u64);
        let buf = ConstantEmitter::serialize_address_array(&[addr]);
        let mut expected = [0u8; 32];
        expected[0] = 1;
        assert_eq!(buf, expected);
    }

    #[test]
    fn address_empty_slice() {
        let buf = ConstantEmitter::serialize_address_array(&[]);
        assert!(buf.is_empty());
    }

    #[test]
    fn scalar_vec_bool() {
        let elements = vec![Constant::Bool(true), Constant::Bool(false)];
        let (size, buf) = ConstantEmitter::serialize_scalar_vector(&elements).unwrap();
        assert_eq!(size, 1);
        assert_eq!(buf, [1, 0]);
    }

    #[test]
    fn scalar_vec_u8() {
        let elements = vec![Constant::U8(0xFF), Constant::U8(0x42)];
        let (size, buf) = ConstantEmitter::serialize_scalar_vector(&elements).unwrap();
        assert_eq!(size, 1);
        assert_eq!(buf, [0xFF, 0x42]);
    }

    #[test]
    fn scalar_vec_u16() {
        let elements = vec![Constant::U16(0x1234)];
        let (size, buf) = ConstantEmitter::serialize_scalar_vector(&elements).unwrap();
        assert_eq!(size, 2);
        assert_eq!(buf, [0x34, 0x12]);
    }

    #[test]
    fn scalar_vec_u32() {
        let elements = vec![Constant::U32(0xDEADBEEF)];
        let (size, buf) = ConstantEmitter::serialize_scalar_vector(&elements).unwrap();
        assert_eq!(size, 4);
        assert_eq!(buf, [0xEF, 0xBE, 0xAD, 0xDE]);
    }

    #[test]
    fn scalar_vec_u64() {
        let elements = vec![Constant::U64(0x0102030405060708)];
        let (size, buf) = ConstantEmitter::serialize_scalar_vector(&elements).unwrap();
        assert_eq!(size, 8);
        assert_eq!(buf, [0x08, 0x07, 0x06, 0x05, 0x04, 0x03, 0x02, 0x01]);
    }

    #[test]
    fn scalar_vec_u128() {
        let val: u128 = 0x0102030405060708_090A0B0C0D0E0F10;
        let elements = vec![Constant::U128(val)];
        let (size, buf) = ConstantEmitter::serialize_scalar_vector(&elements).unwrap();
        assert_eq!(size, 16);
        assert_eq!(buf, val.to_le_bytes());
    }

    #[test]
    fn scalar_vec_u256() {
        let val = ethnum::U256::from(1u64);
        let elements = vec![Constant::U256(val)];
        let (size, buf) = ConstantEmitter::serialize_scalar_vector(&elements).unwrap();
        assert_eq!(size, 32);
        // lo = 1, hi = 0 → first 16 bytes are 1_u128.to_le, next 16 are zeros
        let (hi, lo) = val.into_words();
        let mut expected = Vec::new();
        expected.extend_from_slice(&lo.to_le_bytes());
        expected.extend_from_slice(&hi.to_le_bytes());
        assert_eq!(buf, expected);
    }

    #[test]
    fn scalar_vec_address() {
        let addr = BigUint::from(0xABu64);
        let elements = vec![Constant::Address(addr)];
        let (size, buf) = ConstantEmitter::serialize_scalar_vector(&elements).unwrap();
        assert_eq!(size, 32);
        assert_eq!(buf[0], 0xAB);
        assert!(buf[1..].iter().all(|&b| b == 0));
    }

    #[test]
    fn scalar_vec_unsupported() {
        let elements = vec![Constant::ByteArray(vec![1, 2, 3])];
        let result = ConstantEmitter::serialize_scalar_vector(&elements);
        assert!(result.is_err());
    }

    #[test]
    fn compile_byte_array_constant() {
        use move_binary_format::file_format::{
            Bytecode, ConstantPoolIndex,
            SignatureToken::{U8, Vector},
        };

        let hello: Vec<u8> = b"Hello".to_vec();
        let mut bcs_data = Vec::new();
        bcs_data.push(hello.len() as u8);
        bcs_data.extend_from_slice(&hello);

        let vec_u8 = Vector(Box::new(U8));
        let module = CompiledModuleBuilder::new()
            .constant(vec_u8.clone(), bcs_data)
            .function(
                "get_bytes",
                vec![],
                vec![vec_u8.clone()],
                vec![vec_u8],
                vec![
                    Bytecode::LdConst(ConstantPoolIndex(0)),
                    Bytecode::StLoc(0),
                    Bytecode::MoveLoc(0),
                    Bytecode::Ret,
                ],
            )
            .build();
        let asm = Compiler::compile_module(&Target::host(), &module).unwrap();
        assert!(
            asm.contains("__move_rt_const_vec_u8"),
            "missing runtime call\n{asm}"
        );
    }

    #[test]
    fn compile_address_constant() {
        use move_binary_format::file_format::{Bytecode, ConstantPoolIndex, SignatureToken};

        let mut addr_bytes = [0u8; 32];
        addr_bytes[31] = 0x42;

        let module = CompiledModuleBuilder::new()
            .constant(SignatureToken::Address, addr_bytes.to_vec())
            .function(
                "load_addr",
                vec![],
                vec![SignatureToken::Address],
                vec![SignatureToken::Address],
                vec![
                    Bytecode::LdConst(ConstantPoolIndex(0)),
                    Bytecode::StLoc(0),
                    Bytecode::MoveLoc(0),
                    Bytecode::Ret,
                ],
            )
            .build();
        let asm = Compiler::compile_module(&Target::host(), &module).unwrap();
        assert!(asm.contains("0x0_M_load_addr"), "missing symbol\n{asm}");
    }

    #[test]
    fn byte_array_vec_single() {
        let elements = vec![Constant::ByteArray(vec![0x48, 0x49])];
        let buf = ConstantEmitter::serialize_byte_array_vector(&elements).unwrap();
        let mut expected = Vec::new();
        expected.extend_from_slice(&2u64.to_le_bytes());
        expected.extend_from_slice(&[0x48, 0x49]);
        assert_eq!(buf, expected);
    }

    #[test]
    fn byte_array_vec_multiple() {
        let elements = vec![
            Constant::ByteArray(vec![1]),
            Constant::ByteArray(vec![2, 3, 4]),
        ];
        let buf = ConstantEmitter::serialize_byte_array_vector(&elements).unwrap();
        let mut expected = Vec::new();
        expected.extend_from_slice(&1u64.to_le_bytes());
        expected.push(1);
        expected.extend_from_slice(&3u64.to_le_bytes());
        expected.extend_from_slice(&[2, 3, 4]);
        assert_eq!(buf, expected);
    }

    #[test]
    fn byte_array_vec_empty_element() {
        let elements = vec![Constant::ByteArray(vec![])];
        let buf = ConstantEmitter::serialize_byte_array_vector(&elements).unwrap();
        assert_eq!(buf, 0u64.to_le_bytes());
    }

    #[test]
    fn byte_array_vec_rejects_non_byte_array() {
        let elements = vec![Constant::ByteArray(vec![1]), Constant::U8(2)];
        assert!(ConstantEmitter::serialize_byte_array_vector(&elements).is_err());
    }

    #[test]
    fn compile_vec_vec_u8_constant() {
        use move_binary_format::file_format::{
            Bytecode, ConstantPoolIndex,
            SignatureToken::{U8, Vector},
        };

        // BCS for vector<vector<u8>>: outer length, then each inner vec as length-prefixed bytes
        let inner1: Vec<u8> = vec![0xAA, 0xBB];
        let inner2: Vec<u8> = vec![0xCC];
        let mut bcs_data = Vec::new();
        bcs_data.push(2u8); // 2 elements
        bcs_data.push(inner1.len() as u8);
        bcs_data.extend_from_slice(&inner1);
        bcs_data.push(inner2.len() as u8);
        bcs_data.extend_from_slice(&inner2);

        let vec_vec_u8 = Vector(Box::new(Vector(Box::new(U8))));
        let module = CompiledModuleBuilder::new()
            .constant(vec_vec_u8.clone(), bcs_data)
            .function(
                "get_vecs",
                vec![],
                vec![vec_vec_u8.clone()],
                vec![vec_vec_u8],
                vec![
                    Bytecode::LdConst(ConstantPoolIndex(0)),
                    Bytecode::StLoc(0),
                    Bytecode::MoveLoc(0),
                    Bytecode::Ret,
                ],
            )
            .build();
        let asm = Compiler::compile_module(&Target::host(), &module).unwrap();
        assert!(
            asm.contains("__move_rt_const_vec_vec_u8"),
            "missing runtime call\n{asm}"
        );
    }

    #[test]
    fn compile_vector_u64_constant() {
        use move_binary_format::file_format::{
            Bytecode, ConstantPoolIndex,
            SignatureToken::{U64, Vector},
        };

        let elems: Vec<u64> = vec![10, 20, 30];
        let mut bcs_data = Vec::new();
        bcs_data.push(elems.len() as u8);
        for e in &elems {
            bcs_data.extend_from_slice(&e.to_le_bytes());
        }

        let vec_u64 = Vector(Box::new(U64));
        let module = CompiledModuleBuilder::new()
            .constant(vec_u64.clone(), bcs_data)
            .function(
                "get_vec",
                vec![],
                vec![vec_u64.clone()],
                vec![vec_u64],
                vec![
                    Bytecode::LdConst(ConstantPoolIndex(0)),
                    Bytecode::StLoc(0),
                    Bytecode::MoveLoc(0),
                    Bytecode::Ret,
                ],
            )
            .build();
        let asm = Compiler::compile_module(&Target::host(), &module).unwrap();
        assert!(
            asm.contains("__move_rt_const_vec"),
            "missing runtime call\n{asm}"
        );
    }
}
