// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the Move-to-LLVM compiler.
//!
//! Tests are organized into:
//! - **Kitchen sink**: one large module exercising interactions between features
//! - **Individual features**: compact tests for specific operations
//! - **Cross-module / vector**: tests requiring multiple modules or native stubs

mod common;

use common::*;
use move_binary_format::CompiledModule;
use move_binary_format::file_format::*;
use move_core_types::account_address::AccountAddress;
use move_core_types::identifier::Identifier;
use move_to_llvm::module::CompiledModuleBuilder;
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
use std::ffi::CString;
use std::process::Command;
use tempfile::TempDir;

// ===================================================================
// Kitchen Sink: one module exercising interactions between all features.
// See `CompiledModuleBuilder::all_features()` for the full definition.
// ===================================================================

#[test]
fn all_features_compiles() {
    let module = CompiledModuleBuilder::all_features();
    let asm = compile_module_checked(&module);

    // Verify key symbols are present
    for name in &[
        "make_point",
        "sum_point",
        "round_trip",
        "identity",
        "call_identity",
        "sum_loop",
        "swap_fields",
        "swap_u64",
        "checked_sub",
        "low_byte",
        "forty_two",
        "integration_test",
    ] {
        assert!(
            asm.contains(name),
            "assembly should contain '{name}'\nassembly:\n{asm}"
        );
    }
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn all_features_round_trip() {
    let module = CompiledModuleBuilder::all_features();
    let (exec, obj_path, _dir) = compile_and_load_with_symbols(&module);
    let offset = find_symbol_offset(&obj_path, "round_trip");

    type RoundTripFn = unsafe extern "C" fn(u64, u64) -> u64;
    let f: RoundTripFn = unsafe { exec.as_fn_at(offset as usize) };

    assert_eq!(unsafe { f(3, 7) }, 10);
    assert_eq!(unsafe { f(0, 0) }, 0);
    assert_eq!(unsafe { f(100, 200) }, 300);
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn all_features_sum_loop() {
    let module = CompiledModuleBuilder::all_features();
    let (exec, obj_path, _dir) = compile_and_load_with_symbols(&module);
    let offset = find_symbol_offset(&obj_path, "sum_loop");

    type SumFn = unsafe extern "C" fn(u64) -> u64;
    let f: SumFn = unsafe { exec.as_fn_at(offset as usize) };

    // sum_loop(n) = sum of (i + i+1) for i=0..n-1 = n^2
    assert_eq!(unsafe { f(0) }, 0);
    assert_eq!(unsafe { f(1) }, 1);
    assert_eq!(unsafe { f(5) }, 25);
    assert_eq!(unsafe { f(10) }, 100);
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn all_features_call_identity() {
    let module = CompiledModuleBuilder::all_features();
    let (exec, obj_path, _dir) = compile_and_load_with_symbols(&module);
    let offset = find_symbol_offset(&obj_path, "call_identity");

    type IdFn = unsafe extern "C" fn(u64) -> u64;
    let f: IdFn = unsafe { exec.as_fn_at(offset as usize) };

    assert_eq!(unsafe { f(42) }, 42);
    assert_eq!(unsafe { f(0) }, 0);
    assert_eq!(unsafe { f(u64::MAX) }, u64::MAX);
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn all_features_swap_u64() {
    let module = CompiledModuleBuilder::all_features();
    let (exec, obj_path, _dir) = compile_and_load_with_symbols(&module);
    let offset = find_symbol_offset(&obj_path, "swap_u64");

    // swap_u64 returns (b, a) — in the AAPCS64 ABI, first return in x0, second in x1.
    // We test via a wrapper: the "integration_test" function uses swap_u64 internally.
    // Directly testing multi-return requires reading x0 and x1 which is platform-specific.
    // Instead, verify it compiles and the integration_test exercises it.

    // For direct test: swap_u64(10, 20) → first return = 20 (in x0)
    type SwapFn = unsafe extern "C" fn(u64, u64) -> u64;
    let f: SwapFn = unsafe { exec.as_fn_at(offset as usize) };
    // First return value (x0) should be b=20
    assert_eq!(unsafe { f(10, 20) }, 20);
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn all_features_integration_test() {
    let module = CompiledModuleBuilder::all_features();
    let (exec, obj_path, _dir) = compile_and_load_with_symbols(&module);
    let offset = find_symbol_offset(&obj_path, "integration_test");

    type IntegrationFn = unsafe extern "C" fn(u64) -> u64;
    let f: IntegrationFn = unsafe { exec.as_fn_at(offset as usize) };

    // integration_test(n) = n^2 (via sum_loop → call_identity → swap_u64 → checked_sub)
    assert_eq!(unsafe { f(0) }, 0);
    assert_eq!(unsafe { f(1) }, 1);
    assert_eq!(unsafe { f(5) }, 25);
    assert_eq!(unsafe { f(10) }, 100);
    assert_eq!(unsafe { f(100) }, 10000);
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn all_features_forty_two() {
    let module = CompiledModuleBuilder::all_features();
    let (exec, obj_path, _dir) = compile_and_load_with_symbols(&module);
    let offset = find_symbol_offset(&obj_path, "forty_two");

    type ConstFn = unsafe extern "C" fn() -> u64;
    let f: ConstFn = unsafe { exec.as_fn_at(offset as usize) };
    assert_eq!(unsafe { f() }, 42);
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn all_features_low_byte() {
    let module = CompiledModuleBuilder::all_features();
    let (exec, obj_path, _dir) = compile_and_load_with_symbols(&module);
    let offset = find_symbol_offset(&obj_path, "low_byte");

    type CastFn = unsafe extern "C" fn(u64) -> u8;
    let f: CastFn = unsafe { exec.as_fn_at(offset as usize) };
    assert_eq!(unsafe { f(258) }, 2);
    assert_eq!(unsafe { f(42) }, 42);
}

// ===================================================================
// Individual feature tests (compact, builder-based)
// ===================================================================

// ---------------------------------------------------------------------------
// Arithmetic + comparisons + bitwise
// ---------------------------------------------------------------------------

#[test]
fn compile_all_arithmetic_ops() {
    use Bytecode::*;
    use SignatureToken::*;

    // Binary arithmetic ops: (u64, u64) -> u64
    for (name, op) in [
        ("add", Add),
        ("sub", Sub),
        ("mul", Mul),
        ("div", Div),
        ("mod_", Mod),
        ("bitand", BitAnd),
        ("bitor", BitOr),
        ("xor", Xor),
    ] {
        let module = CompiledModuleBuilder::new()
            .function(
                name,
                vec![U64, U64],
                vec![U64],
                vec![],
                vec![CopyLoc(0), CopyLoc(1), op, Ret],
            )
            .build();
        move_to_llvm::compile_module(&move_to_llvm::Target::Aarch64, &module)
            .unwrap_or_else(|e| panic!("{name} failed: {e}"));
    }

    // Comparisons: (u64, u64) -> bool
    for (name, op) in [
        ("lt", Lt),
        ("gt", Gt),
        ("le", Le),
        ("ge", Ge),
        ("eq", Eq),
        ("neq", Neq),
    ] {
        let module = CompiledModuleBuilder::new()
            .function(
                name,
                vec![U64, U64],
                vec![Bool],
                vec![],
                vec![CopyLoc(0), CopyLoc(1), op, Ret],
            )
            .build();
        move_to_llvm::compile_module(&move_to_llvm::Target::Aarch64, &module)
            .unwrap_or_else(|e| panic!("{name} failed: {e}"));
    }

    // Shifts: (u64, u8) -> u64
    for (name, op) in [("shl", Shl), ("shr", Shr)] {
        let module = CompiledModuleBuilder::new()
            .function(
                name,
                vec![U64, U8],
                vec![U64],
                vec![],
                vec![CopyLoc(0), CopyLoc(1), op, Ret],
            )
            .build();
        move_to_llvm::compile_module(&move_to_llvm::Target::Aarch64, &module)
            .unwrap_or_else(|e| panic!("{name} failed: {e}"));
    }

    // Logical ops: (bool, bool) -> bool
    for (name, op) in [("and", And), ("or", Or)] {
        let module = CompiledModuleBuilder::new()
            .function(
                name,
                vec![Bool, Bool],
                vec![Bool],
                vec![],
                vec![CopyLoc(0), CopyLoc(1), op, Ret],
            )
            .build();
        move_to_llvm::compile_module(&move_to_llvm::Target::Aarch64, &module)
            .unwrap_or_else(|e| panic!("{name} failed: {e}"));
    }

    // Not: (bool) -> bool
    let module = CompiledModuleBuilder::new()
        .function(
            "not",
            vec![Bool],
            vec![Bool],
            vec![],
            vec![CopyLoc(0), Not, Ret],
        )
        .build();
    move_to_llvm::compile_module(&move_to_llvm::Target::Aarch64, &module).expect("not failed");
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_comparisons() {
    use Bytecode::*;
    use SignatureToken::*;

    for (name, op, cases) in [
        ("lt", Lt, vec![(3u64, 4u64, 1u8), (4, 3, 0), (4, 4, 0)]),
        ("gt", Gt, vec![(4, 3, 1), (3, 4, 0), (4, 4, 0)]),
        ("le", Le, vec![(3, 4, 1), (4, 4, 1), (4, 3, 0)]),
        ("ge", Ge, vec![(4, 3, 1), (4, 4, 1), (3, 4, 0)]),
        ("eq", Eq, vec![(4, 4, 1), (3, 4, 0)]),
        ("neq", Neq, vec![(3, 4, 1), (4, 4, 0)]),
    ] {
        let module = CompiledModuleBuilder::new()
            .function(
                name,
                vec![U64, U64],
                vec![Bool],
                vec![],
                vec![CopyLoc(0), CopyLoc(1), op, Ret],
            )
            .build();
        let exec = compile_and_load(&module);
        type CmpFn = unsafe extern "C" fn(u64, u64) -> u8;
        let f: CmpFn = unsafe { exec.as_fn() };

        for (a, b, expected) in &cases {
            let result = unsafe { f(*a, *b) };
            assert_eq!(result, *expected, "{name}({a}, {b}) should be {expected}");
        }
    }
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_bitwise_ops() {
    use Bytecode::*;
    use SignatureToken::*;

    for (name, op, a, b, expected) in [
        ("bitand", BitAnd, 0xFF_u64, 0x0F, 0x0F_u64),
        ("bitor", BitOr, 0xF0, 0x0F, 0xFF),
        ("xor", Xor, 0xFF, 0x0F, 0xF0),
    ] {
        let module = CompiledModuleBuilder::new()
            .function(
                name,
                vec![U64, U64],
                vec![U64],
                vec![],
                vec![CopyLoc(0), CopyLoc(1), op, Ret],
            )
            .build();
        let exec = compile_and_load(&module);
        type BinFn = unsafe extern "C" fn(u64, u64) -> u64;
        let f: BinFn = unsafe { exec.as_fn() };
        let result = unsafe { f(a, b) };
        assert_eq!(result, expected, "{name}(0x{a:X}, 0x{b:X})");
    }
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_shifts() {
    use Bytecode::*;
    use SignatureToken::*;

    for (name, op, val, amt, expected) in
        [("shl", Shl, 1_u64, 4_u8, 16_u64), ("shr", Shr, 256, 4, 16)]
    {
        let module = CompiledModuleBuilder::new()
            .function(
                name,
                vec![U64, U8],
                vec![U64],
                vec![],
                vec![CopyLoc(0), CopyLoc(1), op, Ret],
            )
            .build();
        let exec = compile_and_load(&module);
        type ShiftFn = unsafe extern "C" fn(u64, u8) -> u64;
        let f: ShiftFn = unsafe { exec.as_fn() };
        let result = unsafe { f(val, amt) };
        assert_eq!(result, expected, "{name}({val}, {amt})");
    }
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_logical_not() {
    use Bytecode::*;
    use SignatureToken::*;

    let module = CompiledModuleBuilder::new()
        .function(
            "not",
            vec![Bool],
            vec![Bool],
            vec![],
            vec![CopyLoc(0), Not, Ret],
        )
        .build();
    let exec = compile_and_load(&module);
    type NotFn = unsafe extern "C" fn(u8) -> u8;
    let f: NotFn = unsafe { exec.as_fn() };
    assert_eq!(unsafe { f(0) }, 1, "not(false) should be true");
    assert_eq!(unsafe { f(1) }, 0, "not(true) should be false");
}

// ---------------------------------------------------------------------------
// Casts
// ---------------------------------------------------------------------------

#[test]
fn compile_casts() {
    use Bytecode::*;
    use SignatureToken::*;

    for (name, op, ret) in [
        ("cast_u8", CastU8, U8),
        ("cast_u16", CastU16, U16),
        ("cast_u32", CastU32, U32),
        ("cast_u64", CastU64, U64),
        ("cast_u128", CastU128, U128),
        ("cast_u256", CastU256, U256),
    ] {
        let module = CompiledModuleBuilder::new()
            .function(
                name,
                vec![U64],
                vec![ret],
                vec![],
                vec![CopyLoc(0), op, Ret],
            )
            .build();
        move_to_llvm::compile_module(&move_to_llvm::Target::Aarch64, &module)
            .unwrap_or_else(|e| panic!("{name} failed: {e}"));
    }
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_cast_truncate() {
    use Bytecode::*;
    use SignatureToken::*;

    let module = CompiledModuleBuilder::new()
        .function(
            "cast",
            vec![U64],
            vec![U8],
            vec![],
            vec![CopyLoc(0), CastU8, Ret],
        )
        .build();
    let exec = compile_and_load(&module);
    type CastFn = unsafe extern "C" fn(u64) -> u8;
    let f: CastFn = unsafe { exec.as_fn() };
    assert_eq!(unsafe { f(258) }, 2);
    assert_eq!(unsafe { f(42) }, 42);
}

// ---------------------------------------------------------------------------
// Address and signer types
// ---------------------------------------------------------------------------

#[test]
fn compile_address_and_signer_types() {
    use Bytecode::*;
    use SignatureToken::*;

    let module = CompiledModuleBuilder::new()
        .function(
            "identity_addr",
            vec![Address],
            vec![Address],
            vec![],
            vec![CopyLoc(0), Ret],
        )
        .function(
            "identity_signer",
            vec![Signer],
            vec![Signer],
            vec![],
            vec![CopyLoc(0), Ret],
        )
        .build();
    let asm = compile_module_checked(&module);
    assert!(asm.contains("identity_addr"));
    assert!(asm.contains("identity_signer"));
}

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

#[test]
fn compile_address_constant() {
    use Bytecode::*;
    use SignatureToken::*;

    let mut addr_bytes = [0u8; 32];
    addr_bytes[31] = 0x42;

    let module = CompiledModuleBuilder::new()
        .constant(Address, addr_bytes.to_vec())
        .function(
            "load_addr",
            vec![],
            vec![Address],
            vec![Address],
            vec![LdConst(ConstantPoolIndex(0)), StLoc(0), MoveLoc(0), Ret],
        )
        .build();
    let asm = compile_module_checked(&module);
    assert!(asm.contains("load_addr"));
}

#[test]
fn compile_u256_constant() {
    use Bytecode::*;
    use SignatureToken::*;

    let val: u64 = 1000;
    let mut u256_bytes = [0u8; 32];
    u256_bytes[..8].copy_from_slice(&val.to_le_bytes());

    let module = CompiledModuleBuilder::new()
        .constant(U256, u256_bytes.to_vec())
        .function(
            "load_u256",
            vec![],
            vec![U256],
            vec![U256],
            vec![LdConst(ConstantPoolIndex(0)), StLoc(0), MoveLoc(0), Ret],
        )
        .build();
    let asm = compile_module_checked(&module);
    assert!(asm.contains("load_u256"));
}

#[test]
fn compile_byte_array_constant() {
    use Bytecode::*;
    use SignatureToken::*;

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
            vec![LdConst(ConstantPoolIndex(0)), StLoc(0), MoveLoc(0), Ret],
        )
        .build();
    let asm = compile_module_checked(&module);
    assert!(asm.contains("__move_rt_const_vec_u8"));
}

#[test]
fn compile_vector_u64_constant() {
    use Bytecode::*;
    use SignatureToken::*;

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
            vec![LdConst(ConstantPoolIndex(0)), StLoc(0), MoveLoc(0), Ret],
        )
        .build();
    let asm = compile_module_checked(&module);
    assert!(asm.contains("__move_rt_const_vec"));
}

// ---------------------------------------------------------------------------
// Abort
// ---------------------------------------------------------------------------

#[test]
fn compile_abort_with_code() {
    use Bytecode::*;
    use SignatureToken::*;

    let module = CompiledModuleBuilder::new()
        .function(
            "abort_42",
            vec![],
            vec![],
            vec![U64],
            vec![LdU64(42), StLoc(0), MoveLoc(0), Abort],
        )
        .build();
    let asm = compile_module_checked(&module);
    assert!(asm.contains("__move_rt_abort"));
}

// ---------------------------------------------------------------------------
// Global storage operations
// ---------------------------------------------------------------------------

#[test]
fn compile_global_storage_ops() {
    use Bytecode::*;
    use SignatureToken::*;
    use move_binary_format::file_format::Ability;

    let coin_abilities = AbilitySet::EMPTY | Ability::Key;
    let coin = Datatype(DatatypeHandleIndex(0));
    let coin_ref = Reference(Box::new(coin.clone()));

    let module = CompiledModuleBuilder::new()
        .struct_definition("Coin", coin_abilities, vec![("value", U64)])
        .function(
            "check_exists",
            vec![Address],
            vec![Bool],
            vec![],
            vec![CopyLoc(0), ExistsDeprecated(StructDefinitionIndex(0)), Ret],
        )
        .function_with_acquires(
            "take_coin",
            vec![Address],
            vec![coin.clone()],
            vec![],
            vec![
                CopyLoc(0),
                MoveFromDeprecated(StructDefinitionIndex(0)),
                Ret,
            ],
            vec![StructDefinitionIndex(0)],
        )
        .function(
            "publish_coin",
            vec![coin.clone(), Signer],
            vec![],
            vec![],
            vec![
                MoveLoc(1),
                MoveLoc(0),
                MoveToDeprecated(StructDefinitionIndex(0)),
                Ret,
            ],
        )
        .function_with_acquires(
            "borrow_coin",
            vec![Address],
            vec![coin_ref],
            vec![],
            vec![
                CopyLoc(0),
                ImmBorrowGlobalDeprecated(StructDefinitionIndex(0)),
                Ret,
            ],
            vec![StructDefinitionIndex(0)],
        )
        .build();

    let asm = compile_module_checked(&module);
    assert!(asm.contains("__move_rt_exists"));
    assert!(asm.contains("__move_rt_move_from"));
    assert!(asm.contains("__move_rt_move_to"));
    assert!(asm.contains("__move_rt_borrow_global"));
}

// ---------------------------------------------------------------------------
// Vector operations (requires module stub)
// ---------------------------------------------------------------------------

/// Build a `0x1::vector` module stub with native function declarations.
fn build_vector_module_stub() -> CompiledModule {
    use SignatureToken::*;

    let type_param = AbilitySet::EMPTY;
    let t = TypeParameter(0);
    let vec_t = Vector(Box::new(t.clone()));
    let ref_vec_t = Reference(Box::new(vec_t.clone()));
    let mut_ref_vec_t = MutableReference(Box::new(vec_t.clone()));
    let ref_t = Reference(Box::new(t.clone()));
    let mut_ref_t = MutableReference(Box::new(t.clone()));

    // Can't use CompiledModuleBuilder here: need address 0x1 and module name "vector"
    CompiledModule {
        version: 7,
        publishable: true,
        self_module_handle_idx: ModuleHandleIndex(0),
        module_handles: vec![ModuleHandle {
            address: AddressIdentifierIndex(0),
            name: IdentifierIndex(0),
        }],
        identifiers: vec![
            Identifier::new("vector").unwrap(),
            Identifier::new("empty").unwrap(),
            Identifier::new("length").unwrap(),
            Identifier::new("push_back").unwrap(),
            Identifier::new("pop_back").unwrap(),
            Identifier::new("borrow").unwrap(),
            Identifier::new("borrow_mut").unwrap(),
            Identifier::new("swap").unwrap(),
            Identifier::new("destroy_empty").unwrap(),
        ],
        address_identifiers: vec![AccountAddress::ONE],
        signatures: vec![
            Signature(vec![]),
            Signature(vec![vec_t.clone()]),
            Signature(vec![mut_ref_vec_t.clone(), t.clone()]),
            Signature(vec![t.clone()]),
            Signature(vec![ref_vec_t]),
            Signature(vec![U64]),
            Signature(vec![mut_ref_vec_t.clone()]),
            Signature(vec![Reference(Box::new(vec_t.clone())), U64]),
            Signature(vec![ref_t]),
            Signature(vec![mut_ref_vec_t.clone(), U64]),
            Signature(vec![mut_ref_t]),
            Signature(vec![mut_ref_vec_t, U64, U64]),
        ],
        function_handles: vec![
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(1),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(1),
                type_parameters: vec![type_param],
            },
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(2),
                parameters: SignatureIndex(4),
                return_: SignatureIndex(5),
                type_parameters: vec![type_param],
            },
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(3),
                parameters: SignatureIndex(2),
                return_: SignatureIndex(0),
                type_parameters: vec![type_param],
            },
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(4),
                parameters: SignatureIndex(6),
                return_: SignatureIndex(3),
                type_parameters: vec![type_param],
            },
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(5),
                parameters: SignatureIndex(7),
                return_: SignatureIndex(8),
                type_parameters: vec![type_param],
            },
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(6),
                parameters: SignatureIndex(9),
                return_: SignatureIndex(10),
                type_parameters: vec![type_param],
            },
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(7),
                parameters: SignatureIndex(11),
                return_: SignatureIndex(0),
                type_parameters: vec![type_param],
            },
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(8),
                parameters: SignatureIndex(1),
                return_: SignatureIndex(0),
                type_parameters: vec![type_param],
            },
        ],
        function_defs: (0..8)
            .map(|i| FunctionDefinition {
                function: FunctionHandleIndex(i),
                visibility: Visibility::Public,
                is_entry: false,
                acquires_global_resources: vec![],
                code: None,
            })
            .collect(),
        struct_defs: vec![],
        datatype_handles: vec![],
        constant_pool: vec![],
        metadata: vec![],
        field_handles: vec![],
        friend_decls: vec![],
        struct_def_instantiations: vec![],
        function_instantiations: vec![],
        field_instantiations: vec![],
        enum_defs: vec![],
        enum_def_instantiations: vec![],
        variant_handles: vec![],
        variant_instantiation_handles: vec![],
    }
}

#[test]
fn compile_vec_ops() {
    use SignatureToken::*;

    let vec_stub = build_vector_module_stub();

    // Vector test module needs hand-built CompiledModule because VecXxx bytecodes
    // reference signature indices for element types, which the builder doesn't manage.
    let vec_test = CompiledModule {
        version: 7,
        publishable: true,
        self_module_handle_idx: ModuleHandleIndex(0),
        module_handles: vec![ModuleHandle {
            address: AddressIdentifierIndex(0),
            name: IdentifierIndex(0),
        }],
        identifiers: vec![
            Identifier::new("M").unwrap(),
            Identifier::new("test_vec").unwrap(),
        ],
        address_identifiers: vec![AccountAddress::ZERO],
        function_handles: vec![FunctionHandle {
            module: ModuleHandleIndex(0),
            name: IdentifierIndex(1),
            parameters: SignatureIndex(0),
            return_: SignatureIndex(1),
            type_parameters: vec![],
        }],
        function_defs: vec![FunctionDefinition {
            function: FunctionHandleIndex(0),
            visibility: Visibility::Public,
            is_entry: false,
            acquires_global_resources: vec![],
            code: Some(CodeUnit {
                locals: SignatureIndex(2),
                code: vec![
                    Bytecode::VecPack(SignatureIndex(3), 0),
                    Bytecode::StLoc(2),
                    Bytecode::MutBorrowLoc(2),
                    Bytecode::CopyLoc(0),
                    Bytecode::VecPushBack(SignatureIndex(3)),
                    Bytecode::MutBorrowLoc(2),
                    Bytecode::CopyLoc(1),
                    Bytecode::VecPushBack(SignatureIndex(3)),
                    Bytecode::MutBorrowLoc(2),
                    Bytecode::VecPopBack(SignatureIndex(3)),
                    Bytecode::StLoc(3),
                    Bytecode::MutBorrowLoc(2),
                    Bytecode::VecPopBack(SignatureIndex(3)),
                    Bytecode::StLoc(4),
                    Bytecode::MoveLoc(2),
                    Bytecode::VecUnpack(SignatureIndex(3), 0),
                    Bytecode::CopyLoc(4),
                    Bytecode::CopyLoc(3),
                    Bytecode::Add,
                    Bytecode::Ret,
                ],
                jump_tables: vec![],
            }),
        }],
        signatures: vec![
            Signature(vec![U64, U64]),
            Signature(vec![U64]),
            Signature(vec![Vector(Box::new(U64)), U64, U64]),
            Signature(vec![U64]), // element type for VecXxx
        ],
        struct_defs: vec![],
        datatype_handles: vec![],
        constant_pool: vec![],
        metadata: vec![],
        field_handles: vec![],
        friend_decls: vec![],
        struct_def_instantiations: vec![],
        function_instantiations: vec![],
        field_instantiations: vec![],
        enum_defs: vec![],
        enum_def_instantiations: vec![],
        variant_handles: vec![],
        variant_instantiation_handles: vec![],
    };

    let asm = compile_module_with_deps_checked(&vec_test, &[vec_stub]);
    assert!(asm.contains("__move_rt_0x1_vector_empty"));
    assert!(asm.contains("__move_rt_0x1_vector_push_back"));
    assert!(asm.contains("__move_rt_0x1_vector_pop_back"));
    assert!(asm.contains("__move_rt_0x1_vector_destroy_empty"));
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_vec_round_trip() {
    use SignatureToken::*;

    let vec_stub = build_vector_module_stub();
    let vec_test = CompiledModule {
        version: 7,
        publishable: true,
        self_module_handle_idx: ModuleHandleIndex(0),
        module_handles: vec![ModuleHandle {
            address: AddressIdentifierIndex(0),
            name: IdentifierIndex(0),
        }],
        identifiers: vec![
            Identifier::new("M").unwrap(),
            Identifier::new("test_vec").unwrap(),
        ],
        address_identifiers: vec![AccountAddress::ZERO],
        function_handles: vec![FunctionHandle {
            module: ModuleHandleIndex(0),
            name: IdentifierIndex(1),
            parameters: SignatureIndex(0),
            return_: SignatureIndex(1),
            type_parameters: vec![],
        }],
        function_defs: vec![FunctionDefinition {
            function: FunctionHandleIndex(0),
            visibility: Visibility::Public,
            is_entry: false,
            acquires_global_resources: vec![],
            code: Some(CodeUnit {
                locals: SignatureIndex(2),
                code: vec![
                    Bytecode::VecPack(SignatureIndex(3), 0),
                    Bytecode::StLoc(2),
                    Bytecode::MutBorrowLoc(2),
                    Bytecode::CopyLoc(0),
                    Bytecode::VecPushBack(SignatureIndex(3)),
                    Bytecode::MutBorrowLoc(2),
                    Bytecode::CopyLoc(1),
                    Bytecode::VecPushBack(SignatureIndex(3)),
                    Bytecode::MutBorrowLoc(2),
                    Bytecode::VecPopBack(SignatureIndex(3)),
                    Bytecode::StLoc(3),
                    Bytecode::MutBorrowLoc(2),
                    Bytecode::VecPopBack(SignatureIndex(3)),
                    Bytecode::StLoc(4),
                    Bytecode::MoveLoc(2),
                    Bytecode::VecUnpack(SignatureIndex(3), 0),
                    Bytecode::CopyLoc(4),
                    Bytecode::CopyLoc(3),
                    Bytecode::Add,
                    Bytecode::Ret,
                ],
                jump_tables: vec![],
            }),
        }],
        signatures: vec![
            Signature(vec![U64, U64]),
            Signature(vec![U64]),
            Signature(vec![Vector(Box::new(U64)), U64, U64]),
            Signature(vec![U64]),
        ],
        struct_defs: vec![],
        datatype_handles: vec![],
        constant_pool: vec![],
        metadata: vec![],
        field_handles: vec![],
        friend_decls: vec![],
        struct_def_instantiations: vec![],
        function_instantiations: vec![],
        field_instantiations: vec![],
        enum_defs: vec![],
        enum_def_instantiations: vec![],
        variant_handles: vec![],
        variant_instantiation_handles: vec![],
    };

    let asm = move_to_llvm::compile_module_with_deps(
        &move_to_llvm::Target::Aarch64,
        &vec_test,
        &[vec_stub],
    )
    .expect("vec ops compilation failed");
    assert!(!asm.contains("x23"));

    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let asm_path = temp_dir.path().join("move.s");
    let runtime_path = temp_dir.path().join("runtime.c");
    let dylib_ext = if cfg!(target_os = "macos") {
        "dylib"
    } else {
        "so"
    };
    let dylib_path = temp_dir.path().join(format!("test.{dylib_ext}"));

    std::fs::write(&asm_path, &asm).expect("failed to write asm");
    std::fs::write(&runtime_path, VEC_RUNTIME_C).expect("failed to write runtime");

    let output = Command::new("cc")
        .args([
            "-shared",
            "-o",
            dylib_path.to_str().unwrap(),
            asm_path.to_str().unwrap(),
            runtime_path.to_str().unwrap(),
        ])
        .output()
        .expect("failed to run cc");
    assert!(
        output.status.success(),
        "cc failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );

    unsafe {
        let lib_path = CString::new(dylib_path.to_str().unwrap()).unwrap();
        let lib = libc::dlopen(lib_path.as_ptr(), libc::RTLD_NOW);
        if lib.is_null() {
            let err = std::ffi::CStr::from_ptr(libc::dlerror())
                .to_str()
                .unwrap_or("unknown");
            panic!("dlopen failed: {err}");
        }

        let sym_name = CString::new("test_vec").unwrap();
        let sym = libc::dlsym(lib, sym_name.as_ptr());
        if sym.is_null() {
            let err = std::ffi::CStr::from_ptr(libc::dlerror())
                .to_str()
                .unwrap_or("unknown");
            libc::dlclose(lib);
            panic!("dlsym failed: {err}");
        }

        let f: unsafe extern "C" fn(u64, u64) -> u64 = std::mem::transmute(sym);
        assert_eq!(f(3, 7), 10);
        assert_eq!(f(0, 0), 0);
        assert_eq!(f(100, 200), 300);

        libc::dlclose(lib);
    }
}

// ---------------------------------------------------------------------------
// Cross-module function calls
// ---------------------------------------------------------------------------

#[test]
fn compile_cross_module_call() {
    use Bytecode::*;
    use SignatureToken::*;

    let dep = CompiledModuleBuilder::new()
        .function(
            "double",
            vec![U64],
            vec![U64],
            vec![],
            vec![CopyLoc(0), CopyLoc(0), Add, Ret],
        )
        .build();

    // Main module referencing Dep's "double" — requires manual construction
    // because the builder doesn't support foreign module handles.
    let main = CompiledModule {
        version: 7,
        publishable: true,
        self_module_handle_idx: ModuleHandleIndex(0),
        module_handles: vec![
            ModuleHandle {
                address: AddressIdentifierIndex(0),
                name: IdentifierIndex(0),
            },
            ModuleHandle {
                address: AddressIdentifierIndex(0),
                name: IdentifierIndex(1),
            },
        ],
        identifiers: vec![
            Identifier::new("Main").unwrap(),
            Identifier::new("M").unwrap(),
            Identifier::new("call_double").unwrap(),
            Identifier::new("double").unwrap(),
        ],
        address_identifiers: vec![AccountAddress::ZERO],
        function_handles: vec![
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(2),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(0),
                type_parameters: vec![],
            },
            FunctionHandle {
                module: ModuleHandleIndex(1),
                name: IdentifierIndex(3),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(0),
                type_parameters: vec![],
            },
        ],
        function_defs: vec![FunctionDefinition {
            function: FunctionHandleIndex(0),
            visibility: Visibility::Public,
            is_entry: false,
            acquires_global_resources: vec![],
            code: Some(CodeUnit {
                locals: SignatureIndex(1),
                code: vec![CopyLoc(0), Call(FunctionHandleIndex(1)), Ret],
                jump_tables: vec![],
            }),
        }],
        signatures: vec![Signature(vec![U64]), Signature(vec![])],
        struct_defs: vec![],
        datatype_handles: vec![],
        constant_pool: vec![],
        metadata: vec![],
        field_handles: vec![],
        friend_decls: vec![],
        struct_def_instantiations: vec![],
        function_instantiations: vec![],
        field_instantiations: vec![],
        enum_defs: vec![],
        enum_def_instantiations: vec![],
        variant_handles: vec![],
        variant_instantiation_handles: vec![],
    };

    let asm = compile_module_with_deps_checked(&main, &[dep]);
    assert!(asm.contains("call_double"));
    assert!(asm.contains("bl") && asm.contains("double"));
}

#[test]
#[cfg(all(target_arch = "aarch64", any(target_os = "macos", target_os = "linux")))]
fn execute_cross_module_call() {
    use Bytecode::*;
    use SignatureToken::*;

    let dep = CompiledModuleBuilder::new()
        .function(
            "double",
            vec![U64],
            vec![U64],
            vec![],
            vec![CopyLoc(0), CopyLoc(0), Add, Ret],
        )
        .build();

    let main = CompiledModule {
        version: 7,
        publishable: true,
        self_module_handle_idx: ModuleHandleIndex(0),
        module_handles: vec![
            ModuleHandle {
                address: AddressIdentifierIndex(0),
                name: IdentifierIndex(0),
            },
            ModuleHandle {
                address: AddressIdentifierIndex(0),
                name: IdentifierIndex(1),
            },
        ],
        identifiers: vec![
            Identifier::new("Main").unwrap(),
            Identifier::new("M").unwrap(),
            Identifier::new("call_double").unwrap(),
            Identifier::new("double").unwrap(),
        ],
        address_identifiers: vec![AccountAddress::ZERO],
        function_handles: vec![
            FunctionHandle {
                module: ModuleHandleIndex(0),
                name: IdentifierIndex(2),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(0),
                type_parameters: vec![],
            },
            FunctionHandle {
                module: ModuleHandleIndex(1),
                name: IdentifierIndex(3),
                parameters: SignatureIndex(0),
                return_: SignatureIndex(0),
                type_parameters: vec![],
            },
        ],
        function_defs: vec![FunctionDefinition {
            function: FunctionHandleIndex(0),
            visibility: Visibility::Public,
            is_entry: false,
            acquires_global_resources: vec![],
            code: Some(CodeUnit {
                locals: SignatureIndex(1),
                code: vec![CopyLoc(0), Call(FunctionHandleIndex(1)), Ret],
                jump_tables: vec![],
            }),
        }],
        signatures: vec![Signature(vec![U64]), Signature(vec![])],
        struct_defs: vec![],
        datatype_handles: vec![],
        constant_pool: vec![],
        metadata: vec![],
        field_handles: vec![],
        friend_decls: vec![],
        struct_def_instantiations: vec![],
        function_instantiations: vec![],
        field_instantiations: vec![],
        enum_defs: vec![],
        enum_def_instantiations: vec![],
        variant_handles: vec![],
        variant_instantiation_handles: vec![],
    };

    let dep_asm = move_to_llvm::compile_module(&move_to_llvm::Target::Aarch64, &dep)
        .expect("dep compilation failed");
    let main_asm =
        move_to_llvm::compile_module_with_deps(&move_to_llvm::Target::Aarch64, &main, &[dep])
            .expect("main compilation failed");

    let temp_dir = TempDir::new().expect("failed to create temp dir");
    let dep_asm_path = temp_dir.path().join("dep.s");
    let main_asm_path = temp_dir.path().join("main.s");
    let dylib_ext = if cfg!(target_os = "macos") {
        "dylib"
    } else {
        "so"
    };
    let dylib_path = temp_dir.path().join(format!("test.{dylib_ext}"));

    std::fs::write(&dep_asm_path, &dep_asm).expect("failed to write dep asm");
    std::fs::write(&main_asm_path, &main_asm).expect("failed to write main asm");

    let output = Command::new("cc")
        .args([
            "-shared",
            "-o",
            dylib_path.to_str().unwrap(),
            dep_asm_path.to_str().unwrap(),
            main_asm_path.to_str().unwrap(),
        ])
        .output()
        .expect("failed to run cc");
    assert!(
        output.status.success(),
        "cc failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );

    unsafe {
        let lib_path = CString::new(dylib_path.to_str().unwrap()).unwrap();
        let lib = libc::dlopen(lib_path.as_ptr(), libc::RTLD_NOW);
        if lib.is_null() {
            let err = std::ffi::CStr::from_ptr(libc::dlerror())
                .to_str()
                .unwrap_or("unknown");
            panic!("dlopen failed: {err}");
        }

        let sym_name = CString::new("call_double").unwrap();
        let sym = libc::dlsym(lib, sym_name.as_ptr());
        if sym.is_null() {
            let err = std::ffi::CStr::from_ptr(libc::dlerror())
                .to_str()
                .unwrap_or("unknown");
            libc::dlclose(lib);
            panic!("dlsym failed: {err}");
        }

        let f: unsafe extern "C" fn(u64) -> u64 = std::mem::transmute(sym);
        assert_eq!(f(5), 10);
        assert_eq!(f(0), 0);
        assert_eq!(f(100), 200);

        libc::dlclose(lib);
    }
}
