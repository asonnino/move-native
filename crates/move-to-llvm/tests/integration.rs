// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for the Move-to-LLVM compiler.

use move_binary_format::file_format::*;
use move_core_types::account_address::AccountAddress;
use move_core_types::identifier::Identifier;
use move_to_llvm::module::CompiledModuleBuilder;
use move_to_llvm::{Compiler, Target};

#[test]
fn all_features_compiles() {
    let module = CompiledModuleBuilder::all_features();
    let asm = Compiler::compile_module(&Target::host(), &module).unwrap();

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

    // Verify key instruction patterns proving features work end-to-end
    assert!(asm.contains("bl"), "should contain function calls (bl)");
    assert!(
        asm.contains("b."),
        "should contain conditional branches (b.cond)"
    );
    assert!(asm.contains("ret"), "should contain function returns (ret)");
    assert!(
        asm.contains("identity$u64"),
        "should contain monomorphized generic (identity$u64)"
    );
}

// ===================================================================
// Cross-module / vector tests (require multiple modules or native stubs)
// ===================================================================

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

    let asm = Compiler::compile_module_with_dependencies(&Target::host(), &vec_test, &[vec_stub])
        .unwrap();
    assert!(asm.contains("__move_rt_0x1_vector_empty"));
    assert!(asm.contains("__move_rt_0x1_vector_push_back"));
    assert!(asm.contains("__move_rt_0x1_vector_pop_back"));
    assert!(asm.contains("__move_rt_0x1_vector_destroy_empty"));
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

    let asm = Compiler::compile_module_with_dependencies(&Target::host(), &main, &[dep]).unwrap();
    assert!(asm.contains("call_double"));
    assert!(asm.contains("bl") && asm.contains("double"));
}
