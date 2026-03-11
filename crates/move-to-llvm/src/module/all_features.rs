// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Pre-built test module that exercises interactions between most compiler features.
//!
//! Move pseudocode for the generated module:
//!
//! ```move
//! module 0x0::M {
//!     use 0x0::Dep;
//!     use 0x1::vector;
//!
//!     struct Point has copy, drop, store { x: u64, y: u64 }
//!
//!     public fun make_point(x: u64, y: u64): Point { Point { x, y } }
//!     public fun sum_point(p: Point): u64 { let Point { x, y } = p; x + y }
//!     public fun round_trip(x: u64, y: u64): u64 { sum_point(make_point(x, y)) }
//!     public fun identity<T>(x: T): T { x }
//!     public fun call_identity(x: u64): u64 { identity<u64>(x) }
//!     public fun sum_loop(n: u64): u64 { /* while i < n: sum += i + (i+1) */ }
//!     public fun swap_fields(p: &mut Point): u64 { /* swap x,y; return x+y */ }
//!     public fun swap_u64(a: u64, b: u64): (u64, u64) { (b, a) }
//!     public fun checked_sub(a: u64, b: u64): u64 { if (b > a) abort 1; a - b }
//!     public fun low_byte(x: u64): u8 { (x as u8) }
//!     public fun forty_two(): u64 { 42 }
//!     public fun integration_test(n: u64): u64 {
//!         checked_sub(swap_u64(call_identity(sum_loop(n)), 0))
//!     }
//!     public fun call_double(x: u64): u64 { Dep::double(x) }
//!     public fun test_vec(a: u64, b: u64): u64 {
//!         let v = vector::empty<u64>();
//!         vector::push_back(&mut v, a);
//!         vector::push_back(&mut v, b);
//!         let y = vector::pop_back(&mut v);
//!         let x = vector::pop_back(&mut v);
//!         vector::destroy_empty(v);
//!         x + y
//!     }
//!     public fun cast_widths(x: u64): u64 { ((((x as u16) as u32) as u128) as u256) as u64 }
//!     public fun freeze_and_read(p: &mut Point): u64 { *freeze(&mut p.x) }
//!     public fun discard(x: u64): u64 { let _ = 99; x }
//!     public fun read_x(p: &Point): u64 { *&p.x }
//!     public fun add_u16(a: u16, b: u16): u16 { a + b }
//!     public fun add_u32(a: u32, b: u32): u32 { a + b }
//!     public fun add_u128(a: u128, b: u128): u128 { a + b }
//!     public fun add_u256(a: u256, b: u256): u256 { a + b }
//! }
//! ```
//!
//! Key property: `sum_loop(n) == n²` and `integration_test(n) == n²`.

use move_binary_format::CompiledModule;
use move_binary_format::file_format::{
    AbilitySet,
    Bytecode::{
        self, Abort, Add, BrFalse, Branch, Call, CallGeneric, CastU8, CastU16, CastU32, CastU64,
        CastU128, CastU256, CopyLoc, FreezeRef, Gt, ImmBorrowField, LdU64, Lt, MoveLoc,
        MutBorrowField, MutBorrowLoc, Pack, Pop, ReadRef, Ret, StLoc, Sub, Unpack, WriteRef,
    },
    DatatypeHandleIndex, FieldHandleIndex, FunctionHandleIndex, FunctionInstantiationIndex,
    SignatureToken::{
        self, Datatype, MutableReference, Reference, TypeParameter, U8, U16, U32, U64, U128, U256,
        Vector,
    },
    StructDefinitionIndex,
};
use move_core_types::account_address::AccountAddress;

use super::CompiledModuleBuilder;

impl CompiledModuleBuilder {
    /// Build a module that exercises interactions between most compiler features.
    ///
    /// Returns `(main_module, dependency_modules)`.
    ///
    /// Contains 22 functions operating on a `Point { x: u64, y: u64 }` struct:
    ///
    /// | Index | Name              | Tests                                        |
    /// |-------|-------------------|----------------------------------------------|
    /// | 0     | `make_point`      | struct Pack                                  |
    /// | 1     | `sum_point`       | struct Unpack + arithmetic                   |
    /// | 2     | `round_trip`      | intra-module calls (make_point → sum_point)  |
    /// | 3     | `identity<T>`     | generic function                             |
    /// | 4     | `call_identity`   | CallGeneric (identity\<u64\>)                |
    /// | 5     | `sum_loop`        | while loop + calls + struct interaction      |
    /// | 6     | `swap_fields`     | mutable field borrows, ReadRef, WriteRef     |
    /// | 7     | `swap_u64`        | multi-return                                 |
    /// | 8     | `checked_sub`     | comparison + conditional abort               |
    /// | 9     | `low_byte`        | integer cast (u64 → u8)                      |
    /// | 10    | `forty_two`       | constant loading                             |
    /// | 11    | `integration_test`| chains sum_loop → call_identity → swap_u64 → checked_sub |
    /// | 12    | `double` (foreign)| declared in Dep module                       |
    /// | 13    | `call_double`     | cross-module call to Dep::double             |
    /// | 14    | `test_vec`        | vector ops (VecPack/PushBack/PopBack/Unpack) |
    /// | 15    | `cast_widths`     | integer width casts (U16/U32/U128/U256)      |
    /// | 16    | `freeze_and_read` | MutBorrowField → FreezeRef → ReadRef         |
    /// | 17    | `discard`         | Pop (Destroy) to discard a value             |
    /// | 18    | `read_x`          | ImmBorrowField → ReadRef                     |
    /// | 19    | `add_u16`         | u16 in signature + arithmetic                |
    /// | 20    | `add_u32`         | u32 in signature + arithmetic                |
    /// | 21    | `add_u128`        | u128 in signature + arithmetic               |
    /// | 22    | `add_u256`        | u256 in signature + arithmetic               |
    pub fn all_features() -> (CompiledModule, Vec<CompiledModule>) {
        let point = Datatype(DatatypeHandleIndex(0));
        let mut_point_ref = MutableReference(Box::new(point.clone()));
        let mut_u64_ref = MutableReference(Box::new(U64));

        let builder = Self::new()
            // --- Struct ---
            // DatatypeHandleIndex(0): Point { x: u64, y: u64 }
            .struct_definition(
                "Point",
                AbilitySet::PRIMITIVES,
                vec![("x", U64), ("y", U64)],
            )
            // FieldHandleIndex(0): Point.x, FieldHandleIndex(1): Point.y
            .field_handle(StructDefinitionIndex(0), 0)
            .field_handle(StructDefinitionIndex(0), 1)
            // --- FunctionHandleIndex(0): make_point(x: u64, y: u64): Point ---
            .function(
                "make_point",
                vec![U64, U64],
                vec![point.clone()],
                vec![],
                vec![CopyLoc(0), CopyLoc(1), Pack(StructDefinitionIndex(0)), Ret],
            )
            // --- FunctionHandleIndex(1): sum_point(p: Point): u64 ---
            .function(
                "sum_point",
                vec![point.clone()],
                vec![U64],
                vec![U64, U64],
                vec![
                    MoveLoc(0),                       // push p
                    Unpack(StructDefinitionIndex(0)), // → x, y (y on top)
                    StLoc(2),                         // y
                    StLoc(1),                         // x
                    CopyLoc(1),
                    CopyLoc(2),
                    Add,
                    Ret,
                ],
            )
            // --- FunctionHandleIndex(2): round_trip(x: u64, y: u64): u64 ---
            .function(
                "round_trip",
                vec![U64, U64],
                vec![U64],
                vec![point.clone(), U64],
                vec![
                    CopyLoc(0),
                    CopyLoc(1),
                    Call(FunctionHandleIndex(0)), // make_point
                    StLoc(2),
                    CopyLoc(2),
                    Call(FunctionHandleIndex(1)), // sum_point
                    StLoc(3),
                    MoveLoc(3),
                    Ret,
                ],
            )
            // --- FunctionHandleIndex(3): identity<T>(x: T): T ---
            .generic_function(
                "identity",
                vec![AbilitySet::EMPTY],
                vec![TypeParameter(0)],
                vec![TypeParameter(0)],
                vec![],
                vec![MoveLoc(0), Ret],
            )
            // FunctionInstantiationIndex(0): identity<u64>
            .function_instantiation(FunctionHandleIndex(3), vec![U64])
            // --- FunctionHandleIndex(4): call_identity(x: u64): u64 ---
            .function(
                "call_identity",
                vec![U64],
                vec![U64],
                vec![],
                vec![CopyLoc(0), CallGeneric(FunctionInstantiationIndex(0)), Ret],
            )
            // --- FunctionHandleIndex(5): sum_loop(n: u64): u64 ---
            // sum of (i + i+1) for i=0..n-1 = n²
            .function(
                "sum_loop",
                vec![U64],
                vec![U64],
                vec![U64, U64, point.clone(), U64], // sum, i, p, tmp
                vec![
                    LdU64(0),
                    StLoc(1), // 0,1: sum = 0
                    LdU64(0),
                    StLoc(2), // 2,3: i = 0
                    // LOOP (offset 4):
                    CopyLoc(2),                   // 4: push i
                    CopyLoc(0),                   // 5: push n
                    Lt,                           // 6: i < n
                    BrFalse(24),                  // 7: → END
                    CopyLoc(2),                   // 8: push i
                    CopyLoc(2),                   // 9: push i
                    LdU64(1),                     // 10
                    Add,                          // 11: i + 1
                    Call(FunctionHandleIndex(0)), // 12: make_point(i, i+1)
                    StLoc(3),                     // 13: p
                    CopyLoc(1),                   // 14: push sum
                    CopyLoc(3),                   // 15: push p
                    Call(FunctionHandleIndex(1)), // 16: sum_point(p)
                    Add,                          // 17: sum + sum_point(p)
                    StLoc(1),                     // 18: sum
                    CopyLoc(2),                   // 19: push i
                    LdU64(1),                     // 20
                    Add,                          // 21: i + 1
                    StLoc(2),                     // 22: i
                    Branch(4),                    // 23: → LOOP
                    // END (offset 24):
                    MoveLoc(1), // 24: push sum
                    Ret,        // 25
                ],
            )
            // --- FunctionHandleIndex(6): swap_fields(p: &mut Point): u64 ---
            .function(
                "swap_fields",
                vec![mut_point_ref],
                vec![U64],
                vec![mut_u64_ref.clone(), mut_u64_ref, U64, U64],
                vec![
                    CopyLoc(0),                          // push p
                    MutBorrowField(FieldHandleIndex(0)), // &mut p.x
                    StLoc(1),                            // ref_x
                    CopyLoc(0),                          // push p
                    MutBorrowField(FieldHandleIndex(1)), // &mut p.y
                    StLoc(2),                            // ref_y
                    CopyLoc(1),
                    ReadRef,
                    StLoc(3), // vx = *ref_x
                    CopyLoc(2),
                    ReadRef,
                    StLoc(4), // vy = *ref_y
                    CopyLoc(4),
                    MoveLoc(1),
                    WriteRef, // *ref_x = vy
                    CopyLoc(3),
                    MoveLoc(2),
                    WriteRef, // *ref_y = vx
                    CopyLoc(3),
                    CopyLoc(4),
                    Add,
                    Ret,
                ],
            )
            // --- FunctionHandleIndex(7): swap_u64(a: u64, b: u64): (u64, u64) ---
            .function(
                "swap_u64",
                vec![U64, U64],
                vec![U64, U64],
                vec![],
                vec![CopyLoc(1), CopyLoc(0), Ret],
            )
            // --- FunctionHandleIndex(8): checked_sub(a: u64, b: u64): u64 ---
            .function(
                "checked_sub",
                vec![U64, U64],
                vec![U64],
                vec![],
                vec![
                    CopyLoc(1), // 0: push b
                    CopyLoc(0), // 1: push a
                    Gt,         // 2: b > a?
                    BrFalse(6), // 3: if b <= a, skip to subtraction
                    LdU64(1),   // 4: error code
                    Abort,      // 5: underflow
                    CopyLoc(0), // 6: push a
                    CopyLoc(1), // 7: push b
                    Sub,        // 8: a - b
                    Ret,        // 9
                ],
            )
            // --- FunctionHandleIndex(9): low_byte(x: u64): u8 ---
            .function(
                "low_byte",
                vec![U64],
                vec![U8],
                vec![],
                vec![CopyLoc(0), CastU8, Ret],
            )
            // --- FunctionHandleIndex(10): forty_two(): u64 ---
            .function("forty_two", vec![], vec![U64], vec![], vec![LdU64(42), Ret])
            // --- FunctionHandleIndex(11): integration_test(n: u64): u64 ---
            // Chains: sum_loop → call_identity → swap_u64 → checked_sub
            // Result: n²
            .function(
                "integration_test",
                vec![U64],
                vec![U64],
                vec![U64, U64, U64, U64], // total, id, a, b
                vec![
                    CopyLoc(0),                   // 0: push n
                    Call(FunctionHandleIndex(5)), // 1: sum_loop(n)
                    StLoc(1),                     // 2: total
                    CopyLoc(1),                   // 3
                    Call(FunctionHandleIndex(4)), // 4: call_identity(total)
                    StLoc(2),                     // 5: id
                    CopyLoc(2),                   // 6
                    LdU64(0),                     // 7
                    Call(FunctionHandleIndex(7)), // 8: swap_u64(id, 0) → (0, id)
                    StLoc(4),                     // 9: b = id (second return)
                    StLoc(3),                     // 10: a = 0 (first return)
                    CopyLoc(4),                   // 11: push b
                    CopyLoc(3),                   // 12: push a
                    Call(FunctionHandleIndex(8)), // 13: checked_sub(b, a)
                    Ret,                          // 14
                ],
            );

        // --- Foreign module: Dep (for cross-module call) ---
        let (builder, dep_handle) = builder.foreign_module(AccountAddress::ZERO, "Dep");
        // FunctionHandleIndex(12): Dep::double (foreign, no body)
        let builder = builder.foreign_function(dep_handle, "double", vec![U64], vec![U64]);

        // --- FunctionHandleIndex(13): call_double(x: u64): u64 ---
        let builder = builder.function(
            "call_double",
            vec![U64],
            vec![U64],
            vec![],
            vec![CopyLoc(0), Call(FunctionHandleIndex(12)), Ret],
        );

        // --- Foreign module: vector (for vector ops) ---
        let (builder, _vec_handle) = builder.foreign_module(AccountAddress::ONE, "vector");

        // Signature for VecXxx element type
        let (builder, vec_element_signature) = builder.signature(vec![U64]);

        // --- FunctionHandleIndex(14): test_vec(a: u64, b: u64): u64 ---
        let main_module = builder
            .function(
                "test_vec",
                vec![U64, U64],
                vec![U64],
                vec![Vector(Box::new(U64)), U64, U64], // v, y, x
                vec![
                    Bytecode::VecPack(vec_element_signature, 0),  // empty vec
                    StLoc(2),                                     // v
                    MutBorrowLoc(2),                              // &mut v
                    CopyLoc(0),                                   // a
                    Bytecode::VecPushBack(vec_element_signature), // push_back(a)
                    MutBorrowLoc(2),                              // &mut v
                    CopyLoc(1),                                   // b
                    Bytecode::VecPushBack(vec_element_signature), // push_back(b)
                    MutBorrowLoc(2),                              // &mut v
                    Bytecode::VecPopBack(vec_element_signature),  // pop_back → b
                    StLoc(3),                                     // y
                    MutBorrowLoc(2),                              // &mut v
                    Bytecode::VecPopBack(vec_element_signature),  // pop_back → a
                    StLoc(4),                                     // x
                    MoveLoc(2),                                   // v
                    Bytecode::VecUnpack(vec_element_signature, 0), // destroy_empty
                    CopyLoc(4),                                   // x
                    CopyLoc(3),                                   // y
                    Add,
                    Ret,
                ],
            )
            // --- FunctionHandleIndex(15): cast_widths(x: u64): u64 ---
            // Chains CastU16 → CastU32 → CastU128 → CastU256 → CastU64 to round-trip
            .function(
                "cast_widths",
                vec![U64],
                vec![U64],
                vec![],
                vec![
                    CopyLoc(0),
                    CastU16,
                    CastU32,
                    CastU128,
                    CastU256,
                    CastU64,
                    Ret,
                ],
            )
            // --- FunctionHandleIndex(16): freeze_and_read(p: &mut Point): u64 ---
            // MutBorrowField → FreezeRef → ReadRef
            .function(
                "freeze_and_read",
                vec![MutableReference(Box::new(point.clone()))],
                vec![U64],
                vec![],
                vec![
                    CopyLoc(0),
                    MutBorrowField(FieldHandleIndex(0)), // &mut p.x
                    FreezeRef,                           // &p.x
                    ReadRef,                             // *(&p.x)
                    Ret,
                ],
            )
            // --- FunctionHandleIndex(17): discard(x: u64): u64 ---
            // Pop (Destroy) to discard a value
            .function(
                "discard",
                vec![U64],
                vec![U64],
                vec![],
                vec![
                    CopyLoc(0), // push x
                    LdU64(99),  // push 99
                    Pop,        // discard 99
                    Ret,        // return x
                ],
            )
            // --- FunctionHandleIndex(18): read_x(p: &Point): u64 ---
            // ImmBorrowField → ReadRef
            .function(
                "read_x",
                vec![Reference(Box::new(point.clone()))],
                vec![U64],
                vec![],
                vec![
                    CopyLoc(0),
                    ImmBorrowField(FieldHandleIndex(0)), // &p.x
                    ReadRef,                             // *(&p.x)
                    Ret,
                ],
            )
            // --- FunctionHandleIndex(19): add_u16(a: u16, b: u16): u16 ---
            .function(
                "add_u16",
                vec![U16, U16],
                vec![U16],
                vec![],
                vec![CopyLoc(0), CopyLoc(1), Add, Ret],
            )
            // --- FunctionHandleIndex(20): add_u32(a: u32, b: u32): u32 ---
            .function(
                "add_u32",
                vec![U32, U32],
                vec![U32],
                vec![],
                vec![CopyLoc(0), CopyLoc(1), Add, Ret],
            )
            // --- FunctionHandleIndex(21): add_u128(a: u128, b: u128): u128 ---
            .function(
                "add_u128",
                vec![U128, U128],
                vec![U128],
                vec![],
                vec![CopyLoc(0), CopyLoc(1), Add, Ret],
            )
            // --- FunctionHandleIndex(22): add_u256(a: u256, b: u256): u256 ---
            .function(
                "add_u256",
                vec![U256, U256],
                vec![U256],
                vec![],
                vec![CopyLoc(0), CopyLoc(1), Add, Ret],
            )
            .build();

        // --- Build dependency modules ---
        let dep_module = Self::named("Dep", AccountAddress::ZERO)
            .function(
                "double",
                vec![U64],
                vec![U64],
                vec![],
                vec![CopyLoc(0), CopyLoc(0), Add, Ret],
            )
            .build();

        let vector_stub = Self::vector_module_stub();

        (main_module, vec![dep_module, vector_stub])
    }

    /// Build a `0x1::vector` module stub with native function declarations.
    fn vector_module_stub() -> CompiledModule {
        let type_parameters = vec![AbilitySet::EMPTY];
        let type_param_token = TypeParameter(0);
        let vector_of_t = Vector(Box::new(type_param_token.clone()));
        let ref_vector_of_t = SignatureToken::Reference(Box::new(vector_of_t.clone()));
        let mut_ref_vector_of_t = MutableReference(Box::new(vector_of_t.clone()));
        let ref_of_t = SignatureToken::Reference(Box::new(type_param_token.clone()));
        let mut_ref_of_t = MutableReference(Box::new(type_param_token.clone()));

        Self::named("vector", AccountAddress::ONE)
            .generic_native_function(
                "empty",
                type_parameters.clone(),
                vec![],
                vec![vector_of_t.clone()],
            )
            .generic_native_function(
                "length",
                type_parameters.clone(),
                vec![ref_vector_of_t],
                vec![U64],
            )
            .generic_native_function(
                "push_back",
                type_parameters.clone(),
                vec![mut_ref_vector_of_t.clone(), type_param_token.clone()],
                vec![],
            )
            .generic_native_function(
                "pop_back",
                type_parameters.clone(),
                vec![mut_ref_vector_of_t.clone()],
                vec![type_param_token],
            )
            .generic_native_function(
                "borrow",
                type_parameters.clone(),
                vec![
                    SignatureToken::Reference(Box::new(vector_of_t.clone())),
                    U64,
                ],
                vec![ref_of_t],
            )
            .generic_native_function(
                "borrow_mut",
                type_parameters.clone(),
                vec![mut_ref_vector_of_t.clone(), U64],
                vec![mut_ref_of_t],
            )
            .generic_native_function(
                "swap",
                type_parameters.clone(),
                vec![mut_ref_vector_of_t, U64, U64],
                vec![],
            )
            .generic_native_function("destroy_empty", type_parameters, vec![vector_of_t], vec![])
            .build()
    }
}
