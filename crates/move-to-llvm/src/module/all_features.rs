// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Pre-built test module that exercises interactions between most compiler features.
//!
//! Move pseudocode for the generated module:
//!
//! ```move
//! module 0x0::M {
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
//! }
//! ```
//!
//! Key property: `sum_loop(n) == n²` and `integration_test(n) == n²`.

use move_binary_format::CompiledModule;
use move_binary_format::file_format::{
    AbilitySet,
    Bytecode::{
        Abort, Add, BrFalse, Branch, Call, CallGeneric, CastU8, CopyLoc, Gt, LdU64, Lt, MoveLoc,
        MutBorrowField, Pack, ReadRef, Ret, StLoc, Sub, Unpack, WriteRef,
    },
    DatatypeHandleIndex, FieldHandleIndex, FunctionHandleIndex, FunctionInstantiationIndex,
    SignatureToken::{Datatype, MutableReference, TypeParameter, U8, U64},
    StructDefinitionIndex,
};

use super::CompiledModuleBuilder;

impl CompiledModuleBuilder {
    /// Build a module that exercises interactions between most compiler features.
    ///
    /// Contains 12 functions operating on a `Point { x: u64, y: u64 }` struct:
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
    pub fn all_features() -> CompiledModule {
        let point = Datatype(DatatypeHandleIndex(0));
        let mut_point_ref = MutableReference(Box::new(point.clone()));
        let mut_u64_ref = MutableReference(Box::new(U64));

        Self::new()
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
            )
            .build()
    }
}
