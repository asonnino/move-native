// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use move_binary_format::file_format::{
    Ability, AbilitySet, Bytecode, DatatypeTyParameter, SignatureToken,
};

use super::CompiledModuleBuilder;

impl CompiledModuleBuilder {
    /// Builder pre-loaded with `Point { x: u64, y: u64 }` at `DatatypeHandleIndex(0)`.
    pub fn point() -> Self {
        Self::new().struct_definition(
            "Point",
            AbilitySet::PRIMITIVES,
            vec![("x", SignatureToken::U64), ("y", SignatureToken::U64)],
        )
    }

    /// Builder pre-loaded with `Coin { value: u64 }` (key ability) at `DatatypeHandleIndex(0)`.
    pub fn coin() -> Self {
        Self::new().struct_definition(
            "Coin",
            AbilitySet::EMPTY | Ability::Key,
            vec![("value", SignatureToken::U64)],
        )
    }

    /// Builder pre-loaded with `Balance<phantom T> { value: u64 }` at `DatatypeHandleIndex(0)`.
    ///
    /// Mirrors Sui's `sui::balance::Balance` — a single phantom type parameter
    /// with a `u64` field.
    pub fn balance() -> Self {
        Self::new().generic_struct_definition(
            "Balance",
            AbilitySet::EMPTY | Ability::Store,
            vec![DatatypeTyParameter {
                constraints: AbilitySet::EMPTY,
                is_phantom: true,
            }],
            vec![("value", SignatureToken::U64)],
        )
    }

    /// Builder pre-loaded with `enum MyOption { None, Some { value: u64 } }`
    /// at `DatatypeHandleIndex(0)`, plus `VariantHandle`s 0 (None) and 1 (Some).
    pub fn option() -> Self {
        Self::new()
            .enum_definition(
                "MyOption",
                AbilitySet::EMPTY | Ability::Copy | Ability::Drop,
                vec![
                    ("None", vec![]),
                    ("Some", vec![("value", SignatureToken::U64)]),
                ],
            )
            .variant_handle(0, 0)
            .variant_handle(0, 1)
    }

    /// Module with a single function `name(a: T, b: T) -> T` that applies a binary op.
    pub fn binary_op(name: &str, ty: SignatureToken, op: Bytecode) -> Self {
        Self::new().function(
            name,
            vec![ty.clone(), ty.clone()],
            vec![ty],
            vec![],
            vec![Bytecode::CopyLoc(0), Bytecode::CopyLoc(1), op, Bytecode::Ret],
        )
    }

    /// Module with a single function `name(a: T, b: T) -> bool` that applies a comparison op.
    pub fn comparison_op(name: &str, ty: SignatureToken, op: Bytecode) -> Self {
        Self::new().function(
            name,
            vec![ty.clone(), ty],
            vec![SignatureToken::Bool],
            vec![],
            vec![Bytecode::CopyLoc(0), Bytecode::CopyLoc(1), op, Bytecode::Ret],
        )
    }

    /// Module with a single function `name(a: In) -> Out` that applies a unary op.
    pub fn unary_op(
        name: &str,
        input: SignatureToken,
        output: SignatureToken,
        op: Bytecode,
    ) -> Self {
        Self::new().function(
            name,
            vec![input],
            vec![output],
            vec![],
            vec![Bytecode::CopyLoc(0), op, Bytecode::Ret],
        )
    }
}
