// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use move_binary_format::file_format::{Ability, AbilitySet, DatatypeTyParameter, SignatureToken};

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
}
