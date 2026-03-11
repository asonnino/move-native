// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use move_binary_format::file_format::{Ability, AbilitySet, SignatureToken};

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
}
