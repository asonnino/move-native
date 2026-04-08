// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! ELF object file output from the compiler.

/// Compiled object file (`.o` bytes) produced by [`Compiler::emit_object`].
pub struct ObjectFile(Vec<u8>);

impl ObjectFile {
    pub(crate) fn new(bytes: Vec<u8>) -> Self {
        Self(bytes)
    }

    /// Raw `.o` bytes.
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }
}
