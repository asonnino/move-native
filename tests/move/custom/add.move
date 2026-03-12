// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

// add.move — Minimal Move module for testing the compiler
//
// Equivalent to the CompiledModule constructed in
// crates/compiler/tests/integration.rs::make_add_module()
//
// To compile: sui move build  (produces build/.../add.mv)

module 0x0::M {
    public fun add(a: u64, b: u64): u64 {
        a + b
    }
}
