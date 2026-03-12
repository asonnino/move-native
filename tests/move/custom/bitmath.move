// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

// bitmath.move — Bitwise operations, shifts, and integer casts.

module test_modules::bitmath {
    public fun mask_low_byte(x: u64): u64 {
        x & 0xFF
    }

    public fun set_bit(x: u64, bit: u8): u64 {
        x | (1u64 << bit)
    }

    public fun rotate_left(x: u32, n: u8): u32 {
        (x << n) | (x >> (32u8 - n))
    }

    public fun cast_chain(x: u64): u128 {
        let a = (x as u8);
        let b = (a as u16);
        let c = (b as u32);
        let d = (c as u64);
        (d as u128)
    }

    public fun add_u128(a: u128, b: u128): u128 {
        a + b
    }

    public fun xor_swap(a: u64, b: u64): (u64, u64) {
        let mut a = a;
        let mut b = b;
        a = a ^ b;
        b = b ^ a;
        a = a ^ b;
        (a, b)
    }
}
