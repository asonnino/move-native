// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

// checked_math.move — Abort, comparisons, multi-return, and function chaining.

module test_modules::checked_math {
    public fun checked_sub(a: u64, b: u64): u64 {
        if (b > a) {
            abort 1
        };
        a - b
    }

    public fun safe_div(a: u64, b: u64): u64 {
        if (b == 0) {
            abort 2
        };
        a / b
    }

    public fun divmod(a: u64, b: u64): (u64, u64) {
        if (b == 0) {
            abort 3
        };
        (a / b, a % b)
    }

    public fun clamp(x: u64, lo: u64, hi: u64): u64 {
        if (x < lo) {
            lo
        } else if (x > hi) {
            hi
        } else {
            x
        }
    }

    public fun abs_diff(a: u64, b: u64): u64 {
        if (a >= b) {
            a - b
        } else {
            b - a
        }
    }
}
