// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

// vectors.move — Vector operations requiring framework dependencies.

module test_modules::vectors {
    use std::vector;

    public fun sum_vec(v: &vector<u64>): u64 {
        let mut sum = 0u64;
        let mut i = 0;
        let len = vector::length(v);
        while (i < len) {
            sum = sum + *vector::borrow(v, i);
            i = i + 1;
        };
        sum
    }

    public fun contains(v: &vector<u64>, target: u64): bool {
        let mut i = 0;
        let len = vector::length(v);
        while (i < len) {
            if (*vector::borrow(v, i) == target) {
                return true
            };
            i = i + 1;
        };
        false
    }

    public fun make_range(n: u64): vector<u64> {
        let mut v = vector::empty<u64>();
        let mut i = 0;
        while (i < n) {
            vector::push_back(&mut v, i);
            i = i + 1;
        };
        v
    }
}
