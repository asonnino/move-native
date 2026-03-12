// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

// control_flow.move — Exercises loops and branches for testing control flow lowering
//
// To compile: sui move build  (produces build/.../control_flow.mv)

module 0x0::control_flow {
    public fun sum_to(n: u64): u64 {
        let mut i = 0;
        let mut sum = 0;
        while (i < n) {
            i = i + 1;
            sum = sum + i;
        };
        sum
    }

    public fun sum_even(n: u64): u64 {
        let mut i = 0;
        let mut sum = 0;
        while (i < n) {
            i = i + 1;
            if (i % 2 == 0) {
                sum = sum + i;
            };
        };
        sum
    }

    public fun nested_sum(rows: u64, cols: u64): u64 {
        let mut i = 0;
        let mut total = 0;
        while (i < rows) {
            let mut j = 0;
            while (j < cols) {
                total = total + i * cols + j;
                j = j + 1;
            };
            i = i + 1;
        };
        total
    }
}
