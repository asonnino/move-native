// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

// generics.move — Generic functions with concrete callers to trigger monomorphization.

module test_modules::generics {
    public struct Pair<T: copy + drop> has copy, drop {
        first: T,
        second: T,
    }

    public fun identity<T: copy + drop>(x: T): T {
        x
    }

    public fun make_pair<T: copy + drop>(a: T, b: T): Pair<T> {
        Pair { first: a, second: b }
    }

    public fun swap_pair<T: copy + drop>(p: Pair<T>): Pair<T> {
        let Pair { first, second } = p;
        Pair { first: second, second: first }
    }

    public fun first<T: copy + drop>(p: &Pair<T>): T {
        p.first
    }

    // Concrete callers that trigger monomorphization
    public fun identity_u64(x: u64): u64 {
        identity(x)
    }

    public fun swap_u64_pair(a: u64, b: u64): (u64, u64) {
        let p = make_pair(a, b);
        let swapped = swap_pair(p);
        (swapped.first, swapped.second)
    }
}
