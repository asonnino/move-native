// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

// objects.move — Sui objects with key ability and UID.
// Requires the Sui framework for object::UID and tx_context.

module test_modules::objects {
    use sui::object::{Self, UID};
    use sui::tx_context::TxContext;
    use sui::transfer;

    public struct Counter has key {
        id: UID,
        value: u64,
    }

    public fun create(ctx: &mut TxContext) {
        let counter = Counter {
            id: object::new(ctx),
            value: 0,
        };
        transfer::share_object(counter);
    }

    public fun increment(counter: &mut Counter) {
        counter.value = counter.value + 1;
    }

    public fun value(counter: &Counter): u64 {
        counter.value
    }
}
