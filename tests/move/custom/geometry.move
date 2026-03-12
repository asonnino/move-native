// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

// geometry.move — Struct-heavy module exercising Pack, Unpack, field borrows,
// ReadRef, WriteRef, FreezeRef, intra-module calls, and arithmetic.

module test_modules::geometry {
    public struct Point has copy, drop {
        x: u64,
        y: u64,
    }

    public fun new_point(x: u64, y: u64): Point {
        Point { x, y }
    }

    public fun sum_fields(p: &Point): u64 {
        p.x + p.y
    }

    public fun distance_sq(a: &Point, b: &Point): u64 {
        let dx = if (a.x > b.x) { a.x - b.x } else { b.x - a.x };
        let dy = if (a.y > b.y) { a.y - b.y } else { b.y - a.y };
        dx * dx + dy * dy
    }

    public fun translate(p: &mut Point, dx: u64, dy: u64) {
        p.x = p.x + dx;
        p.y = p.y + dy;
    }

    public fun midpoint(a: &Point, b: &Point): Point {
        new_point((a.x + b.x) / 2, (a.y + b.y) / 2)
    }
}
