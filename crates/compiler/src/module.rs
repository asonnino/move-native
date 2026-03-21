// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Move module construction and loading for tests.

#[cfg(test)]
mod basic;
mod builder;
pub mod bundle;
mod kitchen_sink;

pub use builder::CompiledModuleBuilder;
