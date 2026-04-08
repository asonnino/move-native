// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Move module metadata, construction, and loading.

#[cfg(test)]
mod basic;
mod builder;
pub mod bundle;
pub mod info;
mod kitchen_sink;

pub use builder::CompiledModuleBuilder;
pub use info::ModuleInfo;
