// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::targets::InitializationConfig;

pub(crate) const CPU: &str = "generic";
/// Reserve x23 so LLVM never allocates the gas register.
pub(crate) const FEATURES: &str = "+reserve-x23";

/// Target architecture for code generation.
pub enum Target {
    /// AArch64 (Arm64).
    AArch64,
    // Future: X86_64,
}

impl Target {
    pub(crate) fn triple(&self) -> &'static str {
        match self {
            Self::AArch64 => {
                #[cfg(target_os = "macos")]
                {
                    "aarch64-apple-darwin"
                }
                #[cfg(not(target_os = "macos"))]
                {
                    "aarch64-unknown-linux-gnu"
                }
            }
        }
    }

    /// Register the LLVM backend for this architecture. Idempotent.
    pub(crate) fn initialize(&self) {
        let config = InitializationConfig::default();
        match self {
            Self::AArch64 => {
                inkwell::targets::Target::initialize_aarch64(&config);
            }
        }
    }
}
