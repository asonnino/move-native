// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

use inkwell::targets::InitializationConfig;

pub(crate) const CPU: &str = "generic";
/// Reserve x23 so LLVM never allocates the gas register.
pub(crate) const FEATURES: &str = "+reserve-x23";

/// Target architecture for code generation.
#[non_exhaustive]
pub enum Target {
    /// AArch64 (Arm64).
    Aarch64,
}

impl Target {
    /// Returns the target matching the host architecture.
    ///
    /// # Panics
    ///
    /// Panics if the host architecture is not supported.
    pub fn host() -> Self {
        #[cfg(target_arch = "aarch64")]
        {
            Self::Aarch64
        }
        #[cfg(not(target_arch = "aarch64"))]
        {
            panic!("unsupported host architecture; only aarch64 is supported")
        }
    }

    pub(crate) fn triple(&self) -> &'static str {
        match self {
            Self::Aarch64 => {
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
            Self::Aarch64 => {
                inkwell::targets::Target::initialize_aarch64(&config);
            }
        }
    }
}
