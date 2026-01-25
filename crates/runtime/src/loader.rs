//! Dynamic library loading for native Move modules
//!
//! Provides a safe wrapper around libloading for loading compiled
//! Move modules and resolving function symbols.

use std::path::Path;

use libloading::{Library, Symbol as LibSymbol};

use crate::error::{RuntimeError, RuntimeResult};

/// A loaded native module (internal use only)
///
/// Wraps a dynamically loaded library (.dylib on macOS, .so on Linux).
/// This module is dangerous, use `ModuleCache` for the public API.
pub(crate) struct NativeModule {
    library: Library,
}

impl std::fmt::Debug for NativeModule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativeModule").finish_non_exhaustive()
    }
}

impl NativeModule {
    /// Load a native module from the specified path
    pub(crate) fn load<P: AsRef<Path>>(path: P) -> RuntimeResult<Self> {
        let path = path.as_ref();
        // Safety: The library is loaded with default flags.
        // The caller must ensure the library is safe to load.
        let library = unsafe { Library::new(path) }.map_err(|e| RuntimeError::LoadError {
            path: path.to_path_buf(),
            reason: e.to_string(),
        })?;

        Ok(Self { library })
    }

    /// Get a function pointer from the module
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - The type parameter `F` matches the actual function signature
    /// - The function is safe to call (e.g., properly instrumented)
    /// - The module (`self`) outlives usage of the returned function pointer
    pub(crate) unsafe fn get_function<F: Copy + 'static>(&self, name: &str) -> RuntimeResult<F> {
        // Note: dlsym handles platform symbol conventions automatically.
        // On macOS, dlsym("foo") finds "_foo" in Mach-O binaries.
        // On Linux, dlsym("foo") finds "foo" in ELF binaries.
        let symbol: LibSymbol<F> =
            self.library
                .get(name.as_bytes())
                .map_err(|_| RuntimeError::SymbolNotFound {
                    symbol: name.to_string(),
                })?;

        // Dereference to get the raw function pointer
        Ok(*symbol)
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::NativeModule;
    use crate::RuntimeError;

    #[test]
    fn test_load_nonexistent() {
        let result = NativeModule::load("/nonexistent/path/to/library.dylib");
        assert!(result.is_err());
        match result.unwrap_err() {
            RuntimeError::LoadError { path, .. } => {
                assert_eq!(
                    path,
                    Path::new("/nonexistent/path/to/library.dylib").to_path_buf()
                );
            }
            _ => panic!("expected LoadError"),
        }
    }
}
