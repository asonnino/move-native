//! Dynamic library loading for native Move modules
//!
//! Provides a safe wrapper around libloading for loading compiled
//! Move modules and resolving function symbols.

use std::{
    io::Write,
    path::{Path, PathBuf},
    sync::Arc,
};

use libloading::{Library, Symbol as LibSymbol};
use tempfile::NamedTempFile;

use crate::error::{RuntimeError, RuntimeResult};

/// A function pointer with its module reference
///
/// This wrapper ensures the module stays loaded as long as the function
/// pointer is held. When this struct is dropped, the module reference
/// is released (though the module may remain loaded if other references
/// exist elsewhere).
///
/// # Type Parameters
///
/// * `F` - The function pointer type (e.g., `unsafe extern "C" fn()`)
#[derive(Clone)]
pub struct FunctionHandle<F: Copy> {
    ptr: F,
    _module: Arc<NativeModule>,
}

impl<F: Copy> FunctionHandle<F> {
    /// Get the raw function pointer
    ///
    /// The pointer remains valid as long as this `FunctionHandle` is alive.
    pub fn ptr(&self) -> F {
        self.ptr
    }
}

impl<F: Copy + std::fmt::Debug> std::fmt::Debug for FunctionHandle<F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("FunctionHandle")
            .field("ptr", &self.ptr)
            .finish_non_exhaustive()
    }
}

/// A loaded native module (internal use only)
///
/// Wraps a dynamically loaded library (.dylib on macOS, .so on Linux).
/// This module is dangerous, use `ModuleCache` for the public API.
pub struct NativeModule {
    library: Library,
}

impl std::fmt::Debug for NativeModule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativeModule").finish_non_exhaustive()
    }
}

impl NativeModule {
    /// Load a native module from the specified path
    ///
    /// Returns an `Arc<NativeModule>` to ensure the module can be shared
    /// with `FunctionHandle`s that reference functions within it.
    pub fn load_from_file<P: AsRef<Path>>(path: P) -> RuntimeResult<Arc<Self>> {
        let path = path.as_ref();
        // Safety: The library is loaded with default flags.
        // The caller must ensure the library is safe to load.
        let library = unsafe { Library::new(path) }.map_err(|e| RuntimeError::LoadError {
            path: path.to_path_buf(),
            reason: e.to_string(),
        })?;

        Ok(Arc::new(Self { library }))
    }

    /// Load a native module from bytes
    ///
    /// Writes bytes to a temporary file and loads via dlopen.
    ///
    /// TODO: Avoid writing to disk - use memfd on Linux or direct mmap.
    pub fn load_from_bytes(bytes: &[u8]) -> RuntimeResult<Arc<Self>> {
        // Platform-appropriate extension
        #[cfg(target_os = "macos")]
        let suffix = ".dylib";
        #[cfg(not(target_os = "macos"))]
        let suffix = ".so";

        // Write bytes to temp file
        let mut temp_file =
            NamedTempFile::with_suffix(suffix).map_err(|e| RuntimeError::LoadError {
                path: PathBuf::from("<tempfile>"),
                reason: format!("failed to create temp file: {e}"),
            })?;

        temp_file
            .write_all(bytes)
            .map_err(|e| RuntimeError::LoadError {
                path: PathBuf::from("<tempfile>"),
                reason: format!("write to temp file failed: {e}"),
            })?;

        // Load the library (temp file deleted after this, but dlopen keeps mapping valid)
        Self::load_from_file(temp_file.path())
    }

    /// Get a function handle from the module
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - The type parameter `F` matches the actual function signature
    /// - The function is safe to call (e.g., properly instrumented)
    pub unsafe fn get_function<F: Copy + 'static>(
        self: Arc<Self>,
        name: &str,
    ) -> RuntimeResult<FunctionHandle<F>> {
        // Note: dlsym handles platform symbol conventions automatically.
        // On macOS, dlsym("foo") finds "_foo" in Mach-O binaries.
        // On Linux, dlsym("foo") finds "foo" in ELF binaries.
        let symbol: LibSymbol<F> =
            self.library
                .get(name.as_bytes())
                .map_err(|_| RuntimeError::SymbolNotFound {
                    symbol: name.to_string(),
                })?;

        Ok(FunctionHandle {
            ptr: *symbol,
            _module: self,
        })
    }
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::NativeModule;
    use crate::RuntimeError;

    #[test]
    fn test_load_nonexistent() {
        let result = NativeModule::load_from_file("/nonexistent/path/to/library.dylib");
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
