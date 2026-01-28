//! Module abstractions for compiled native code
//!
//! This module contains the types that represent compiled modules and their functions:
//! - `CompiledModule`: Raw bytes + entry points (what gets stored/transferred)
//! - `LoadedModule`: A module loaded into a slot (internal)
//! - `FunctionHandle`: A reference to a function that keeps its slot alive

use std::{collections::HashMap, fmt, marker::PhantomData, sync::Arc};

use crate::slot::SlotHandle;

/// Compiled module output from the compiler
///
/// Contains raw executable bytes and entry point offsets.
/// This is what gets stored in the database/cache.
#[derive(Clone, Debug)]
pub struct CompiledModule {
    /// Raw executable bytes (flat binary, no ELF wrapper)
    pub code: Vec<u8>,
    /// Function name -> offset in code
    pub entry_points: HashMap<String, u32>,
}

impl CompiledModule {
    /// Create a new compiled module
    pub fn new(code: Vec<u8>, entry_points: HashMap<String, u32>) -> Self {
        Self { code, entry_points }
    }

    /// Create a compiled module with a single entry point at offset 0
    pub fn with_single_entry(code: Vec<u8>, name: impl Into<String>) -> Self {
        Self::new(code, HashMap::from([(name.into(), 0)]))
    }

    /// Create a minimal test module that returns a constant value
    ///
    /// Generates: `mov x0, #return_val; ret`
    #[cfg(test)]
    pub fn new_for_test(return_val: u16, name: &str) -> Self {
        // mov x0, #N (immediate in bits 20:5)
        let mov = 0xd2800000u32 | ((return_val as u32) << 5);
        let ret = 0xd65f03c0u32;
        let code: Vec<u8> = mov
            .to_le_bytes()
            .into_iter()
            .chain(ret.to_le_bytes())
            .collect();
        Self::with_single_entry(code, name)
    }
}

/// A module loaded into a slot
///
/// Contains the slot handle and entry point offsets. Shared via Arc
/// to allow multiple FunctionHandles to reference the same loaded code.
pub(crate) struct LoadedModule {
    /// The slot containing the executable code
    pub(crate) handle: SlotHandle,
    /// Function name -> offset in code
    pub(crate) entry_points: HashMap<String, u32>,
}

/// Handle to a function in a loaded module
///
/// Keeps the underlying slot alive while the handle exists.
/// The slot is only returned to the pool when all FunctionHandles
/// (and the cache entry) are dropped.
pub struct FunctionHandle<F> {
    /// Reference to the loaded module (keeps slot alive)
    module: Arc<LoadedModule>,
    /// Offset of the function within the code
    offset: u32,
    /// Marker for the function type
    _marker: PhantomData<F>,
}

impl<F> fmt::Debug for FunctionHandle<F> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FunctionHandle")
            .field("offset", &self.offset)
            .finish_non_exhaustive()
    }
}

impl<F: Copy> FunctionHandle<F> {
    /// Create a new function handle
    ///
    /// # Safety
    ///
    /// The caller must ensure:
    /// - `offset` points to a valid function entry point
    /// - `F` matches the actual function signature at that offset
    pub(crate) unsafe fn new(module: Arc<LoadedModule>, offset: u32) -> Self {
        Self {
            module,
            offset,
            _marker: PhantomData,
        }
    }

    /// Get the function pointer
    pub fn as_ptr(&self) -> F {
        // Safety: The caller of `new` guaranteed the offset and type are valid
        unsafe { self.module.handle.get_function(self.offset as usize) }
    }
}

#[cfg(test)]
mod tests {
    use super::CompiledModule;

    #[test]
    fn test_compiled_module() {
        let code = vec![0x40, 0x05, 0x80, 0xd2, 0xc0, 0x03, 0x5f, 0xd6];
        let module = CompiledModule::with_single_entry(code.clone(), "main");

        assert_eq!(module.code, code);
        assert_eq!(module.entry_points.get("main"), Some(&0));
    }
}
