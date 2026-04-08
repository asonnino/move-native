// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! ELF object file output from the compiler, with relocation support.

use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget};

use crate::error::{CompileError, CompileResult};

/// Compiled object file (`.o` bytes) produced by [`Compiler::emit_object`].
///
/// Wraps the raw ELF relocatable object and provides methods to extract
/// linked code without needing an external linker.
pub struct ObjectFile(Vec<u8>);

impl ObjectFile {
    pub(crate) fn new(bytes: Vec<u8>) -> Self {
        Self(bytes)
    }

    /// Raw `.o` bytes.
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Extract the `.text` section with all internal relocations applied,
    /// plus the offset of a named entry-point symbol.
    ///
    /// This is a minimal in-process linker: it resolves PC-relative call
    /// relocations so the returned code bytes can be loaded directly.
    pub fn linked_text(&self, entry: &str) -> CompileResult<LinkedText> {
        let obj = object::File::parse(self.as_bytes())
            .map_err(|e| CompileError::codegen(format!("failed to parse object: {e}")))?;

        let text = obj
            .section_by_name(".text")
            .ok_or_else(|| CompileError::codegen("no .text section"))?;
        let text_index = text.index();
        let text_addr = text.address();
        let mut code = text
            .data()
            .map_err(|e| CompileError::codegen(format!("failed to read .text: {e}")))?
            .to_vec();

        // Build symbol index → offset-in-.text map.
        let mut symbols: std::collections::HashMap<object::SymbolIndex, u64> =
            std::collections::HashMap::new();
        for sym in obj.symbols() {
            if sym.section_index() == Some(text_index) {
                symbols.insert(sym.index(), sym.address() - text_addr);
            }
        }

        // Apply relocations.
        for (offset, reloc) in text.relocations() {
            let target_offset = match reloc.target() {
                RelocationTarget::Symbol(sym_idx) => {
                    symbols.get(&sym_idx).copied().ok_or_else(|| {
                        let name = obj
                            .symbol_by_index(sym_idx)
                            .and_then(|s| s.name().map(|n| n.to_string()))
                            .unwrap_or_else(|_| "?".into());
                        CompileError::codegen(format!("unresolved symbol: {name}"))
                    })?
                }
                _ => return Err(CompileError::codegen("unsupported relocation target")),
            };

            let flags = reloc.flags();
            let is_call = matches!(
                flags,
                object::RelocationFlags::Elf {
                    r_type: object::elf::R_RISCV_CALL | object::elf::R_RISCV_CALL_PLT
                }
            );

            if is_call {
                apply_riscv_call(&mut code, offset, target_offset);
            } else {
                return Err(CompileError::codegen(format!(
                    "unsupported relocation at offset {offset:#x}: {flags:?}"
                )));
            }
        }

        // Find entry symbol (in .text section, any symbol kind — inline asm
        // symbols may not have SymbolKind::Text).
        let entry_offset = obj
            .symbols()
            .find(|s| s.name() == Ok(entry) && s.section_index() == Some(text_index))
            .map(|s| s.address() - text_addr)
            .ok_or_else(|| CompileError::codegen(format!("symbol '{entry}' not found")))?;

        Ok(LinkedText { code, entry_offset })
    }
}

/// Relocated `.text` code ready for direct execution or ELF packaging.
#[derive(Debug)]
pub struct LinkedText {
    /// Machine code bytes with all internal relocations resolved.
    pub code: Vec<u8>,
    /// Offset of the entry-point symbol within `code`.
    pub entry_offset: u64,
}

/// Apply a RISC-V CALL/CALL_PLT relocation: patch an auipc+jalr pair
/// with the PC-relative offset to the target.
fn apply_riscv_call(code: &mut [u8], offset: u64, target_offset: u64) {
    let rel = target_offset as i64 - offset as i64;

    let hi20 = ((rel + 0x800) >> 12) & 0xfffff;
    let lo12 = rel - (hi20 << 12);

    let off = offset as usize;
    let auipc = u32::from_le_bytes(code[off..off + 4].try_into().unwrap());
    let jalr = u32::from_le_bytes(code[off + 4..off + 8].try_into().unwrap());

    // auipc: imm[31:12] in bits [31:12]
    let auipc = (auipc & 0xfff) | ((hi20 as u32) << 12);
    // jalr: imm[11:0] in bits [31:20]
    let jalr = (jalr & 0xfffff) | ((lo12 as u32 & 0xfff) << 20);

    code[off..off + 4].copy_from_slice(&auipc.to_le_bytes());
    code[off + 4..off + 8].copy_from_slice(&jalr.to_le_bytes());
}

#[cfg(test)]
mod tests {
    use super::apply_riscv_call;

    /// Decode the PC-relative offset from a patched auipc+jalr pair.
    fn decode_call_offset(code: &[u8], off: usize) -> i64 {
        let auipc = u32::from_le_bytes(code[off..off + 4].try_into().unwrap());
        let jalr = u32::from_le_bytes(code[off + 4..off + 8].try_into().unwrap());
        // Sign-extend hi20 (auipc uses bits [31:12] as a signed upper immediate).
        let hi20 = ((auipc as i32) >> 12) as i64;
        // Sign-extend lo12 (jalr uses bits [31:20] as a signed 12-bit immediate).
        let lo12 = ((jalr as i32) >> 20) as i64;
        (hi20 << 12) + lo12
    }

    /// Create a buffer with a bare auipc+jalr pair at the given offset.
    fn make_call_pair(size: usize, off: usize) -> Vec<u8> {
        let mut code = vec![0u8; size];
        // auipc ra, 0  →  0x00000097
        code[off..off + 4].copy_from_slice(&0x0000_0097u32.to_le_bytes());
        // jalr ra, ra, 0  →  0x000080E7
        code[off + 4..off + 8].copy_from_slice(&0x0000_80E7u32.to_le_bytes());
        code
    }

    #[test]
    fn forward_call() {
        let mut code = make_call_pair(0x200, 0);
        apply_riscv_call(&mut code, 0, 0x100);
        assert_eq!(decode_call_offset(&code, 0), 0x100);
    }

    #[test]
    fn backward_call() {
        let mut code = make_call_pair(0x200, 0x100);
        apply_riscv_call(&mut code, 0x100, 0);
        assert_eq!(decode_call_offset(&code, 0x100), -0x100);
    }

    #[test]
    fn zero_offset_call() {
        let mut code = make_call_pair(16, 0);
        apply_riscv_call(&mut code, 0, 0);
        assert_eq!(decode_call_offset(&code, 0), 0);
    }

    #[test]
    fn large_forward_call() {
        let mut code = make_call_pair(16, 0);
        apply_riscv_call(&mut code, 0, 0x8_0000);
        assert_eq!(decode_call_offset(&code, 0), 0x8_0000);
    }

    #[test]
    fn large_backward_call() {
        let mut code = make_call_pair(0x10_0000, 0x8_0000);
        apply_riscv_call(&mut code, 0x8_0000, 0);
        assert_eq!(decode_call_offset(&code, 0x8_0000), -0x8_0000);
    }
}
