// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Minimal in-process linker and ELF builder: resolve relocations in a
//! `.o` file, extract the `.text` section, and produce an SP1-compatible ELF.

use std::collections::HashMap;

use object::{Object, ObjectSection, ObjectSymbol, RelocationTarget};

use compiler::ObjectFile;

use crate::error::{ZkError, ZkResult};

/// SP1 requires all code segments at addresses >= 0x78000000.
const SP1_TEXT_BASE: u64 = 0x78100000;

/// Pre-link state: holds a compiled object file and entry symbol name.
pub struct Linker<'a> {
    object_file: &'a ObjectFile,
    entry: &'a str,
}

impl<'a> Linker<'a> {
    pub fn new(object_file: &'a ObjectFile, entry: &'a str) -> Self {
        Self { object_file, entry }
    }

    /// Parse the `.o` file, resolve all relocations in `.text`, and return
    /// the linked code bytes with the entry symbol's offset.
    pub fn link(&self) -> ZkResult<LinkedText> {
        let file = object::File::parse(self.object_file.as_bytes())
            .map_err(|e| ZkError::Linker(format!("failed to parse object: {e}")))?;

        let text_section = file
            .section_by_name(".text")
            .ok_or_else(|| ZkError::Linker("no .text section".into()))?;
        let section_index = text_section.index();
        let section_address = text_section.address();
        let code = text_section
            .data()
            .map_err(|e| ZkError::Linker(format!("failed to read .text: {e}")))?
            .to_vec();

        // Build symbol index -> offset-in-.text map.
        let mut symbol_offsets: HashMap<_, _> = HashMap::new();
        for symbol in file.symbols() {
            if symbol.section_index() == Some(section_index) {
                let offset = symbol
                    .address()
                    .checked_sub(section_address)
                    .ok_or_else(|| {
                        ZkError::Linker(format!(
                            "symbol address {:#x} is below section base {:#x}",
                            symbol.address(),
                            section_address,
                        ))
                    })?;
                symbol_offsets.insert(symbol.index(), offset);
            }
        }

        // Find entry symbol (in .text section, any symbol kind — inline asm
        // symbols may not have SymbolKind::Text).
        let entry_sym = file
            .symbols()
            .find(|s| s.name() == Ok(self.entry) && s.section_index() == Some(section_index))
            .ok_or_else(|| ZkError::Linker(format!("symbol '{}' not found", self.entry)))?;
        let entry_offset = entry_sym
            .address()
            .checked_sub(section_address)
            .ok_or_else(|| {
                ZkError::Linker(format!(
                    "entry symbol address {:#x} is below section base {:#x}",
                    entry_sym.address(),
                    section_address,
                ))
            })?;

        let mut linked = LinkedText { code, entry_offset };

        // Apply relocations.
        for (offset, relocation) in text_section.relocations() {
            let target_offset = match relocation.target() {
                RelocationTarget::Symbol(symbol_index) => {
                    symbol_offsets.get(&symbol_index).copied().ok_or_else(|| {
                        let name = file
                            .symbol_by_index(symbol_index)
                            .and_then(|s| s.name().map(|n| n.to_string()))
                            .unwrap_or_else(|_| "?".into());
                        ZkError::Linker(format!("unresolved symbol: {name}"))
                    })?
                }
                _ => return Err(ZkError::Linker("unsupported relocation target".into())),
            };

            let flags = relocation.flags();
            let is_call = matches!(
                flags,
                object::RelocationFlags::Elf {
                    r_type: object::elf::R_RISCV_CALL | object::elf::R_RISCV_CALL_PLT
                }
            );

            if is_call {
                linked.apply_riscv_call(offset, target_offset)?;
            } else {
                return Err(ZkError::Linker(format!(
                    "unsupported relocation at offset {offset:#x}: {flags:?}"
                )));
            }
        }

        Ok(linked)
    }
}

/// Relocated `.text` code ready for ELF packaging.
#[derive(Debug)]
pub struct LinkedText {
    /// Machine code bytes with all internal relocations resolved.
    pub code: Vec<u8>,
    /// Offset of the entry-point symbol within `code`.
    pub entry_offset: u64,
}

impl LinkedText {
    /// Apply a RISC-V CALL/CALL_PLT relocation: patch an auipc+jalr pair
    /// with the PC-relative offset to the target.
    fn apply_riscv_call(&mut self, instruction_offset: u64, target_offset: u64) -> ZkResult<()> {
        let relative = target_offset as i64 - instruction_offset as i64;

        let upper = ((relative + 0x800) >> 12) & 0xfffff;
        let lower = relative - (upper << 12);

        let position = instruction_offset as usize;
        let pair = self
            .code
            .get(position..position + 8)
            .ok_or_else(|| ZkError::Linker(format!("relocation at {position:#x} out of bounds")))?;
        let auipc = u32::from_le_bytes(pair[..4].try_into().unwrap());
        let jalr = u32::from_le_bytes(pair[4..].try_into().unwrap());

        // auipc: imm[31:12] in bits [31:12]
        let auipc = (auipc & 0xfff) | ((upper as u32) << 12);
        // jalr: imm[11:0] in bits [31:20]
        let jalr = (jalr & 0xfffff) | ((lower as u32 & 0xfff) << 20);

        self.code[position..position + 4].copy_from_slice(&auipc.to_le_bytes());
        self.code[position + 4..position + 8].copy_from_slice(&jalr.to_le_bytes());
        Ok(())
    }

    /// Build a minimal SP1-compatible ELF from linked text.
    ///
    /// Layout: ELF header (64B) + one program header (56B) + code.
    pub fn build_elf(&self) -> ZkResult<Vec<u8>> {
        let entry = SP1_TEXT_BASE + self.entry_offset;
        let code_offset: u64 = 64 + 56;
        let code_len = self.code.len() as u64;

        let mut elf = Vec::with_capacity(code_offset as usize + self.code.len());

        // ELF header (64 bytes)
        elf.extend_from_slice(&[0x7f, b'E', b'L', b'F']); // magic
        elf.push(2); // ELFCLASS64
        elf.push(1); // ELFDATA2LSB
        elf.push(1); // EV_CURRENT
        elf.push(0); // ELFOSABI_NONE
        elf.extend_from_slice(&[0; 8]); // padding

        elf.extend_from_slice(&2u16.to_le_bytes()); // e_type: ET_EXEC
        elf.extend_from_slice(&243u16.to_le_bytes()); // e_machine: EM_RISCV
        elf.extend_from_slice(&1u32.to_le_bytes()); // e_version
        elf.extend_from_slice(&entry.to_le_bytes()); // e_entry
        elf.extend_from_slice(&64u64.to_le_bytes()); // e_phoff
        elf.extend_from_slice(&0u64.to_le_bytes()); // e_shoff
        elf.extend_from_slice(&0u32.to_le_bytes()); // e_flags
        elf.extend_from_slice(&64u16.to_le_bytes()); // e_ehsize
        elf.extend_from_slice(&56u16.to_le_bytes()); // e_phentsize
        elf.extend_from_slice(&1u16.to_le_bytes()); // e_phnum
        elf.extend_from_slice(&64u16.to_le_bytes()); // e_shentsize
        elf.extend_from_slice(&0u16.to_le_bytes()); // e_shnum
        elf.extend_from_slice(&0u16.to_le_bytes()); // e_shstrndx
        debug_assert_eq!(elf.len(), 64);

        // Program header (56 bytes)
        elf.extend_from_slice(&1u32.to_le_bytes()); // p_type: PT_LOAD
        elf.extend_from_slice(&5u32.to_le_bytes()); // p_flags: PF_R | PF_X
        elf.extend_from_slice(&code_offset.to_le_bytes()); // p_offset
        elf.extend_from_slice(&SP1_TEXT_BASE.to_le_bytes()); // p_vaddr
        elf.extend_from_slice(&SP1_TEXT_BASE.to_le_bytes()); // p_paddr
        elf.extend_from_slice(&code_len.to_le_bytes()); // p_filesz
        elf.extend_from_slice(&code_len.to_le_bytes()); // p_memsz
        elf.extend_from_slice(&4u64.to_le_bytes()); // p_align
        debug_assert_eq!(elf.len(), 120);

        // Code
        elf.extend_from_slice(&self.code);

        Ok(elf)
    }
}

#[cfg(test)]
mod tests {
    use compiler::module::CompiledModuleBuilder;
    use compiler::{Compiler, Target};

    use super::{LinkedText, Linker};

    #[test]
    fn link_errors_on_missing_entry_symbol() {
        let module = CompiledModuleBuilder::add();
        let ctx = inkwell::context::Context::create();
        let object = Compiler::new(&Target::Riscv64, &ctx, &module, &[])
            .unwrap()
            .emit_object()
            .unwrap();
        assert!(Linker::new(&object, "no_such_entry").link().is_err());
    }

    /// Decode the PC-relative offset from a patched auipc+jalr pair.
    fn decode_call_offset(code: &[u8], position: usize) -> i64 {
        let auipc = u32::from_le_bytes(code[position..position + 4].try_into().unwrap());
        let jalr = u32::from_le_bytes(code[position + 4..position + 8].try_into().unwrap());
        let upper = ((auipc as i32) >> 12) as i64;
        let lower = ((jalr as i32) >> 20) as i64;
        (upper << 12) + lower
    }

    /// Create a `LinkedText` with a bare auipc+jalr pair at the given position.
    fn make_linked(size: usize, position: usize) -> LinkedText {
        let mut code = vec![0u8; size];
        code[position..position + 4].copy_from_slice(&0x0000_0097u32.to_le_bytes());
        code[position + 4..position + 8].copy_from_slice(&0x0000_80E7u32.to_le_bytes());
        LinkedText {
            code,
            entry_offset: 0,
        }
    }

    #[test]
    fn forward_call() {
        let mut linked = make_linked(0x200, 0);
        linked.apply_riscv_call(0, 0x100).unwrap();
        assert_eq!(decode_call_offset(&linked.code, 0), 0x100);
    }

    #[test]
    fn backward_call() {
        let mut linked = make_linked(0x200, 0x100);
        linked.apply_riscv_call(0x100, 0).unwrap();
        assert_eq!(decode_call_offset(&linked.code, 0x100), -0x100);
    }

    #[test]
    fn zero_offset_call() {
        let mut linked = make_linked(16, 0);
        linked.apply_riscv_call(0, 0).unwrap();
        assert_eq!(decode_call_offset(&linked.code, 0), 0);
    }

    #[test]
    fn rounding_boundary_call() {
        // Offset 0x800: lower 12 bits are negative (-0x800), so upper
        // must compensate via the +0x800 rounding to become 0x1000.
        let mut linked = make_linked(0x1000, 0);
        linked.apply_riscv_call(0, 0x800).unwrap();
        assert_eq!(decode_call_offset(&linked.code, 0), 0x800);
    }

    #[test]
    fn out_of_bounds_call() {
        let mut linked = make_linked(16, 0);
        // Offset 12 means we need bytes 12..20, but buffer is only 16 bytes.
        assert!(linked.apply_riscv_call(12, 0).is_err());
    }

    #[test]
    fn build_elf_header() {
        let code = vec![0x93, 0x00, 0x00, 0x00]; // 4 bytes of code
        let linked = LinkedText {
            code: code.clone(),
            entry_offset: 0,
        };
        let elf = linked.build_elf().unwrap();

        // Total size: 64 (ELF header) + 56 (program header) + 4 (code).
        assert_eq!(elf.len(), 124);
        // ELF magic.
        assert_eq!(&elf[0..4], &[0x7f, b'E', b'L', b'F']);
        // e_entry at offset 24: SP1_TEXT_BASE + 0.
        let entry = u64::from_le_bytes(elf[24..32].try_into().unwrap());
        assert_eq!(entry, super::SP1_TEXT_BASE);
        // Code at offset 120.
        assert_eq!(&elf[120..], &code);
    }

    #[test]
    fn build_elf_with_entry_offset() {
        let linked = LinkedText {
            code: vec![0; 32],
            entry_offset: 16,
        };
        let elf = linked.build_elf().unwrap();

        let entry = u64::from_le_bytes(elf[24..32].try_into().unwrap());
        assert_eq!(entry, super::SP1_TEXT_BASE + 16);
    }
}
