// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Generate the RISC-V assembly stub that wraps a compiled Move function
//! with SP1 syscall-based I/O (read inputs, call function, commit output, halt).

use std::fmt;

use compiler::FunctionInfo;

/// SP1 entry-stub generator for a Move function.
pub struct StubGenerator<'a> {
    symbol: &'a str,
    arg_count: usize,
    ret_count: usize,
}

impl<'a> From<&'a FunctionInfo> for StubGenerator<'a> {
    fn from(info: &'a FunctionInfo) -> Self {
        Self {
            symbol: &info.symbol,
            arg_count: info.arg_count,
            ret_count: info.ret_count,
        }
    }
}

impl<'a> StubGenerator<'a> {
    /// SP1 syscall codes (register t0).
    const SYSCALL_HALT: u32 = 0x00;
    const SYSCALL_WRITE: u32 = 0x02;
    const SYSCALL_HINT_LEN: u32 = 0xF0;
    const SYSCALL_HINT_READ: u32 = 0xF1;

    /// SP1 file descriptor for public-values output.
    const FD_PUBLIC_VALUES: u32 = 13;

    /// Generate RISC-V assembly for the SP1 entry stub.
    /// Generate RISC-V assembly for the SP1 entry stub.
    pub fn generate(&self) -> String {
        let mut output = String::new();
        self.write_asm(&mut output)
            .expect("formatting into String is infallible");
        output
    }

    #[cfg(test)]
    fn new(symbol: &'a str, arg_count: usize, ret_count: usize) -> Self {
        Self {
            symbol,
            arg_count,
            ret_count,
        }
    }

    fn write_asm(&self, out: &mut impl fmt::Write) -> fmt::Result {
        writeln!(out, "\t.text")?;
        writeln!(out, "\t.globl\t_start")?;
        writeln!(out, "\t.p2align\t2")?;
        writeln!(out, "\t.type\t_start,@function")?;
        writeln!(out, "_start:")?;

        // Reserve stack space for reading inputs (aligned to 16 bytes).
        let stack_frame = (self.arg_count * 8).max(16);
        let stack_frame = (stack_frame + 15) & !15;

        // Stack grows downward from just below the code segment.
        writeln!(out, "\tli\tsp, 0x78100000")?;
        writeln!(out, "\taddi\tsp, sp, -{stack_frame}")?;
        writeln!(out)?;

        // Read each u64 argument via HINT_LEN + HINT_READ ecalls.
        for arg_index in 0..self.arg_count {
            let offset = arg_index * 8;
            writeln!(out, "\t# Read argument {arg_index}")?;
            writeln!(out, "\tli\tt0, {:#x}", Self::SYSCALL_HINT_LEN)?;
            writeln!(out, "\tecall")?;
            writeln!(out, "\taddi\ta0, sp, {offset}")?;
            writeln!(out, "\tli\ta1, 8")?;
            writeln!(out, "\tli\tt0, {:#x}", Self::SYSCALL_HINT_READ)?;
            writeln!(out, "\tecall")?;
        }
        writeln!(out)?;

        // Load arguments into a0..a7.
        for arg_index in 0..self.arg_count {
            writeln!(out, "\tld\ta{arg_index}, {}(sp)", arg_index * 8)?;
        }

        // Call the Move function.
        writeln!(out, "\tcall\t{}", self.symbol)?;
        writeln!(out)?;

        // Commit return value to SP1 public outputs.
        if self.ret_count > 0 {
            writeln!(out, "\tsd\ta0, 0(sp)")?;
            writeln!(out, "\tli\ta0, {}", Self::FD_PUBLIC_VALUES)?;
            writeln!(out, "\tmv\ta1, sp")?;
            writeln!(out, "\tli\ta2, 8")?;
            writeln!(out, "\tli\tt0, {:#x}", Self::SYSCALL_WRITE)?;
            writeln!(out, "\tecall")?;
            writeln!(out)?;
        }

        // Halt with exit code 0.
        writeln!(out, "\tli\tt0, {:#x}", Self::SYSCALL_HALT)?;
        writeln!(out, "\tli\ta0, 0")?;
        writeln!(out, "\tecall")?;
        writeln!(out)?;

        // Move runtime abort handler.
        writeln!(out, "\t.globl\t__move_rt_arithmetic_error")?;
        writeln!(out, "\t.type\t__move_rt_arithmetic_error,@function")?;
        writeln!(out, "__move_rt_arithmetic_error:")?;
        writeln!(out, "\tli\tt0, {:#x}", Self::SYSCALL_HALT)?;
        writeln!(out, "\tli\ta0, 1")?;
        writeln!(out, "\tecall")?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::StubGenerator;

    #[test]
    fn stub_for_two_arg_function() {
        let stub = StubGenerator::new("_mv_0x0_M_add", 2, 1).generate();

        assert!(stub.contains("_start:"));
        assert!(stub.contains("__move_rt_arithmetic_error:"));
        assert!(stub.contains("call\t_mv_0x0_M_add"));
        assert!(stub.contains(".text"));
        assert_eq!(stub.matches("# Read argument").count(), 2);
    }

    #[test]
    fn stub_for_zero_arg_function() {
        let stub = StubGenerator::new("_mv_0x0_M_noop", 0, 0).generate();

        assert!(stub.contains("call\t_mv_0x0_M_noop"));
        assert!(!stub.contains("# Read argument"));
        assert!(!stub.contains(&format!("{}", StubGenerator::FD_PUBLIC_VALUES)));
    }

    #[test]
    fn stub_for_zero_args_with_return() {
        let stub = StubGenerator::new("_mv_0x0_M_get", 0, 1).generate();

        assert!(!stub.contains("# Read argument"));
        assert!(stub.contains(&format!("{}", StubGenerator::FD_PUBLIC_VALUES)));
        assert!(stub.contains("sd\ta0, 0(sp)"));
    }

    #[test]
    fn stub_stack_alignment() {
        // 3 args: raw frame = 24, must round up to 32 for 16-byte alignment.
        let stub = StubGenerator::new("_mv_0x0_M_f", 3, 0).generate();

        assert!(stub.contains("addi\tsp, sp, -32"));
    }
}
