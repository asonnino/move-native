//! CLI for native-verifier
//!
//! Decodes and analyzes Arm64 object files, reporting gas instrumentation status.
//!
//! # Usage
//!
//! ```bash
//! # Assemble and verify
//! as -o test.o test.s
//! native-verifier test.o
//!
//! # Full pipeline with gas instrumentation
//! gas-instrument test.s > test_instrumented.s
//! as -o test.o test_instrumented.s
//! native-verifier test.o
//! ```

use std::{env, fs, process};

use cfg::CfgInstruction;
use native_verifier::decode_instructions;
use object::{Object, ObjectSection};

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() != 2 {
        eprintln!("Usage: {} <binary-file>", args[0]);
        process::exit(1);
    }

    let path = &args[1];

    let data = fs::read(path).unwrap_or_else(|e| {
        eprintln!("Failed to read {}: {}", path, e);
        process::exit(1);
    });

    // Parse the binary file
    let file = object::File::parse(&*data).unwrap_or_else(|e| {
        eprintln!("Failed to parse binary: {}", e);
        process::exit(1);
    });

    // Find the code section
    let text_section = file
        .section_by_name("__text") // Mach-O
        .or_else(|| file.section_by_name(".text")) // ELF
        .unwrap_or_else(|| {
            eprintln!("No code section found");
            process::exit(1);
        });

    let code = text_section.data().unwrap_or_else(|e| {
        eprintln!("Failed to read code section: {}", e);
        process::exit(1);
    });

    println!(
        "Code section: {} bytes ({} instructions)",
        code.len(),
        code.len() / 4
    );

    // Decode instructions
    let instructions = decode_instructions(code).unwrap_or_else(|e| {
        eprintln!("Decode error: {}", e);
        process::exit(1);
    });

    // Print summary
    let mut branch_count = 0;
    let mut back_edge_count = 0;
    let mut gas_decrement_count = 0;

    for instruction in &instructions {
        if instruction.is_branch() {
            branch_count += 1;
            if let Some(target) = instruction.branch_target() {
                if target <= instruction.offset {
                    back_edge_count += 1;
                }
            }
        }
        if instruction.is_gas_decrement() {
            gas_decrement_count += 1;
        }
    }

    println!("Decoded {} instructions", instructions.len());
    println!("  Branches: {}", branch_count);
    println!("  Back-edges: {}", back_edge_count);
    println!("  Gas decrements: {}", gas_decrement_count);

    // For now, just dump the first 20 instructions
    println!("\nFirst 20 instructions:");
    for instruction in instructions.iter().take(20) {
        println!("  {:04x}: {}", instruction.offset, instruction.instruction);
    }
}
