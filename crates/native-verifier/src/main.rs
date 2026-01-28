//! CLI for native-verifier
//!
//! Verifies Arm64 object files for safe deterministic execution.
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

use native_verifier::{Verifier, decode_instructions};
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
        "Verifying: {} ({} bytes, {} instructions)",
        path,
        code.len(),
        code.len() / 4
    );

    // Decode instructions
    let instructions = decode_instructions(code).unwrap_or_else(|e| {
        eprintln!("Decode error: {}", e);
        process::exit(1);
    });

    // Run verification
    let result = Verifier::new(&instructions).verify();

    if result.is_ok() {
        println!("Verification PASSED");
    } else {
        println!("Verification FAILED ({} errors):", result.errors().len());
        for error in result.errors() {
            println!("  {}", error);
        }
        process::exit(1);
    }
}
