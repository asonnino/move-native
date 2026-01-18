//! Gas instrumentation CLI tool
//!
//! Reads Arm64 assembly from stdin, instruments it with gas checks, and writes to stdout.
//!
//! Usage:
//!     cat test.s | gas-instrument > test_instrumented.s

use std::io::{self, Read};

use gas_instrument::{cfg, instrument, parser::ParsedAssembly};

fn main() {
    let args: Vec<String> = std::env::args().collect();

    // Check for --help
    if args.iter().any(|a| a == "--help" || a == "-h") {
        eprintln!("gas-instrument - Arm64 assembly gas instrumentation tool");
        eprintln!();
        eprintln!("Usage: cat input.s | gas-instrument > output.s");
        eprintln!();
        eprintln!("Options:");
        eprintln!("  --help, -h  Show this help message");
        std::process::exit(0);
    }

    // Read input from stdin
    let mut input = String::new();
    if let Err(e) = io::stdin().read_to_string(&mut input) {
        eprintln!("Error reading stdin: {e}");
        std::process::exit(1);
    }

    // Parse assembly
    let asm = ParsedAssembly::parse(&input);

    // Build CFG (resolves labels to instruction indices)
    let cfg_result = match cfg::build(&asm) {
        Ok(result) => result,
        Err(e) => {
            eprintln!("Error building CFG: {e}");
            std::process::exit(1);
        }
    };

    // Instrument
    let output = instrument::instrument(asm.lines(), &cfg_result);

    // Write to stdout
    print!("{output}");
}
