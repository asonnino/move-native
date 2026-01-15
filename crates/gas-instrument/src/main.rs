//! Gas instrumentation CLI tool
//!
//! Reads Arm64 assembly from stdin, instruments it with gas checks, and writes to stdout.
//!
//! Usage:
//!     cat test.s | gas-instrument > test_instrumented.s

use std::io::{self, Read};

use gas_instrument::{cfg, instrument, parse};

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
        eprintln!("Error reading stdin: {}", e);
        std::process::exit(1);
    }

    // Parse assembly
    let lines = match parse(&input) {
        Ok(lines) => lines,
        Err(e) => {
            eprintln!("Parse error: {}", e);
            std::process::exit(1);
        }
    };

    // Build CFG
    let cfg = cfg::Cfg::from_lines(&lines);

    // Instrument
    let output = instrument::instrument(&lines, &cfg);

    // Write to stdout
    print!("{}", output);
}
