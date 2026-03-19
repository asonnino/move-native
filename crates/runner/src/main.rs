// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Unified CLI for the Move native compilation pipeline

use std::fs;
use std::io::{self, Read};
use std::process;

use clap::{Parser, Subcommand};
use object::{Object, ObjectSection};

use runner::PipelineError;

#[derive(Parser)]
#[command(name = "runner", about = "Move native compilation pipeline")]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Full pipeline: .mv bytecode -> verified binary blob
    Prepare {
        /// Input .mv file
        input: String,
        /// Output file path
        #[arg(short, long)]
        output: String,
    },
    /// Compile Move bytecode to assembly (for debugging)
    Compile {
        /// Input .mv file
        input: String,
    },
    /// Instrument assembly with gas checks
    Instrument {
        /// Input .s file (reads from stdin if omitted)
        input: Option<String>,
    },
    /// Verify an assembled object file
    Verify {
        /// Input .o file
        input: String,
    },
}

fn main() {
    let cli = Cli::parse();

    let result = match cli.command {
        Commands::Prepare { input, output } => cmd_prepare(&input, &output),
        Commands::Compile { input } => cmd_compile(&input),
        Commands::Instrument { input } => cmd_instrument(input.as_deref()),
        Commands::Verify { input } => cmd_verify(&input),
    };

    if let Err(e) = result {
        eprintln!("Error: {e}");
        process::exit(1);
    }
}

fn cmd_prepare(input: &str, output: &str) -> Result<(), PipelineError> {
    let bytecode = fs::read(input).map_err(PipelineError::Io)?;
    let module = runner::prepare(&bytecode)?;

    // Serialize: entry_point_count (u32) | [name_len (u32) | name | offset (u32)] | code
    let mut blob = Vec::new();
    blob.extend((module.entry_points.len() as u32).to_le_bytes());
    for (name, offset) in &module.entry_points {
        blob.extend((name.len() as u32).to_le_bytes());
        blob.extend(name.as_bytes());
        blob.extend(offset.to_le_bytes());
    }
    blob.extend(&module.code);

    fs::write(output, &blob).map_err(PipelineError::Io)?;
    eprintln!(
        "Prepared {} ({} bytes, {} entry points)",
        input,
        module.code.len(),
        module.entry_points.len()
    );
    Ok(())
}

fn cmd_compile(input: &str) -> Result<(), PipelineError> {
    let bytecode = fs::read(input).map_err(PipelineError::Io)?;
    let mut asm = compiler::compile(&compiler::Target::host(), &bytecode)?;
    asm.add_symbol_aliases();
    print!("{asm}");
    Ok(())
}

fn cmd_instrument(input: Option<&str>) -> Result<(), PipelineError> {
    let source = match input {
        Some(path) => fs::read_to_string(path).map_err(PipelineError::Io)?,
        None => {
            let mut buf = String::new();
            io::stdin()
                .read_to_string(&mut buf)
                .map_err(PipelineError::Io)?;
            buf
        }
    };

    let parsed = instrumenter::ParsedAssembly::parse(&source);
    let cfg_result = instrumenter::build_cfg(&parsed)?;
    let output = instrumenter::instrument(parsed.lines(), &cfg_result)?;
    print!("{output}");
    Ok(())
}

fn cmd_verify(input: &str) -> Result<(), PipelineError> {
    let data = fs::read(input).map_err(PipelineError::Io)?;

    let file =
        object::File::parse(&*data).map_err(|e| PipelineError::AssemblerFailed(e.to_string()))?;

    let text_section = file
        .section_by_name("__text")
        .or_else(|| file.section_by_name(".text"))
        .ok_or(PipelineError::NoCodeSection)?;

    let code = text_section
        .data()
        .map_err(|e| PipelineError::AssemblerFailed(e.to_string()))?;

    eprintln!(
        "Verifying: {} ({} bytes, {} instructions)",
        input,
        code.len(),
        code.len() / 4
    );

    let instructions = verifier::decode_instructions(code)?;
    let result = verifier::Verifier::new(&instructions).verify();

    if result.is_ok() {
        eprintln!("Verification PASSED");
        Ok(())
    } else {
        for error in result.errors() {
            eprintln!("  {error}");
        }
        Err(PipelineError::Verification(result.errors().to_vec()))
    }
}
