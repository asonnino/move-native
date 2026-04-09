// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! CLI for generating and verifying ZK proofs of Move contract execution.

mod error;
mod linker;
mod proof;
mod stub;

use std::fs;

use clap::Parser;
use inkwell::context::Context;
use move_binary_format::CompiledModule;
use sp1_sdk::SP1Stdin;
use tracing::{error, info};

use compiler::{ModuleInfo, Target};
use error::{ZkError, ZkResult};
use linker::Linker;
use proof::Prover;
use stub::StubGenerator;

#[derive(Parser)]
#[command(name = "zk", about = "ZK proof generation for Move contracts")]
struct Cli {
    /// Input .mv file (compiled Move bytecode)
    input: String,

    /// Function to prove (e.g. "add"). If omitted, uses the first
    /// non-native public function in the module.
    #[arg(short, long)]
    function: Option<String>,

    /// u64 inputs as comma-separated values (e.g. "42,58")
    #[arg(short, long, value_delimiter = ',')]
    inputs: Vec<u64>,

    /// Use mock prover (fast, no real proof). Omit for CPU proving.
    #[arg(long)]
    mock: bool,
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt::init();
    let cli = Cli::parse();
    if let Err(e) = run(&cli).await {
        error!("{e}");
    }
}

async fn run(cli: &Cli) -> ZkResult<()> {
    // 1. Read and deserialize the Move bytecode.
    let bytecode = fs::read(&cli.input).map_err(ZkError::Io)?;
    let module = CompiledModule::deserialize_with_defaults(&bytecode)
        .map_err(|e| ZkError::Function(e.to_string()))?;

    // 2. Find the target function.
    let info = ModuleInfo::from_module(&module)?;
    let function = match &cli.function {
        Some(name) => info
            .function(name)
            .ok_or_else(|| ZkError::Function(format!("function '{name}' not found")))?,
        None => info.only_function().ok_or_else(|| {
            let names: Vec<_> = info
                .functions
                .iter()
                .filter(|f| !f.is_native)
                .map(|f| f.name.as_str())
                .collect();
            ZkError::Function(format!(
                "multiple functions in module, use --function: {names:?}"
            ))
        })?,
    };
    info!(
        name = %function.name,
        args = function.arg_count,
        returns = function.ret_count,
        "Selected function"
    );

    // 3. Generate the stub assembly.
    let stub_asm = StubGenerator::from(function).generate();

    // 4. Compile Move + stub → single .o via LLVM.
    info!("Compiling to RISC-V");
    let context = Context::create();
    let compiler = compiler::Compiler::new(&Target::Riscv64, &context, &module, &[])?;
    compiler.set_module_assembly(&stub_asm);
    let object = compiler.emit_object()?;

    // 5. Link relocations and wrap in SP1-compatible ELF.
    info!("Building ELF");
    let elf_bytes = Linker::new(&object, "_start").link()?.build_elf()?;
    info!(bytes = elf_bytes.len(), "ELF ready");

    // 6. Validate inputs.
    if cli.inputs.len() != function.arg_count {
        return Err(ZkError::Sp1(format!(
            "expected {} inputs, got {}",
            function.arg_count,
            cli.inputs.len()
        )));
    }
    info!(inputs = ?cli.inputs, "Inputs validated");

    // 7. Prove and verify.
    let elf = sp1_sdk::Elf::from(elf_bytes);
    let mut stdin = SP1Stdin::new();
    for val in &cli.inputs {
        stdin.write(val);
    }

    info!("Proving");
    let proof = if cli.mock {
        Prover::mock()
            .await
            .prove(elf, stdin, function.ret_count)
            .await?
    } else {
        Prover::cpu()
            .await
            .prove(elf, stdin, function.ret_count)
            .await?
    };
    info!(cycles = proof.cycles, "Execution complete");
    if let Some(value) = proof.return_value {
        info!(value, "Return value");
    }

    proof.verify().await?;
    info!("Proof verified");
    Ok(())
}
