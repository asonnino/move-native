// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! CLI for generating and verifying ZK proofs of Move contract execution.

use std::fs;

use clap::Parser;
use move_binary_format::CompiledModule;
use tracing::{error, info};

use compiler::ModuleInfo;
use zero_knowledge::error::{ZkError, ZkResult};
use zero_knowledge::pipeline::CompiledElf;

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

    // 2. Resolve the target function name.
    let info = ModuleInfo::from_module(&module)?;
    let function_name = match &cli.function {
        Some(name) => {
            info.function(name)
                .ok_or_else(|| ZkError::Function(format!("function '{name}' not found")))?;
            name.clone()
        }
        None => {
            let func = info.only_function().ok_or_else(|| {
                let names: Vec<_> = info
                    .functions
                    .iter()
                    .filter(|f| !f.is_native)
                    .map(|f| f.name.as_str())
                    .collect();
                ZkError::Function(format!(
                    "multiple functions in module, use --function: {names:?}"
                ))
            })?;
            func.name.clone()
        }
    };

    // 3. Compile Move → RISC-V → ELF.
    info!("Compiling to RISC-V");
    let compiled = CompiledElf::compile(&module, &function_name, &[])?;
    info!(bytes = compiled.elf_bytes.len(), "ELF ready");

    // 5. Prove and verify.
    info!("Proving");
    let proof = compiled.prove(&cli.inputs, cli.mock).await?;
    info!(cycles = proof.cycles, "Execution complete");
    if let Some(value) = proof.return_value {
        info!(value, "Return value");
    }

    proof.verify().await?;
    info!("Proof verified");
    Ok(())
}
