// Copyright (c) Mysten Labs, Inc.
// SPDX-License-Identifier: Apache-2.0

//! Full compilation pipeline: Move bytecode -> verified native module

use crate::assembler;
use crate::error::PipelineError;

/// Compile Move bytecode through the full pipeline:
/// compile -> instrument -> assemble -> verify.
///
/// Returns a [`runtime::CompiledModule`] ready for execution.
pub fn prepare(bytecode: &[u8]) -> Result<runtime::CompiledModule, PipelineError> {
    // 1. Compile Move bytecode to assembly
    let asm = compiler::compile(&compiler::Target::host(), bytecode)?;

    prepare_from_assembly(&asm)
}

/// Compile a pre-deserialized Move module (with optional dependencies)
/// through the full pipeline.
pub fn prepare_module(
    module: &move_binary_format::CompiledModule,
    deps: &[move_binary_format::CompiledModule],
) -> Result<runtime::CompiledModule, PipelineError> {
    let asm = compiler::compile_module_with_deps(&compiler::Target::host(), module, deps)?;

    prepare_from_assembly(&asm)
}

/// Shared pipeline from assembly text onward: instrument -> assemble -> verify.
///
/// TODO: Multi-function modules currently fail verification because:
///   1. The instrumenter only instruments the first function's back-edges
///   2. The verifier assumes a single entry point at offset 0
fn prepare_from_assembly(asm: &str) -> Result<runtime::CompiledModule, PipelineError> {
    // 2. Instrument with gas checks
    let parsed = instrumenter::ParsedAssembly::parse(asm);
    let cfg_result = instrumenter::build_cfg(&parsed)?;
    let instrumented = instrumenter::instrument(parsed.lines(), &cfg_result)?;

    // 3. Assemble to machine code
    let assembled = assembler::assemble(&instrumented)?;

    // 4. Verify the binary
    let instructions = verifier::decode_instructions(&assembled.code)?;
    let result = verifier::Verifier::new(&instructions).verify();
    if !result.is_ok() {
        return Err(PipelineError::Verification(result.errors().to_vec()));
    }

    // 5. Build runtime module
    Ok(runtime::CompiledModule::new(
        assembled.code,
        assembled.entry_points,
    ))
}
