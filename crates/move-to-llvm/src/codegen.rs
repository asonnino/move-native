use inkwell::module::Module;
use inkwell::passes::PassBuilderOptions;
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple,
};
use inkwell::OptimizationLevel;

use crate::error::CompileError;

const CPU: &str = "generic";
/// Reserve x23 so LLVM never allocates the gas register.
const FEATURES: &str = "+reserve-x23";

/// Return the LLVM target triple for the host platform.
fn host_triple() -> &'static str {
    if cfg!(target_os = "macos") {
        "aarch64-apple-darwin"
    } else {
        "aarch64-unknown-linux-gnu"
    }
}

/// Run optimization passes on the module using the new pass manager.
///
/// Runs mem2reg (promote allocas to SSA registers), instcombine, and
/// simplifycfg — enough to clean up the alloca-heavy IR we generate.
pub fn run_optimization_passes(module: &Module<'_>) -> Result<(), CompileError> {
    let machine = create_target_machine()?;
    let opts = PassBuilderOptions::create();
    module
        .run_passes("mem2reg,instcombine,simplifycfg", &machine, opts)
        .map_err(|e| CompileError::Llvm(e.to_string()))
}

/// Create an LLVM `TargetMachine` for AArch64 with `+reserve-x23`.
pub fn create_target_machine() -> Result<TargetMachine, CompileError> {
    Target::initialize_aarch64(&InitializationConfig::default());

    let triple = TargetTriple::create(host_triple());
    let target =
        Target::from_triple(&triple).map_err(|e| CompileError::TargetInit(e.to_string()))?;

    target
        .create_target_machine(
            &triple,
            CPU,
            FEATURES,
            OptimizationLevel::Default,
            RelocMode::PIC,
            CodeModel::Default,
        )
        .ok_or_else(|| CompileError::TargetMachine("failed to create target machine".into()))
}

/// Emit the module as AArch64 assembly text.
pub fn emit_assembly(module: &Module<'_>) -> Result<String, CompileError> {
    let machine = create_target_machine()?;

    let buf = machine
        .write_to_memory_buffer(module, FileType::Assembly)
        .map_err(|e| CompileError::Codegen(e.to_string()))?;

    let asm = std::str::from_utf8(buf.as_slice())
        .map_err(|e| CompileError::Codegen(e.to_string()))?
        .to_string();

    Ok(asm)
}

/// Post-process LLVM assembly to add platform-compatible symbol aliases.
///
/// On macOS (where LLVM emits `_name` symbols), adds unprefixed aliases
/// so that instrumenter and the runtime can find functions by their
/// Move names. On Linux, adds underscore-prefixed aliases for the same
/// cross-platform compatibility.
pub fn add_symbol_aliases(asm: &str) -> String {
    let mut output = String::with_capacity(asm.len());
    let mut global_names: Vec<&str> = Vec::new();

    for line in asm.lines() {
        let trimmed = line.trim();
        if let Some(name) = trimmed
            .strip_prefix(".globl\t")
            .or_else(|| trimmed.strip_prefix(".globl "))
        {
            let name = name.trim();
            global_names.push(name);
        }
    }

    output.push_str(asm);

    if !global_names.is_empty() {
        output.push('\n');
        for name in &global_names {
            if let Some(bare) = name.strip_prefix('_') {
                // macOS: _add exists, add alias for bare name
                output.push_str(&format!(".globl {bare}\n"));
                output.push_str(&format!("{bare}:\n"));
                output.push_str(&format!("\tb {name}\n"));
            } else {
                // Linux: add exists, add alias for _name
                output.push_str(&format!(".globl _{name}\n"));
                output.push_str(&format!("_{name}:\n"));
                output.push_str(&format!("\tb {name}\n"));
            }
        }
    }

    output
}
