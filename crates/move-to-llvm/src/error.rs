use thiserror::Error;

#[derive(Debug, Error)]
pub enum CompileError {
    #[error("unsupported bytecode: {0}")]
    UnsupportedBytecode(String),

    #[error("unsupported type: {0}")]
    UnsupportedType(String),

    #[error("function has no code unit")]
    NoCode,

    #[error("LLVM error: {0}")]
    Llvm(String),

    #[error("failed to initialize target: {0}")]
    TargetInit(String),

    #[error("failed to create target machine: {0}")]
    TargetMachine(String),

    #[error("codegen failed: {0}")]
    Codegen(String),

    #[error("failed to deserialize module: {0}")]
    Deserialize(String),
}
