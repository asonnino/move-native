use std::fs;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.iter().any(|a| a == "--help" || a == "-h") || args.len() < 2 {
        eprintln!("move-to-llvm - Compile Move bytecode to Arm64 assembly");
        eprintln!();
        eprintln!("Usage: move-to-llvm <module.mv> > output.s");
        eprintln!();
        eprintln!("Options:");
        eprintln!("  --help, -h  Show this help message");
        std::process::exit(if args.len() < 2 { 1 } else { 0 });
    }

    let path = &args[1];
    let bytecode = match fs::read(path) {
        Ok(data) => data,
        Err(e) => {
            eprintln!("Error reading {path}: {e}");
            std::process::exit(1);
        }
    };

    match move_to_llvm::compile(&bytecode) {
        Ok(asm) => print!("{asm}"),
        Err(e) => {
            eprintln!("Compilation error: {e}");
            std::process::exit(1);
        }
    }
}
