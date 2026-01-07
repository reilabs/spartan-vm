//! Native Runner for Spartan VM
//!
//! Runs LLVM-compiled native code with inputs from Prover.toml.

mod field;
mod prover;
mod runner;

use std::path::PathBuf;

use anyhow::Result;
use clap::Parser;

#[derive(Parser, Debug)]
#[command(name = "native-runner")]
#[command(about = "Run Spartan VM native compiled programs")]
struct Args {
    /// Path to the compiled object file (.o)
    #[arg(value_name = "OBJECT_FILE")]
    object_file: PathBuf,

    /// Path to Prover.toml (default: look in same directory as object file)
    #[arg(short = 'i', long = "input")]
    prover_toml: Option<PathBuf>,

    /// Path to output JSON file
    #[arg(short = 'o', long = "output")]
    output_file: Option<PathBuf>,

    /// Path to the runtime library (libspartan_wasm_runtime.so)
    #[arg(short = 'r', long = "runtime")]
    runtime_path: Option<PathBuf>,

    /// Number of witnesses to allocate (default: auto-detect from metadata or 1000000)
    #[arg(long)]
    witness_count: Option<usize>,

    /// Number of constraints to allocate (default: auto-detect from metadata or 1000001)
    #[arg(long)]
    constraint_count: Option<usize>,

    /// Print verbose output
    #[arg(short, long)]
    verbose: bool,
}

fn main() -> Result<()> {
    let args = Args::parse();

    // Determine Prover.toml path
    let prover_path = args.prover_toml.unwrap_or_else(|| {
        // Look for Prover.toml in the same directory as the object file
        let mut path = args.object_file.parent().unwrap_or(&PathBuf::from(".")).to_path_buf();
        path.push("Prover.toml");
        path
    });

    if args.verbose {
        eprintln!("Object file: {}", args.object_file.display());
        eprintln!("Prover.toml: {}", prover_path.display());
    }

    // Parse Prover.toml
    let inputs = prover::parse_prover_toml(&prover_path)?;

    if args.verbose {
        eprintln!("Loaded {} inputs from Prover.toml", inputs.len());
        for (name, value) in &inputs {
            eprintln!("  {} = {}", name, value);
        }
    }

    // Convert inputs to Montgomery form field elements
    let field_inputs: Vec<field::FieldElement> = inputs
        .values()
        .map(|v| field::to_montgomery(v))
        .collect();

    if args.verbose {
        eprintln!("Converted to {} field elements", field_inputs.len());
    }

    // Determine buffer sizes
    let witness_count = args.witness_count.unwrap_or(1_000_003);
    let constraint_count = args.constraint_count.unwrap_or(1_000_001);

    if args.verbose {
        eprintln!("Allocating {} witnesses, {} constraints", witness_count, constraint_count);
    }

    // Find runtime library
    let runtime_path = args.runtime_path.unwrap_or_else(|| {
        // Try common locations
        let candidates = [
            PathBuf::from("../target/release/libspartan_wasm_runtime.so"),
            PathBuf::from("./libspartan_wasm_runtime.so"),
            PathBuf::from("/usr/local/lib/libspartan_wasm_runtime.so"),
        ];
        for path in &candidates {
            if path.exists() {
                return path.clone();
            }
        }
        // Default - will fail if not found
        PathBuf::from("libspartan_wasm_runtime.so")
    });

    if args.verbose {
        eprintln!("Runtime library: {}", runtime_path.display());
    }

    // Run the program
    let result = runner::run(
        &args.object_file,
        &runtime_path,
        &field_inputs,
        witness_count,
        constraint_count,
        args.verbose,
    )?;

    eprintln!("Execution complete!");
    eprintln!("  Witnesses: {}", result.witness_count);
    eprintln!("  Constraints: {}", result.constraint_count);

    // Output results
    if let Some(output_path) = args.output_file {
        let json = result.to_json();
        std::fs::write(&output_path, json)?;
        eprintln!("Output written to: {}", output_path.display());
    }

    Ok(())
}
