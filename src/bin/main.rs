//! A utility for extracting [Noir](https://noir-lang.org) programs to
//! equivalent definitions in the [Lean](https://lean-lang.org) theorem prover
//! and programming language.
//!
//! # Limitations
//!
//! It currently only supports single-file programs, pending further expansion
//! to support full Noir projects. The stdlib functions properly at this stage.

#![warn(clippy::all, clippy::cargo, clippy::pedantic)]
// These occur in our Noir dependencies and cannot be avoided.
#![allow(clippy::multiple_crate_versions)]

use std::{fs, path::PathBuf, process::ExitCode, str::FromStr};

use clap::Parser;
use spartan_vm::{Error, Project};

/// The default Noir project path for the CLI to extract from.
const DEFAULT_NOIR_PROJECT_PATH: &str = "./";

#[derive(Clone, Debug, Parser)]
pub struct ProgramOptions {
    /// The root of the Noir project to extract.
    #[arg(long, value_name = "PATH", default_value = DEFAULT_NOIR_PROJECT_PATH, value_parser = parse_path)]
    pub root: PathBuf,

    #[arg(long, value_name = "PUBLIC WITNESS", default_value = "", num_args = 0..)]
    pub public_witness: Vec<String>,
}

/// The main function for the CLI utility, responsible for parsing program
/// options and handing them off to the actual execution of the tool.
fn main() -> ExitCode {
    // Parse args and hand-off immediately.
    let args = ProgramOptions::parse();

    tracing_forest::init();

    run(&args).unwrap_or_else(|err| {
        eprintln!("Error Encountered: {err:?}");
        ExitCode::FAILURE
    })
}

/// The main execution of the CLI utility. Should be called directly from the
/// `main` function of the application.
///
/// # Errors
///
/// - [`Error`] if the extraction process fails for any reason.
pub fn run(args: &ProgramOptions) -> Result<ExitCode, Error> {
    let project = Project::new(args.root.clone())?;

    let public_witness: Vec<_> = args.public_witness.iter().map(|s| ark_bn254::Fr::from_str(s).unwrap()).collect();
    println!("Public witness: {:?}", public_witness);

    let result = project.extract(public_witness)?;
    Ok(ExitCode::SUCCESS)
}

// Copied from: https://github.com/noir-lang/noir/blob/5071093f9b51e111a49a5f78d827774ef8e80c74/tooling/nargo_cli/src/cli/mod.rs#L301
/// Parses a path and turns it into an absolute one by joining to the current
/// directory.
fn parse_path(path: &str) -> Result<PathBuf, String> {
    use fm::NormalizePath;
    let mut path: PathBuf = path
        .parse()
        .map_err(|e| format!("failed to parse path: {e}"))?;
    if !path.is_absolute() {
        path = std::env::current_dir().unwrap().join(path).normalize();
    }
    Ok(path)
}

/// Generate a PNG image from a DOT graph string
fn generate_graph_image(
    dot_content: &str,
    output_path: &str,
) -> Result<(), Box<dyn std::error::Error>> {
    use std::process::Command;

    // Write DOT content to a temporary file
    let temp_dot_path = "temp_graph.dot";
    fs::write(temp_dot_path, dot_content)?;

    // Use system dot command to generate PNG
    let output = Command::new("dot")
        .args(&["-Tpng", temp_dot_path, "-o", output_path])
        .output()?;

    // Clean up temporary file
    let _ = fs::remove_file(temp_dot_path);

    if output.status.success() {
        Ok(())
    } else {
        let error_msg = String::from_utf8_lossy(&output.stderr);
        Err(format!("Graphviz dot command failed: {}", error_msg).into())
    }
}
