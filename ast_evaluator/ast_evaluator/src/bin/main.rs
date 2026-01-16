//! Binary for running Noir programs through the AST interpreter.
//!
//! This binary compiles a Noir project to its monomorphized AST and then
//! executes it using the ast_evaluator interpreter.

use std::{path::PathBuf, process::ExitCode};

use clap::Parser;

use ast_evaluator::{run_project, EvalError, RunError, RunOptions};

/// CLI options for the AST evaluator.
#[derive(Clone, Debug, Parser)]
#[command(name = "ast-eval")]
#[command(about = "Execute Noir programs using the AST interpreter")]
pub struct Options {
    /// The root of the Noir project to execute.
    #[arg(long, value_name = "PATH", default_value = "./", value_parser = parse_path)]
    pub root: PathBuf,

    /// Print verbose output including the return value.
    #[arg(long, short, action = clap::ArgAction::SetTrue)]
    pub verbose: bool,

    /// Check that the return value matches the expected value in Prover.toml.
    #[arg(long, action = clap::ArgAction::SetTrue)]
    pub check_return: bool,
}

fn main() -> ExitCode {
    let args = Options::parse();

    if args.verbose {
        println!("Loading project from {:?}...", args.root);
    }

    let options = RunOptions {
        check_return_value: args.check_return,
    };

    match run_project(args.root, &options) {
        Ok(result) => {
            println!("Execution successful!");

            if args.verbose {
                println!("Return value: {:?}", result.return_value);
            }

            if let Some(expected) = result.expected_return {
                if args.verbose {
                    println!("Expected return value: {:?}", expected);
                }
                println!("Return value matches expected value.");
            }

            ExitCode::SUCCESS
        }
        Err(RunError::EvaluationFailed(EvalError::AssertionFailed(msg))) => {
            eprintln!("Assertion failed: {msg}");
            ExitCode::FAILURE
        }
        Err(err) => {
            eprintln!("Error: {err}");
            ExitCode::FAILURE
        }
    }
}

/// Parse a path, making it absolute if necessary.
fn parse_path(path: &str) -> Result<PathBuf, String> {
    use fm::NormalizePath;
    let mut path: PathBuf = path
        .parse()
        .map_err(|e| format!("Failed to parse path: {e}"))?;
    if !path.is_absolute() {
        path = std::env::current_dir()
            .map_err(|e| format!("Failed to get current directory: {e}"))?
            .join(path)
            .normalize();
    }
    Ok(path)
}
