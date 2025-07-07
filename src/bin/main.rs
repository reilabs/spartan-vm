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

use std::{fs, panic, path::PathBuf, process::ExitCode};
use graphviz_rust::{dot_generator::*, dot_structures::*, printer::PrinterContext};

use clap::{Parser, arg};
use spartan_vm::compiler::ssa::{SSA, Terminator, Type, ValueId, FunctionId, BlockId};
use spartan_vm::compiler::taint_analysis::{TaintAnalysis, Taint, TypeVariable};
use spartan_vm::compiler::constraint_solver::ConstraintSolver;
use spartan_vm::{Error, Project, noir_error, noir_error::file};

/// The default Noir project path for the CLI to extract from.
const DEFAULT_NOIR_PROJECT_PATH: &str = "./";

/// A utility to extract Noir code to Lean in order to enable the formal
/// verification of Noir programs.
#[derive(Clone, Debug, Parser)]
pub struct ProgramOptions {
    /// The root of the Noir project to extract.
    #[arg(long, value_name = "PATH", default_value = DEFAULT_NOIR_PROJECT_PATH, value_parser = parse_path)]
    pub root: PathBuf,

    /// Testing mode?
    #[arg(long)]
    pub test_mode: bool,
}

/// The main function for the CLI utility, responsible for parsing program
/// options and handing them off to the actual execution of the tool.
fn main() -> ExitCode {
    // Parse args and hand-off immediately.
    let args = ProgramOptions::parse();
    if args.test_mode {
        run_test_mode(&args).unwrap_or_else(|err| {
            eprintln!("Error Encountered: {err}");
            ExitCode::FAILURE
        })
    } else {
        run(&args).unwrap_or_else(|err| {
            eprintln!("Error Encountered: {err:?}");
            ExitCode::FAILURE
        })
    }
}

/// A particular testing mode for the main function used to run through Noir
/// frontend tests
///
/// # Errors
///
/// - [`Error`] If the source directory is not readable
pub fn run_test_mode(args: &ProgramOptions) -> Result<ExitCode, Error> {
    let list = fs::read_dir(&args.root).map_err(|_| {
        file::Error::Other(format!(
            "Unable to read directory {:?}",
            args.root.as_os_str()
        ))
    })?;

    for entry in list {
        let entry =
            entry.map_err(|err| file::Error::Other(format!("Unable to read entry: {err:?}")))?;
        if !entry
            .metadata()
            .map_err(|_| {
                file::Error::Other(format!(
                    "Unable to read metadata of {:?}",
                    entry.file_name()
                ))
            })?
            .is_dir()
        {
            continue;
        }

        let result = panic::catch_unwind(|| Project::new(entry.path())?.extract());

        match result {
            Err(panic) => {
                println!(
                    "🔴 Panic                 {}\t{}",
                    entry.path().to_str().unwrap_or(""),
                    panic
                        .downcast::<String>()
                        .unwrap_or(Box::new("<no info>".to_string()))
                );
            }
            Ok(Err(Error::EmitError(noir_error::emit::Error::UnsupportedFeature(feature)))) => {
                println!(
                    "🟡 Unsupported           {}\t{}",
                    entry.path().to_str().unwrap_or(""),
                    feature
                );
            }
            Ok(Err(Error::EmitError(err))) => {
                println!(
                    "🔴 Emit Error            {}\t{:?}",
                    entry.path().to_str().unwrap_or(""),
                    err
                );
            }
            Ok(Err(Error::CompilationError(_))) => {
                println!(
                    "🟡 Compile Error         {}",
                    entry.path().to_str().unwrap_or("")
                );
            }
            Ok(Err(Error::FileError(err))) => {
                println!(
                    "🟡 IO Error              {}\t{:?}",
                    entry.path().to_str().unwrap_or(""),
                    err
                );
            }
            Ok(Err(Error::NoirProjectError(err))) => {
                println!(
                    "🟡 Noir project error    {}\t{:?}",
                    entry.path().to_str().unwrap_or(""),
                    err
                );
            }
            Ok(Err(err)) => {
                println!("🟡 Error                 {err:?}");
            }
            Ok(Ok(_)) => {
                println!(
                    "🟢 Pass                  {}",
                    entry.path().to_str().unwrap_or("")
                );
            }
        }
    }
    Ok(ExitCode::SUCCESS)
}

/// The main execution of the CLI utility. Should be called directly from the
/// `main` function of the application.
///
/// # Errors
///
/// - [`Error`] if the extraction process fails for any reason.
pub fn run(args: &ProgramOptions) -> Result<ExitCode, Error> {
    let project = Project::new(args.root.clone())?;

    let result = project.extract()?;

    // let ex = merkle_program().to_string(|_, _, _| "".to_string());
    // println!("Example program:\n{ex}");

    // let mut taint = TaintAnalysis::new();
    // let ssa = merkle_program();
    // taint.run(&ssa).unwrap();

    // println!(
    //     "Example program taint analysis:\n{}",
    //     ssa.to_string(|a, b, c| taint.annotate_value(a, b, c))
    // );

    // // println!("Judgements:\n{}", taint.judgements_string());

    // // Initialize and run constraint solver
    // println!("\n=== Constraint Solver ===");
    // let mut solver = ConstraintSolver::new(&taint);

    // println!("Judgements:\n{}", solver.judgements_string());
    // println!("Number of judgements: {}", solver.num_judgements());

    // solver.solve();

    // // Generate and display the inequality graph
    // println!("\n=== Inequality Graph (Graphviz DOT) ===");
    // let graph_dot = solver.generate_inequality_graph();

    // // Generate the image file
    // println!("\n=== Generating Image ===");
    // match generate_graph_image(&graph_dot, "inequality_graph.png") {
    //     Ok(_) => println!("✅ Image generated successfully: inequality_graph.png"),
    //     Err(e) => eprintln!("❌ Failed to generate image: {}", e),
    // }

    Ok(ExitCode::SUCCESS)
}

fn example_program() -> SSA {
    let mut ssa = SSA::new();
    let main = ssa.get_main_mut();
    let block_id = main.get_entry_id();

    let v0 = main.add_parameter(block_id, Type::field());
    let _v1 = main.add_parameter(block_id, Type::field().array_of(32));
    let v2 = main.add_parameter(block_id, Type::field());
    let _v3 = main.add_parameter(block_id, Type::bool().array_of(32));

    let v4 = main.push_eq(block_id, v0, v2);
    let const_0 = main.push_field_const(block_id, ark_bn254::Fr::from(0));
    main.push_assert_eq(block_id, v4, const_0);

    ssa.typecheck();
    ssa
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
fn generate_graph_image(dot_content: &str, output_path: &str) -> Result<(), Box<dyn std::error::Error>> {
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
