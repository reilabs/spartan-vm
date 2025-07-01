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

use clap::{Parser, arg};
use spartan_vm::compiler::ssa::{SSA, Terminator, Type};
use spartan_vm::compiler::taint_analysis::TaintAnalysis;
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

    let ex = merkle_program().to_string(|_, _, _| "".to_string());
    println!("Example program:\n{ex}");

    let mut taint = TaintAnalysis::new();
    let ssa = merkle_program();
    taint.run(&ssa).unwrap();

    println!(
        "Example program taint analysis:\n{}",
        ssa.to_string(|a, b, c| taint.annotate_value(a, b, c))
    );

    Ok(ExitCode::SUCCESS)
}

fn example_program() -> SSA {
    let mut ssa = SSA::new();
    let main = ssa.get_main_mut();
    let block = main.get_entry_mut();

    let v0 = block.add_parameter(Type::field());
    let v1 = block.add_parameter(Type::field().array_of(32));
    let v2 = block.add_parameter(Type::field());
    let v3 = block.add_parameter(Type::bool().array_of(32));

    let v4 = block.push_eq(v0, v2);
    let const_0 = block.push_field_const(ark_bn254::Fr::from(0));
    block.push_assert_eq(v4, const_0);

    ssa.typecheck();
    ssa
}

fn merkle_program() -> SSA {
    let mut ssa = SSA::new();
    // let main = ssa.get_main_mut();
    let mtree_recover = ssa.add_function();
    let hash = ssa.add_function();

    let main = ssa.get_main_mut();

    {
        let b0 = main.get_entry_mut();
        let v0 = b0.add_parameter(Type::field());
        let v1 = b0.add_parameter(Type::field().array_of(32));
        let v2 = b0.add_parameter(Type::field());
        let v3 = b0.add_parameter(Type::bool().array_of(32));
        let v5 = b0.push_call(mtree_recover, vec![v3, v1, v2], 1)[0];
        println!("v0: {v0:?}, v1: {v1:?}, v2: {v2:?}, v3: {v3:?}, v5: {v5:?}");
        b0.push_assert_eq(v0, v5);
        b0.set_terminator(Terminator::Return(vec![]));
    }

    let mtree_recover_fn = ssa.get_function_mut(mtree_recover);
    mtree_recover_fn.add_return_type(Type::field());
    let b1id = mtree_recover_fn.add_block();
    let b2id = mtree_recover_fn.add_block();
    let b3id = mtree_recover_fn.add_block();
    let b4id = mtree_recover_fn.add_block();
    let b5id = mtree_recover_fn.add_block();
    let b6id = mtree_recover_fn.add_block();

    {
        let b0 = mtree_recover_fn.get_entry_mut();

        let v0 = b0.add_parameter(Type::bool().array_of(32));
        let v1 = b0.add_parameter(Type::field().array_of(32));
        let v2 = b0.add_parameter(Type::field());

        let v4 = b0.push_alloc(Type::field());
        let vconst0 = b0.push_u32_const(0);
        b0.push_store(v4, v2);
        b0.set_terminator(Terminator::Jmp(b1id, vec![vconst0, v0, v1, v4]));
    }

    {
        let b1 = mtree_recover_fn.get_block_mut(b1id);

        let v3 = b1.add_parameter(Type::u32());
        let v0 = b1.add_parameter(Type::bool().array_of(32));
        let v1 = b1.add_parameter(Type::field().array_of(32));
        let v4 = b1.add_parameter(Type::field().ref_of());

        let vconst32 = b1.push_u32_const(32);
        let v7 = b1.push_lt(v3, vconst32);
        b1.set_terminator(Terminator::JmpIf(
            v7,
            b2id,
            vec![v3, v0, v1, v4],
            b3id,
            vec![v4],
        ));
    }

    {
        let b2 = mtree_recover_fn.get_block_mut(b2id);

        let v3 = b2.add_parameter(Type::u32());
        let v0 = b2.add_parameter(Type::bool().array_of(32));
        let v1 = b2.add_parameter(Type::field().array_of(32));
        let v4 = b2.add_parameter(Type::field().ref_of());

        let vconst32 = b2.push_u32_const(32);
        let vconst_true = b2.push_bool_const(true);
        let v9 = b2.push_lt(v3, vconst32);
        b2.push_assert_eq(v9, vconst_true);
        let v11 = b2.push_array_get(v0, v3);
        let v12 = b2.push_lt(v3, vconst32);
        b2.push_assert_eq(v12, vconst_true);
        let v13 = b2.push_array_get(v1, v3);
        b2.set_terminator(Terminator::JmpIf(
            v11,
            b4id,
            vec![v4, v13, v3, v0, v1],
            b5id,
            vec![v4, v13, v3, v0, v1],
        ));
    }

    {
        let b3 = mtree_recover_fn.get_block_mut(b3id);

        let v4 = b3.add_parameter(Type::field().ref_of());

        let v8 = b3.push_load(v4);
        b3.set_terminator(Terminator::Return(vec![v8]));
    }

    {
        let b4 = mtree_recover_fn.get_block_mut(b4id);

        let v4 = b4.add_parameter(Type::field().ref_of());
        let v13 = b4.add_parameter(Type::field());
        let v3 = b4.add_parameter(Type::u32());
        let v0 = b4.add_parameter(Type::bool().array_of(32));
        let v1 = b4.add_parameter(Type::field().array_of(32));

        let v17 = b4.push_load(v4);
        let v18 = b4.push_call(hash, vec![v13, v17], 1)[0];
        b4.push_store(v4, v18);
        b4.set_terminator(Terminator::Jmp(b6id, vec![v3, v0, v1, v4]));
    }

    {
        let b5 = mtree_recover_fn.get_block_mut(b5id);

        let v4 = b5.add_parameter(Type::field().ref_of());
        let v13 = b5.add_parameter(Type::field());
        let v3 = b5.add_parameter(Type::u32());
        let v0 = b5.add_parameter(Type::bool().array_of(32));
        let v1 = b5.add_parameter(Type::field().array_of(32));

        let v14 = b5.push_load(v4);
        let v16 = b5.push_call(hash, vec![v14, v13], 1)[0];
        b5.push_store(v4, v16);
        b5.set_terminator(Terminator::Jmp(b6id, vec![v3, v0, v1, v4]));
    }

    {
        let b6 = mtree_recover_fn.get_block_mut(b6id);

        let v3 = b6.add_parameter(Type::u32());
        let v0 = b6.add_parameter(Type::bool().array_of(32));
        let v1 = b6.add_parameter(Type::field().array_of(32));
        let v4 = b6.add_parameter(Type::field().ref_of());

        let const1 = b6.push_u32_const(1);
        let v20 = b6.push_add(v3, const1);
        b6.set_terminator(Terminator::Jmp(b1id, vec![v20, v0, v1, v4]));
    }

    let hash_fn = ssa.get_function_mut(hash);
    hash_fn.add_return_type(Type::field());
    {
        let b0 = hash_fn.get_entry_mut();
        let v0 = b0.add_parameter(Type::field());
        let v1 = b0.add_parameter(Type::field());
        let v2 = b0.push_add(v0, v1);
        b0.set_terminator(Terminator::Return(vec![v2]));
    }

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
