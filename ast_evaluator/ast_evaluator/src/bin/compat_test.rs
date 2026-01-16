use std::path::PathBuf;

use ast_evaluator::{run_project, RunOptions};
use compat_harness::run_harness;

fn runner(project: PathBuf) -> Result<(), String> {
    let options = RunOptions {
        check_return_value: true,
    };

    run_project(project, &options)
        .map(|_| ())
        .map_err(|e| e.to_string())
}

fn main() {
    match run_harness(runner) {
        Ok(()) => {
            println!("\nAll compatibility tests passed!");
            std::process::exit(0);
        }
        Err(failures) => {
            eprintln!("\n{} compatibility test(s) failed", failures.len());
            std::process::exit(1);
        }
    }
}
