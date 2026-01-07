//! Native Code Runner
//!
//! Links object files, loads them, and executes spartan_main.

use std::path::Path;
use std::process::Command;
use std::time::Instant;

use anyhow::{bail, Context, Result};
use libloading::{Library, Symbol};
use tempfile::TempDir;

use crate::field::FieldElement;

/// VM struct matching the C ABI
#[repr(C)]
pub struct VM {
    pub witness_ptr: *mut FieldElement,
    pub constraints_a_ptr: *mut FieldElement,
    pub constraints_b_ptr: *mut FieldElement,
    pub constraints_c_ptr: *mut FieldElement,
}

/// Execution result
pub struct RunResult {
    pub witnesses: Vec<FieldElement>,
    pub constraints_a: Vec<FieldElement>,
    pub constraints_b: Vec<FieldElement>,
    pub constraints_c: Vec<FieldElement>,
    pub witness_count: usize,
    pub constraint_count: usize,
}

impl RunResult {
    /// Convert to JSON string
    pub fn to_json(&self) -> String {
        use crate::field::from_montgomery;

        let witnesses: Vec<String> = self.witnesses[..self.witness_count]
            .iter()
            .map(|fe| from_montgomery(fe))
            .collect();

        let constraints_a: Vec<String> = self.constraints_a[..self.constraint_count]
            .iter()
            .map(|fe| fe.to_hex())
            .collect();

        let constraints_b: Vec<String> = self.constraints_b[..self.constraint_count]
            .iter()
            .map(|fe| fe.to_hex())
            .collect();

        let constraints_c: Vec<String> = self.constraints_c[..self.constraint_count]
            .iter()
            .map(|fe| fe.to_hex())
            .collect();

        format!(
            r#"{{
  "witness_count": {},
  "constraint_count": {},
  "witnesses": {:?},
  "constraints": {{
    "a": {:?},
    "b": {:?},
    "c": {:?}
  }}
}}"#,
            self.witness_count,
            self.constraint_count,
            witnesses,
            constraints_a,
            constraints_b,
            constraints_c
        )
    }
}

/// Global state for write callbacks
static mut WITNESS_IDX: usize = 0;
static mut CONSTRAINT_IDX: usize = 0;
static mut WITNESSES: *mut FieldElement = std::ptr::null_mut();
static mut CONSTRAINTS_A: *mut FieldElement = std::ptr::null_mut();
static mut CONSTRAINTS_B: *mut FieldElement = std::ptr::null_mut();
static mut CONSTRAINTS_C: *mut FieldElement = std::ptr::null_mut();

/// Write witness callback
#[no_mangle]
pub unsafe extern "C" fn __write_witness(_vm: *mut VM, value: *const FieldElement) {
    if !WITNESSES.is_null() {
        *WITNESSES.add(WITNESS_IDX) = *value;
        WITNESS_IDX += 1;
    }
}

/// Write constraint A callback
#[no_mangle]
pub unsafe extern "C" fn __write_a(_vm: *mut VM, value: *const FieldElement) {
    if !CONSTRAINTS_A.is_null() {
        *CONSTRAINTS_A.add(CONSTRAINT_IDX) = *value;
    }
}

/// Write constraint B callback
#[no_mangle]
pub unsafe extern "C" fn __write_b(_vm: *mut VM, value: *const FieldElement) {
    if !CONSTRAINTS_B.is_null() {
        *CONSTRAINTS_B.add(CONSTRAINT_IDX) = *value;
    }
}

/// Write constraint C callback
#[no_mangle]
pub unsafe extern "C" fn __write_c(_vm: *mut VM, value: *const FieldElement) {
    if !CONSTRAINTS_C.is_null() {
        *CONSTRAINTS_C.add(CONSTRAINT_IDX) = *value;
        CONSTRAINT_IDX += 1;
    }
}

/// Link an object file into a shared library
fn link_shared_library(
    object_file: &Path,
    runtime_path: &Path,
    output_path: &Path,
) -> Result<()> {
    // Get the directory containing the runtime library
    let runtime_dir = runtime_path.parent().unwrap_or(Path::new("."));

    let mut args = Vec::new();

    // On macOS, use -dynamiclib instead of -shared
    #[cfg(target_os = "macos")]
    {
        args.push("-dynamiclib".to_string());
        // Set deployment target to avoid version mismatch warnings
        let deployment_target = std::env::var("MACOSX_DEPLOYMENT_TARGET")
            .unwrap_or_else(|_| "11.0".to_string());
        args.push(format!("-mmacosx-version-min={}", deployment_target));
        // Allow undefined symbols - they'll be resolved from the loading executable
        // (the __write_* callbacks are defined in native-runner, not the runtime)
        args.push("-undefined".to_string());
        args.push("dynamic_lookup".to_string());
    }

    #[cfg(not(target_os = "macos"))]
    {
        args.push("-shared".to_string());
    }

    args.push("-o".to_string());
    args.push(output_path.to_str().unwrap().to_string());
    args.push(object_file.to_str().unwrap().to_string());
    args.push(format!("-L{}", runtime_dir.display()));
    args.push("-lspartan_wasm_runtime".to_string());
    args.push("-lpthread".to_string());
    args.push("-lm".to_string());

    // -ldl is not needed on macOS
    #[cfg(not(target_os = "macos"))]
    args.push("-ldl".to_string());

    let status = Command::new("cc")
        .args(&args)
        .status()
        .context("Failed to run linker")?;

    if !status.success() {
        bail!("Linker failed with status: {}", status);
    }

    Ok(())
}

/// Run the compiled program
pub fn run(
    object_file: &Path,
    runtime_path: &Path,
    inputs: &[FieldElement],
    witness_count: usize,
    constraint_count: usize,
    verbose: bool,
) -> Result<RunResult> {
    let total_start = Instant::now();

    // Create temp directory for shared library
    let temp_dir = TempDir::new().context("Failed to create temp directory")?;
    let so_path = temp_dir.path().join("program.so");

    if verbose {
        eprintln!("Linking {} -> {}", object_file.display(), so_path.display());
    }

    // Link object file into shared library
    let link_start = Instant::now();
    link_shared_library(object_file, runtime_path, &so_path)?;
    let link_time = link_start.elapsed();

    // Allocate output buffers
    let mut witnesses = vec![FieldElement::zero(); witness_count];
    let mut constraints_a = vec![FieldElement::zero(); constraint_count];
    let mut constraints_b = vec![FieldElement::zero(); constraint_count];
    let mut constraints_c = vec![FieldElement::zero(); constraint_count];

    // Set up global state for callbacks
    unsafe {
        WITNESS_IDX = 0;
        CONSTRAINT_IDX = 0;
        WITNESSES = witnesses.as_mut_ptr();
        CONSTRAINTS_A = constraints_a.as_mut_ptr();
        CONSTRAINTS_B = constraints_b.as_mut_ptr();
        CONSTRAINTS_C = constraints_c.as_mut_ptr();
    }

    // Create VM struct
    let mut vm = VM {
        witness_ptr: witnesses.as_mut_ptr(),
        constraints_a_ptr: constraints_a.as_mut_ptr(),
        constraints_b_ptr: constraints_b.as_mut_ptr(),
        constraints_c_ptr: constraints_c.as_mut_ptr(),
    };

    // Load the shared library
    if verbose {
        eprintln!("Loading shared library...");
    }

    let load_start = Instant::now();

    // We need to set LD_LIBRARY_PATH for the runtime
    let runtime_dir = runtime_path.parent().unwrap_or(Path::new("."));
    std::env::set_var(
        "LD_LIBRARY_PATH",
        format!(
            "{}:{}",
            runtime_dir.display(),
            std::env::var("LD_LIBRARY_PATH").unwrap_or_default()
        ),
    );

    let library = unsafe {
        Library::new(&so_path).context("Failed to load shared library")?
    };
    let load_time = load_start.elapsed();

    // Get the spartan_main symbol
    // The signature is: void spartan_main(VM*, FieldElement*, FieldElement*, ...)
    // Number of FieldElement* parameters depends on the program

    if verbose {
        eprintln!("Calling spartan_main with {} inputs...", inputs.len());
    }

    let exec_start = Instant::now();
    unsafe {
        match inputs.len() {
            0 => {
                let func: Symbol<unsafe extern "C" fn(*mut VM)> =
                    library.get(b"spartan_main").context("spartan_main not found")?;
                func(&mut vm);
            }
            1 => {
                let func: Symbol<unsafe extern "C" fn(*mut VM, *const FieldElement)> =
                    library.get(b"spartan_main").context("spartan_main not found")?;
                func(&mut vm, &inputs[0]);
            }
            2 => {
                let func: Symbol<unsafe extern "C" fn(*mut VM, *const FieldElement, *const FieldElement)> =
                    library.get(b"spartan_main").context("spartan_main not found")?;
                func(&mut vm, &inputs[0], &inputs[1]);
            }
            3 => {
                let func: Symbol<unsafe extern "C" fn(*mut VM, *const FieldElement, *const FieldElement, *const FieldElement)> =
                    library.get(b"spartan_main").context("spartan_main not found")?;
                func(&mut vm, &inputs[0], &inputs[1], &inputs[2]);
            }
            4 => {
                let func: Symbol<unsafe extern "C" fn(*mut VM, *const FieldElement, *const FieldElement, *const FieldElement, *const FieldElement)> =
                    library.get(b"spartan_main").context("spartan_main not found")?;
                func(&mut vm, &inputs[0], &inputs[1], &inputs[2], &inputs[3]);
            }
            5 => {
                let func: Symbol<unsafe extern "C" fn(*mut VM, *const FieldElement, *const FieldElement, *const FieldElement, *const FieldElement, *const FieldElement)> =
                    library.get(b"spartan_main").context("spartan_main not found")?;
                func(&mut vm, &inputs[0], &inputs[1], &inputs[2], &inputs[3], &inputs[4]);
            }
            n => bail!("Unsupported number of inputs: {}. Maximum supported is 5.", n),
        }
    }
    let exec_time = exec_start.elapsed();
    let total_time = total_start.elapsed();

    // Read results
    let (final_witness_idx, final_constraint_idx) = unsafe {
        (WITNESS_IDX, CONSTRAINT_IDX)
    };

    // Print timing summary
    eprintln!("Timing:");
    eprintln!("  Link:      {:>8.3} ms", link_time.as_secs_f64() * 1000.0);
    eprintln!("  Load:      {:>8.3} ms", load_time.as_secs_f64() * 1000.0);
    eprintln!("  Execute:   {:>8.3} ms", exec_time.as_secs_f64() * 1000.0);
    eprintln!("  Total:     {:>8.3} ms", total_time.as_secs_f64() * 1000.0);

    if verbose {
        eprintln!("Execution complete: {} witnesses, {} constraints",
            final_witness_idx, final_constraint_idx);
    }

    // Clean up global state
    unsafe {
        WITNESSES = std::ptr::null_mut();
        CONSTRAINTS_A = std::ptr::null_mut();
        CONSTRAINTS_B = std::ptr::null_mut();
        CONSTRAINTS_C = std::ptr::null_mut();
    }

    Ok(RunResult {
        witnesses,
        constraints_a,
        constraints_b,
        constraints_c,
        witness_count: final_witness_idx,
        constraint_count: final_constraint_idx,
    })
}
