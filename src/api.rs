use std::{fs, path::{Path, PathBuf}};

use crate::{
    Project,
    compiler::{Field, r1cs_gen::R1CS},
    driver::{Driver, Error as DriverError},
    vm::interpreter,
};

#[derive(Debug)]
pub enum ApiError {
    Project(crate::Error),

    Driver { inner: DriverError },

    Io(std::io::Error),

    UnsupportedInputExt(String),

    InputsParse(String),

    InputsEncode(String),
}

impl std::fmt::Display for ApiError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ApiError::Project(e) => write!(f, "{e}"),
            ApiError::Driver { inner } => write!(f, "driver error: {inner:?}"),
            ApiError::Io(e) => write!(f, "{e}"),
            ApiError::UnsupportedInputExt(ext) => write!(f, "unsupported input file extension: {ext}"),
            ApiError::InputsParse(e) => write!(f, "failed to parse inputs: {e}"),
            ApiError::InputsEncode(e) => write!(f, "failed to encode inputs: {e}"),
        }
    }
}

impl std::error::Error for ApiError {}

/// Build a `Driver` and compile the Noir project all the way to R1CS.
pub fn compile_to_r1cs(root: PathBuf, draw_graphs: bool) -> Result<(Driver, R1CS), ApiError> {
    let project = Project::new(root).map_err(ApiError::Project)?;
    let mut driver = Driver::new(project, draw_graphs);
    driver.run_noir_compiler().map_err(|e| ApiError::Driver { inner: e })?;
    driver.monomorphize().map_err(|e| ApiError::Driver { inner: e })?;
    driver.explictize_witness().map_err(|e| ApiError::Driver { inner: e })?;
    let r1cs = driver.generate_r1cs().map_err(|e| ApiError::Driver { inner: e })?;
    Ok((driver, r1cs))
}

/// Read and encode `Prover.toml` inputs using the driver's ABI.
pub fn read_prover_inputs(root: &Path, abi: &noirc_abi::Abi) -> Result<Vec<Field>, ApiError> {
    use noirc_abi::input_parser::Format;

    let file_path = root.join("Prover.toml");
    let ext = file_path.extension().and_then(|e| e.to_str()).unwrap_or_default();

    let Some(format) = Format::from_ext(ext) else {
        return Err(ApiError::UnsupportedInputExt(ext.to_string()));
    };

    let inputs_src = fs::read_to_string(&file_path).map_err(ApiError::Io)?;
    let parsed = format.parse(&inputs_src, abi).map_err(|e| ApiError::InputsParse(e.to_string()))?;
    let params: Vec<Field> = abi.encode(&parsed, None)
        .map_err(|e| ApiError::InputsEncode(e.to_string()))?
        .into_iter()
        .map(|(_, v)| v.into_repr())
        .collect();

    Ok(params)
}

/// Execute witness generation given a compiled witgen binary.
pub fn run_witgen_from_binary(
    binary: &mut [u64],
    r1cs: &R1CS,
    params: &[Field],
) -> interpreter::WitgenResult {
    interpreter::run(binary, r1cs.witness_layout, r1cs.constraints_layout, params)
}

/// Compile the witgen VM from the current driver state.
pub fn compile_witgen(driver: &Driver) -> Result<Vec<u64>, ApiError> {
    Ok(driver.compile_witgen().map_err(|e| ApiError::Driver { inner: e })?)
}

/// Compile the AD VM from the current driver state.
pub fn compile_ad(driver: &Driver) -> Result<Vec<u64>, ApiError> {
    Ok(driver.compile_ad().map_err(|e| ApiError::Driver { inner: e })?)
}

/// Execute the AD run given a compiled AD binary and coeffs.
pub fn run_ad_from_binary(
    binary: &mut [u64],
    r1cs: &R1CS,
    coeffs: &[Field],
) -> (Vec<Field>, Vec<Field>, Vec<Field>, crate::vm::bytecode::AllocationInstrumenter) {
    interpreter::run_ad(binary, coeffs, r1cs.witness_layout, r1cs.constraints_layout)
}

/// Convenience: generate random AD coeffs sized to constraints.
pub fn random_ad_coeffs(r1cs: &R1CS) -> Vec<Field> {
    use ark_ff::UniformRand as _;
    let mut rng = rand::thread_rng();
    (0..r1cs.constraints.len())
        .map(|_| ark_bn254::Fr::rand(&mut rng))
        .collect()
}

/// Convenience: check witgen output against R1CS.
pub fn check_witgen(r1cs: &R1CS, res: &interpreter::WitgenResult) -> bool {
    r1cs.check_witgen_output(
        &res.out_wit_pre_comm,
        &res.out_wit_post_comm,
        &res.out_a,
        &res.out_b,
        &res.out_c,
    )
}

/// Convenience: check AD output against R1CS and coeffs.
pub fn check_ad(r1cs: &R1CS, coeffs: &[Field], a: &[Field], b: &[Field], c: &[Field]) -> bool {
    r1cs.check_ad_output(coeffs, a, b, c)
}

/// Where all debug files are written.
pub fn debug_output_dir(driver: &Driver) -> PathBuf {
    driver.get_debug_output_dir()
}


