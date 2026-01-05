//! Spartan VM Interpreter
//!
//! This crate contains the core VM execution engine for Spartan, including:
//! - Bytecode definitions and dispatch mechanisms
//! - VM interpreter implementation
//! - Array handling for dynamic data
//! - Memory layout types for witness and constraint data

use std::fs;
use std::io::{self, Read, Write};
use std::path::Path;

pub mod array;
pub mod bytecode;
pub mod interpreter;
pub mod layouts;

// Re-export commonly used types
pub use layouts::{ConstraintsLayout, WitnessLayout};

// Re-export Field type for convenience
pub use ark_bn254::Fr as Field;

/// Save bytecode to a binary file (array of u64 in little-endian)
pub fn save_bytecode(bytecode: &[u64], path: impl AsRef<Path>) -> io::Result<()> {
    let bytes: Vec<u8> = bytecode
        .iter()
        .flat_map(|&v| v.to_le_bytes())
        .collect();
    fs::write(path, bytes)
}

/// Load bytecode from a binary file
pub fn load_bytecode(path: impl AsRef<Path>) -> io::Result<Vec<u64>> {
    let bytes = fs::read(path)?;
    if bytes.len() % 8 != 0 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "Bytecode file size must be multiple of 8",
        ));
    }

    let mut bytecode = Vec::with_capacity(bytes.len() / 8);
    for chunk in bytes.chunks_exact(8) {
        let value = u64::from_le_bytes(chunk.try_into().unwrap());
        bytecode.push(value);
    }
    Ok(bytecode)
}

/// Save layouts to a JSON file
pub fn save_layouts(
    witness_layout: &WitnessLayout,
    constraints_layout: &ConstraintsLayout,
    path: impl AsRef<Path>,
) -> io::Result<()> {
    let layouts = serde_json::json!({
        "witness": witness_layout,
        "constraints": constraints_layout,
    });
    fs::write(path, serde_json::to_string_pretty(&layouts)?)
}

/// Load layouts from a JSON file
pub fn load_layouts(path: impl AsRef<Path>) -> io::Result<(WitnessLayout, ConstraintsLayout)> {
    let content = fs::read_to_string(path)?;
    let layouts: serde_json::Value = serde_json::from_str(&content)?;

    let witness_layout = serde_json::from_value(layouts["witness"].clone())
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
    let constraints_layout = serde_json::from_value(layouts["constraints"].clone())
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

    Ok((witness_layout, constraints_layout))
}
