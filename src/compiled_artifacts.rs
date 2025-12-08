//! Compiled artifacts that can be serialized and deserialized for later execution.
//!
//! This module provides a `CompiledArtifacts` struct that captures the compilation
//! results from the Driver, allowing the compile and execute phases to be split
//! and the artifacts to be persisted to disk.

use std::{fs, io, path::Path};

use serde::{Deserialize, Serialize};

use crate::compiler::r1cs_gen::R1CS;

/// Compiled artifacts from the Driver that can be serialized/deserialized.
///
/// This struct captures all the outputs from the compilation phase that are
/// needed for the execution phase (witness generation and automatic differentiation).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CompiledArtifacts {
    /// The R1CS constraint system
    pub r1cs: R1CS,
    /// The compiled witness generation bytecode
    pub witgen_binary: Vec<u64>,
    /// The compiled automatic differentiation bytecode
    pub ad_binary: Vec<u64>,
}

/// Error type for artifact serialization/deserialization operations
#[derive(Debug)]
pub enum ArtifactError {
    /// IO error during file operations
    Io(io::Error),
    /// Serialization error
    Serialize(bincode::Error),
    /// Deserialization error
    Deserialize(bincode::Error),
}

impl std::fmt::Display for ArtifactError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ArtifactError::Io(e) => write!(f, "IO error: {}", e),
            ArtifactError::Serialize(e) => write!(f, "Serialization error: {}", e),
            ArtifactError::Deserialize(e) => write!(f, "Deserialization error: {}", e),
        }
    }
}

impl std::error::Error for ArtifactError {}

impl From<io::Error> for ArtifactError {
    fn from(e: io::Error) -> Self {
        ArtifactError::Io(e)
    }
}

impl CompiledArtifacts {
    /// Create new compiled artifacts from the compilation outputs.
    pub fn new(r1cs: R1CS, witgen_binary: Vec<u64>, ad_binary: Vec<u64>) -> Self {
        Self {
            r1cs,
            witgen_binary,
            ad_binary,
        }
    }

    /// Serialize the artifacts to a byte vector.
    pub fn to_bytes(&self) -> Result<Vec<u8>, ArtifactError> {
        bincode::serialize(self).map_err(ArtifactError::Serialize)
    }

    /// Deserialize artifacts from a byte slice.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, ArtifactError> {
        bincode::deserialize(bytes).map_err(ArtifactError::Deserialize)
    }

    /// Save the artifacts to a file.
    pub fn save_to_file<P: AsRef<Path>>(&self, path: P) -> Result<(), ArtifactError> {
        let bytes = self.to_bytes()?;
        fs::write(path, bytes)?;
        Ok(())
    }

    /// Load artifacts from a file.
    pub fn load_from_file<P: AsRef<Path>>(path: P) -> Result<Self, ArtifactError> {
        let bytes = fs::read(path)?;
        Self::from_bytes(&bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler::r1cs_gen::{ConstraintsLayout, R1C, WitnessLayout};

    fn create_test_artifacts() -> CompiledArtifacts {
        let witness_layout = WitnessLayout {
            algebraic_size: 10,
            multiplicities_size: 2,
            challenges_size: 1,
            tables_data_size: 3,
            lookups_data_size: 4,
        };

        let constraints_layout = ConstraintsLayout {
            algebraic_size: 5,
            tables_data_size: 2,
            lookups_data_size: 1,
        };

        // Create a simple R1C constraint: 1 * 1 = 1
        let r1c = R1C {
            a: vec![(0, ark_bn254::Fr::from(1u64))],
            b: vec![(0, ark_bn254::Fr::from(1u64))],
            c: vec![(0, ark_bn254::Fr::from(1u64))],
        };

        let r1cs = R1CS {
            witness_layout,
            constraints_layout,
            constraints: vec![r1c],
        };

        let witgen_binary = vec![1u64, 2, 3, 4, 5];
        let ad_binary = vec![6u64, 7, 8, 9, 10];

        CompiledArtifacts::new(r1cs, witgen_binary, ad_binary)
    }

    #[test]
    fn test_serialize_deserialize_bytes() {
        let original = create_test_artifacts();
        
        // Serialize to bytes
        let bytes = original.to_bytes().expect("Serialization should succeed");
        
        // Deserialize from bytes
        let restored = CompiledArtifacts::from_bytes(&bytes)
            .expect("Deserialization should succeed");
        
        // Verify the data matches
        assert_eq!(original.witgen_binary, restored.witgen_binary);
        assert_eq!(original.ad_binary, restored.ad_binary);
        assert_eq!(original.r1cs.constraints.len(), restored.r1cs.constraints.len());
        assert_eq!(
            original.r1cs.witness_layout.algebraic_size,
            restored.r1cs.witness_layout.algebraic_size
        );
    }

    #[test]
    fn test_serialize_deserialize_file() {
        let original = create_test_artifacts();
        
        // Create a temporary file
        let temp_dir = tempfile::tempdir().expect("Failed to create temp dir");
        let file_path = temp_dir.path().join("artifacts.bin");
        
        // Save to file
        original.save_to_file(&file_path).expect("Save should succeed");
        
        // Load from file
        let restored = CompiledArtifacts::load_from_file(&file_path)
            .expect("Load should succeed");
        
        // Verify the data matches
        assert_eq!(original.witgen_binary, restored.witgen_binary);
        assert_eq!(original.ad_binary, restored.ad_binary);
        assert_eq!(original.r1cs.constraints.len(), restored.r1cs.constraints.len());
    }

    #[test]
    fn test_field_element_serialization() {
        let witness_layout = WitnessLayout {
            algebraic_size: 1,
            multiplicities_size: 0,
            challenges_size: 0,
            tables_data_size: 0,
            lookups_data_size: 0,
        };

        let constraints_layout = ConstraintsLayout {
            algebraic_size: 1,
            tables_data_size: 0,
            lookups_data_size: 0,
        };

        // Test with a large field element
        let large_value = ark_bn254::Fr::from(u64::MAX);
        let r1c = R1C {
            a: vec![(1, large_value)],
            b: vec![(2, ark_bn254::Fr::from(42u64))],
            c: vec![(3, -ark_bn254::Fr::from(1u64))], // Test negative coefficient
        };

        let r1cs = R1CS {
            witness_layout,
            constraints_layout,
            constraints: vec![r1c],
        };

        let original = CompiledArtifacts::new(r1cs, vec![], vec![]);
        let bytes = original.to_bytes().expect("Serialization should succeed");
        let restored = CompiledArtifacts::from_bytes(&bytes)
            .expect("Deserialization should succeed");

        // Verify field elements match
        assert_eq!(
            original.r1cs.constraints[0].a[0].1,
            restored.r1cs.constraints[0].a[0].1
        );
        assert_eq!(
            original.r1cs.constraints[0].b[0].1,
            restored.r1cs.constraints[0].b[0].1
        );
        assert_eq!(
            original.r1cs.constraints[0].c[0].1,
            restored.r1cs.constraints[0].c[0].1
        );
    }
}

