use std::{fs, io, path::Path};

use serde::{Deserialize, Serialize};

use crate::compiler::r1cs_gen::R1CS;

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CompiledArtifacts {
    pub r1cs: R1CS,
    pub witgen_binary: Vec<u64>,
    pub ad_binary: Vec<u64>,
}

#[derive(Debug)]
pub enum ArtifactError {
    Io(io::Error),
    Serialize(bincode::Error),
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

    pub fn to_bytes(&self) -> Result<Vec<u8>, ArtifactError> {
        bincode::serialize(self).map_err(ArtifactError::Serialize)
    }

    pub fn from_bytes(bytes: &[u8]) -> Result<Self, ArtifactError> {
        bincode::deserialize(bytes).map_err(ArtifactError::Deserialize)
    }

    pub fn save_to_file<P: AsRef<Path>>(&self, path: P) -> Result<(), ArtifactError> {
        let bytes = self.to_bytes()?;
        fs::write(path, bytes)?;
        Ok(())
    }

    pub fn load_from_file<P: AsRef<Path>>(path: P) -> Result<Self, ArtifactError> {
        let bytes = fs::read(path)?;
        Self::from_bytes(&bytes)
    }
}
