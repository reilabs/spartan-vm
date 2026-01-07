//! Prover.toml Parser
//!
//! Parses Noir Prover.toml files to extract input values.

use std::collections::BTreeMap;
use std::path::Path;

use anyhow::{Context, Result};
use serde::Deserialize;

/// Raw TOML value that can be a string, integer, or array
#[derive(Debug, Deserialize)]
#[serde(untagged)]
enum TomlValue {
    String(String),
    Integer(i64),
    Array(Vec<TomlValue>),
}

impl TomlValue {
    /// Flatten to a list of string values
    fn flatten(&self) -> Vec<String> {
        match self {
            TomlValue::String(s) => vec![s.clone()],
            TomlValue::Integer(n) => vec![n.to_string()],
            TomlValue::Array(arr) => arr.iter().flat_map(|v| v.flatten()).collect(),
        }
    }
}

/// Parse a Prover.toml file and return input values as strings
///
/// Returns a BTreeMap to maintain consistent ordering of inputs.
pub fn parse_prover_toml(path: &Path) -> Result<BTreeMap<String, String>> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("Failed to read {}", path.display()))?;

    let table: BTreeMap<String, TomlValue> = toml::from_str(&content)
        .with_context(|| format!("Failed to parse {}", path.display()))?;

    let mut result = BTreeMap::new();

    for (key, value) in table {
        let values = value.flatten();
        if values.len() == 1 {
            result.insert(key, values.into_iter().next().unwrap());
        } else {
            // For arrays, insert each element with indexed key
            for (i, v) in values.into_iter().enumerate() {
                result.insert(format!("{}[{}]", key, i), v);
            }
        }
    }

    Ok(result)
}

/// Parse Prover.toml and return values in order, suitable for function arguments
pub fn parse_prover_toml_ordered(path: &Path) -> Result<Vec<(String, String)>> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("Failed to read {}", path.display()))?;

    let table: BTreeMap<String, TomlValue> = toml::from_str(&content)
        .with_context(|| format!("Failed to parse {}", path.display()))?;

    let mut result = Vec::new();

    for (key, value) in table {
        let values = value.flatten();
        if values.len() == 1 {
            result.push((key, values.into_iter().next().unwrap()));
        } else {
            // For arrays, add each element
            for (i, v) in values.into_iter().enumerate() {
                result.push((format!("{}[{}]", key, i), v));
            }
        }
    }

    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;
    use tempfile::NamedTempFile;

    #[test]
    fn test_parse_simple() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "x = \"2\"").unwrap();
        writeln!(file, "y = \"3\"").unwrap();

        let result = parse_prover_toml(file.path()).unwrap();
        assert_eq!(result.get("x"), Some(&"2".to_string()));
        assert_eq!(result.get("y"), Some(&"3".to_string()));
    }

    #[test]
    fn test_parse_integers() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "x = 42").unwrap();
        writeln!(file, "y = 100").unwrap();

        let result = parse_prover_toml(file.path()).unwrap();
        assert_eq!(result.get("x"), Some(&"42".to_string()));
        assert_eq!(result.get("y"), Some(&"100".to_string()));
    }

    #[test]
    fn test_parse_array() {
        let mut file = NamedTempFile::new().unwrap();
        writeln!(file, "arr = [1, 2, 3]").unwrap();

        let result = parse_prover_toml(file.path()).unwrap();
        assert_eq!(result.get("arr[0]"), Some(&"1".to_string()));
        assert_eq!(result.get("arr[1]"), Some(&"2".to_string()));
        assert_eq!(result.get("arr[2]"), Some(&"3".to_string()));
    }
}
