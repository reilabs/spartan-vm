use std::fs;
use std::path::PathBuf;

/// Represents an unexpected test result
#[derive(Debug, Clone)]
pub struct UnexpectedResult {
    pub test_name: String,
    pub expected_success: bool,
    pub error: Option<String>,
}

/// Information about how noir was sourced
#[derive(Debug)]
enum NoirSource {
    /// Git dependency with URL and commit hash
    Git { commit_hash: String },
    /// Registry (crates.io) dependency with version
    Registry { version: String },
}

/// Parses Cargo.lock to find how noir is sourced.
///
/// Looks for noir packages (noirc_driver, noirc_frontend, nargo, etc.) and
/// determines if they come from git or crates.io registry.
fn parse_noir_source(cargo_lock_content: &str) -> Result<NoirSource, String> {
    // Known noir package names to look for
    let noir_packages = [
        "noirc_driver",
        "noirc_frontend",
        "noirc_evaluator",
        "nargo",
        "nargo_toml",
        "noirc_abi",
        "noirc_errors",
        "fm",
    ];

    let lines: Vec<&str> = cargo_lock_content.lines().collect();

    for (i, line) in lines.iter().enumerate() {
        // Look for package declarations
        if line.starts_with("name = ") {
            let name = line
                .trim_start_matches("name = ")
                .trim_matches('"');

            if noir_packages.contains(&name) {
                // Look for the source line (should be within next few lines)
                for j in i..std::cmp::min(i + 5, lines.len()) {
                    let source_line = lines[j];
                    if source_line.starts_with("source = ") {
                        let source = source_line
                            .trim_start_matches("source = ")
                            .trim_matches('"');

                        // Check if it's a git source
                        if source.starts_with("git+") && source.contains("#") {
                            let commit_hash = source
                                .split('#')
                                .last()
                                .ok_or("Failed to parse git commit hash")?
                                .to_string();
                            return Ok(NoirSource::Git { commit_hash });
                        }

                        // Check if it's a registry source
                        if source.starts_with("registry+") {
                            // Get the version from previous lines
                            for k in (0..j).rev() {
                                if lines[k].starts_with("version = ") {
                                    let version = lines[k]
                                        .trim_start_matches("version = ")
                                        .trim_matches('"')
                                        .to_string();
                                    return Ok(NoirSource::Registry { version });
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    Err("Could not find noir dependency in Cargo.lock. Ensure a noir package (noirc_driver, nargo, etc.) is in your dependencies.".to_string())
}

/// Gets the cargo home directory
fn cargo_home() -> PathBuf {
    std::env::var("CARGO_HOME")
        .map(PathBuf::from)
        .unwrap_or_else(|_| {
            dirs::home_dir()
                .expect("Could not find home directory")
                .join(".cargo")
        })
}

/// Finds noir test_programs from a git checkout
fn find_git_checkout(commit_hash: &str) -> Result<PathBuf, String> {
    let checkouts_dir = cargo_home().join("git").join("checkouts");

    if !checkouts_dir.exists() {
        return Err(format!(
            "Cargo git checkouts directory not found at {:?}",
            checkouts_dir
        ));
    }

    // Search all checkout directories for one containing noir with test_programs
    let entries = fs::read_dir(&checkouts_dir)
        .map_err(|e| format!("Failed to read checkouts directory: {}", e))?;

    let short_hash = &commit_hash[..std::cmp::min(7, commit_hash.len())];

    for entry in entries.filter_map(|e| e.ok()) {
        let checkout_name = entry.file_name().to_string_lossy().to_lowercase();

        // Look for directories that might be noir (contains "noir" in name)
        if checkout_name.contains("noir") {
            // Check for the specific commit
            let commit_dir = entry.path().join(short_hash);
            if commit_dir.exists() {
                let test_programs = commit_dir.join("test_programs");
                if test_programs.exists()
                    && test_programs.join("execution_success").exists()
                    && test_programs.join("execution_failure").exists()
                {
                    return Ok(test_programs);
                }
            }
        }
    }

    // If not found by name, search all checkouts for the commit with test_programs
    let entries = fs::read_dir(&checkouts_dir)
        .map_err(|e| format!("Failed to read checkouts directory: {}", e))?;

    for entry in entries.filter_map(|e| e.ok()) {
        let commit_dir = entry.path().join(short_hash);
        if commit_dir.exists() {
            let test_programs = commit_dir.join("test_programs");
            if test_programs.exists()
                && test_programs.join("execution_success").exists()
                && test_programs.join("execution_failure").exists()
            {
                return Ok(test_programs);
            }
        }
    }

    Err(format!(
        "Could not find noir checkout with test_programs for commit {}",
        short_hash
    ))
}

/// Finds noir test_programs from a registry (crates.io) source
fn find_registry_source(version: &str) -> Result<PathBuf, String> {
    let registry_src = cargo_home().join("registry").join("src");

    if !registry_src.exists() {
        return Err(format!(
            "Cargo registry source directory not found at {:?}",
            registry_src
        ));
    }

    // Registry sources are in directories like:
    // ~/.cargo/registry/src/index.crates.io-<hash>/noir-<version>/
    // But individual noir packages are published separately, so we need to find
    // a noir package and look for test_programs in the same registry cache

    let entries = fs::read_dir(&registry_src)
        .map_err(|e| format!("Failed to read registry src directory: {}", e))?;

    for index_entry in entries.filter_map(|e| e.ok()) {
        let index_path = index_entry.path();
        if index_path.is_dir() {
            // Look for noir package directories
            if let Ok(pkg_entries) = fs::read_dir(&index_path) {
                for pkg_entry in pkg_entries.filter_map(|e| e.ok()) {
                    let pkg_name = pkg_entry.file_name().to_string_lossy().to_string();

                    // Look for noir-<version> directory (the main noir crate if published)
                    if pkg_name == format!("noir-{}", version) {
                        let test_programs = pkg_entry.path().join("test_programs");
                        if test_programs.exists()
                            && test_programs.join("execution_success").exists()
                            && test_programs.join("execution_failure").exists()
                        {
                            return Ok(test_programs);
                        }
                    }
                }
            }
        }
    }

    Err(format!(
        "Could not find noir test_programs for version {} in registry cache. \
        Note: test_programs may not be included in crates.io releases. \
        Consider using a git dependency instead.",
        version
    ))
}

/// Finds the noir test_programs directory.
///
/// This parses the Cargo.lock file in the workspace root to find the noir
/// dependency (either git or crates.io) and locates the test_programs directory.
fn find_noir_test_programs() -> Result<PathBuf, String> {
    // Find workspace root by looking for Cargo.lock
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let workspace_root = manifest_dir
        .parent()
        .ok_or("Failed to find workspace root")?;

    let cargo_lock_path = workspace_root.join("Cargo.lock");
    let cargo_lock_content = fs::read_to_string(&cargo_lock_path)
        .map_err(|e| format!("Failed to read Cargo.lock: {}", e))?;

    let source = parse_noir_source(&cargo_lock_content)?;

    match source {
        NoirSource::Git { commit_hash } => find_git_checkout(&commit_hash),
        NoirSource::Registry { version } => find_registry_source(&version),
    }
}

/// Runs the compatibility test harness.
///
/// This function iterates through the `execution_success` and `execution_failure`
/// test directories from the noir repository (version specified in Cargo.toml),
/// runs the provided runner function for each test case, and validates that
/// the results match expectations.
///
/// # Arguments
///
/// * `runner` - A function that takes a project path and returns `Ok(())` on
///   success or `Err(String)` on failure.
///
/// # Returns
///
/// * `Ok(())` - All tests matched their expectations
/// * `Err(Vec<UnexpectedResult>)` - A list of tests that did not match expectations
///
/// # Expectations
///
/// * Tests in `execution_success` should return `Ok(())`
/// * Tests in `execution_failure` should return `Err(_)`
pub fn run_harness(
    runner: fn(project: PathBuf) -> Result<(), String>,
) -> Result<(), Vec<UnexpectedResult>> {
    let test_programs = find_noir_test_programs()
        .map_err(|e| vec![UnexpectedResult {
            test_name: "<harness setup>".to_string(),
            expected_success: true,
            error: Some(e),
        }])?;

    let mut unexpected_results = Vec::new();
    let mut success_count = 0;
    let mut failure_count = 0;

    // Process execution_success tests
    let success_dir = test_programs.join("execution_success");
    if success_dir.exists() {
        println!("Running execution_success tests...");
        if let Ok(entries) = fs::read_dir(&success_dir) {
            for entry in entries.filter_map(|e| e.ok()) {
                let path = entry.path();
                if path.is_dir() {
                    let test_name = path.file_name()
                        .map(|n| n.to_string_lossy().to_string())
                        .unwrap_or_default();

                    print!("  {} ... ", test_name);
                    match runner(path) {
                        Ok(()) => {
                            println!("ok");
                            success_count += 1;
                        }
                        Err(e) => {
                            println!("UNEXPECTED FAILURE");
                            unexpected_results.push(UnexpectedResult {
                                test_name: format!("execution_success/{}", test_name),
                                expected_success: true,
                                error: Some(e),
                            });
                            failure_count += 1;
                        }
                    }
                }
            }
        }
    }

    // Process execution_failure tests
    let failure_dir = test_programs.join("execution_failure");
    if failure_dir.exists() {
        println!("\nRunning execution_failure tests...");
        if let Ok(entries) = fs::read_dir(&failure_dir) {
            for entry in entries.filter_map(|e| e.ok()) {
                let path = entry.path();
                if path.is_dir() {
                    let test_name = path.file_name()
                        .map(|n| n.to_string_lossy().to_string())
                        .unwrap_or_default();

                    print!("  {} ... ", test_name);
                    match runner(path) {
                        Ok(()) => {
                            println!("UNEXPECTED SUCCESS");
                            unexpected_results.push(UnexpectedResult {
                                test_name: format!("execution_failure/{}", test_name),
                                expected_success: false,
                                error: None,
                            });
                            failure_count += 1;
                        }
                        Err(_) => {
                            println!("ok (failed as expected)");
                            success_count += 1;
                        }
                    }
                }
            }
        }
    }

    // Print summary
    println!("\n--- Test Summary ---");
    println!("Passed: {}", success_count);
    println!("Failed: {}", failure_count);

    if unexpected_results.is_empty() {
        println!("\nAll tests matched expectations!");
        Ok(())
    } else {
        println!("\n--- Unexpected Results ---");
        for result in &unexpected_results {
            if result.expected_success {
                println!(
                    "  {} - Expected success, got failure: {}",
                    result.test_name,
                    result.error.as_deref().unwrap_or("unknown error")
                );
            } else {
                println!(
                    "  {} - Expected failure, got success",
                    result.test_name
                );
            }
        }
        Err(unexpected_results)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_find_noir_test_programs() {
        let result = find_noir_test_programs();
        assert!(result.is_ok(), "Failed to find test_programs: {:?}", result);

        let path = result.unwrap();
        assert!(path.exists(), "test_programs path does not exist");
        assert!(path.join("execution_success").exists());
        assert!(path.join("execution_failure").exists());
    }

    #[test]
    fn test_parse_noir_source_git() {
        let cargo_lock = r#"
[[package]]
name = "noirc_driver"
version = "1.0.0"
source = "git+https://github.com/noir-lang/noir.git?branch=master#abc1234567890"
"#;
        let result = parse_noir_source(cargo_lock);
        assert!(result.is_ok());
        match result.unwrap() {
            NoirSource::Git { commit_hash } => {
                assert_eq!(commit_hash, "abc1234567890");
            }
            _ => panic!("Expected Git source"),
        }
    }

    #[test]
    fn test_parse_noir_source_registry() {
        let cargo_lock = r#"
[[package]]
name = "noirc_driver"
version = "0.30.0"
source = "registry+https://github.com/rust-lang/crates.io-index"
"#;
        let result = parse_noir_source(cargo_lock);
        assert!(result.is_ok());
        match result.unwrap() {
            NoirSource::Registry { version } => {
                assert_eq!(version, "0.30.0");
            }
            _ => panic!("Expected Registry source"),
        }
    }
}
