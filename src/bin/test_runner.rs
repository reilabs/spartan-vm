use std::{
    collections::HashMap,
    env,
    fs,
    io::{BufRead, BufReader, Write},
    path::{Path, PathBuf},
    process::{Command, Stdio},
};

use ark_ff::UniformRand as _;
use noirc_abi::input_parser::{Format, InputValue};
use rand::SeedableRng;
use spartan_vm::{Project, compiler::Field, driver::Driver, vm::interpreter};

fn main() {
    let args: Vec<String> = env::args().collect();

    // Child mode: --run-single <path>
    if args.len() >= 3 && args[1] == "--run-single" {
        run_single(PathBuf::from(&args[2]));
        return;
    }

    // Regression check mode: --check-regression <baseline> <current>
    if args.len() >= 4 && args[1] == "--check-regression" {
        let baseline = PathBuf::from(&args[2]);
        let current = PathBuf::from(&args[3]);
        std::process::exit(check_regression(&baseline, &current));
    }

    // Growth check mode: --check-growth <baseline> <current>
    // Prints markdown to stdout if any rows/cols grew; exits 0 always.
    if args.len() >= 4 && args[1] == "--check-growth" {
        let baseline = PathBuf::from(&args[2]);
        let current = PathBuf::from(&args[3]);
        check_growth(&baseline, &current);
        return;
    }

    // Parent mode
    let output_path = parse_output_arg(&args);
    run_parent(&output_path);
}

fn parse_output_arg(args: &[String]) -> PathBuf {
    let mut i = 1;
    while i < args.len() {
        if args[i] == "--output" && i + 1 < args.len() {
            return PathBuf::from(&args[i + 1]);
        }
        i += 1;
    }
    PathBuf::from("STATUS.md")
}

// ── Child: run a single test ──────────────────────────────────────────

fn emit(line: &str) {
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    let _ = writeln!(out, "{line}");
    let _ = out.flush();
}

fn run_single(root: PathBuf) {
    // 1. Compile
    emit("START:COMPILED");
    let driver = (|| {
        let project = Project::new(root.clone()).ok()?;
        let mut driver = Driver::new(project, false);
        driver.run_noir_compiler().ok()?;
        driver.monomorphize().ok()?;
        driver.explictize_witness().ok()?;
        Some(driver)
    })();
    let mut driver = match driver {
        Some(d) => { emit("END:COMPILED:ok"); d }
        None => { emit("END:COMPILED:fail"); return; }
    };

    // 2. R1CS
    emit("START:R1CS");
    let r1cs = match driver.generate_r1cs() {
        Ok(r) => {
            let rows = r.constraints.len();
            let cols = r.witness_layout.size();
            emit(&format!("END:R1CS:ok:{rows}:{cols}"));
            Some(r)
        }
        Err(_) => { emit("END:R1CS:fail"); None }
    };

    // 3. Compile witgen  (depends on R1CS)
    let witgen_binary = r1cs.as_ref().and_then(|_| {
        emit("START:WITGEN_COMPILE");
        match driver.compile_witgen() {
            Ok(b) => { emit("END:WITGEN_COMPILE:ok"); Some(b) }
            Err(_) => { emit("END:WITGEN_COMPILE:fail"); None }
        }
    });

    // 4. Compile AD  (depends on R1CS, independent of witgen)
    let ad_binary = r1cs.as_ref().and_then(|_| {
        emit("START:AD_COMPILE");
        match driver.compile_ad() {
            Ok(b) => { emit("END:AD_COMPILE:ok"); Some(b) }
            Err(_) => { emit("END:AD_COMPILE:fail"); None }
        }
    });

    // Load inputs (needed for witgen run)
    let ordered_params = load_inputs(&root.join("Prover.toml"), &driver);

    // 5. Run witgen  (depends on WITGEN_COMPILE)
    let had_witgen_binary = witgen_binary.is_some();
    let witgen_result = witgen_binary.and_then(|mut binary| {
        emit("START:WITGEN_RUN");
        let r1cs = r1cs.as_ref().unwrap();
        let params = ordered_params.as_ref()?;
        let result = interpreter::run(
            &mut binary,
            r1cs.witness_layout,
            r1cs.constraints_layout,
            params,
        );
        emit("END:WITGEN_RUN:ok");
        Some(result)
    });
    if had_witgen_binary && witgen_result.is_none() {
        emit("START:WITGEN_RUN");
        emit("END:WITGEN_RUN:fail");
    }

    // 6. Check witgen correctness  (depends on WITGEN_RUN)
    if let (Some(result), Some(r1cs)) = (&witgen_result, &r1cs) {
        emit("START:WITGEN_CORRECT");
        let correct = r1cs.check_witgen_output(
            &result.out_wit_pre_comm,
            &result.out_wit_post_comm,
            &result.out_a,
            &result.out_b,
            &result.out_c,
        );
        emit(if correct { "END:WITGEN_CORRECT:ok" } else { "END:WITGEN_CORRECT:fail" });
    }

    // 7. Witgen leak check  (depends on WITGEN_RUN)
    if let Some(result) = &witgen_result {
        emit("START:WITGEN_NOLEAK");
        let tmpdir = tempfile::tempdir().unwrap();
        let leftover = result.instrumenter.plot(&tmpdir.path().join("wt.png"));
        emit(if leftover == 0 { "END:WITGEN_NOLEAK:ok" } else { "END:WITGEN_NOLEAK:fail" });
    }

    // 8. Run AD  (depends on AD_COMPILE, independent of witgen)
    let ad_result = ad_binary.and_then(|mut binary| {
        emit("START:AD_RUN");
        let r1cs = r1cs.as_ref().unwrap();
        let mut rng = rand::rngs::StdRng::seed_from_u64(42);
        let ad_coeffs: Vec<Field> = (0..r1cs.constraints.len())
            .map(|_| ark_bn254::Fr::rand(&mut rng))
            .collect();
        let (ad_a, ad_b, ad_c, ad_instrumenter) = interpreter::run_ad(
            &mut binary,
            &ad_coeffs,
            r1cs.witness_layout,
            r1cs.constraints_layout,
        );
        emit("END:AD_RUN:ok");
        Some((ad_coeffs, ad_a, ad_b, ad_c, ad_instrumenter))
    });

    // 9. Check AD correctness  (depends on AD_RUN)
    if let (Some((coeffs, ad_a, ad_b, ad_c, _)), Some(r1cs)) = (&ad_result, &r1cs) {
        emit("START:AD_CORRECT");
        let correct = r1cs.check_ad_output(coeffs, ad_a, ad_b, ad_c);
        emit(if correct { "END:AD_CORRECT:ok" } else { "END:AD_CORRECT:fail" });
    }

    // 10. AD leak check  (depends on AD_RUN)
    if let Some((_, _, _, _, instrumenter)) = &ad_result {
        emit("START:AD_NOLEAK");
        let tmpdir = tempfile::tempdir().unwrap();
        let leftover = instrumenter.plot(&tmpdir.path().join("ad.png"));
        emit(if leftover == 0 { "END:AD_NOLEAK:ok" } else { "END:AD_NOLEAK:fail" });
    }
}

fn load_inputs(file_path: &Path, driver: &Driver) -> Option<Vec<InputValue>> {
    let ext = file_path.extension().and_then(|e| e.to_str())?;
    let format = Format::from_ext(ext)?;
    let contents = fs::read_to_string(file_path).ok()?;
    let params = format.parse(&contents, driver.abi()).ok()?;
    let abi = driver.abi();
    let mut ordered = Vec::new();
    for name in abi.parameter_names() {
        ordered.push(params.get(name)?.clone());
    }
    Some(ordered)
}

// ── Parent: discover & run all tests ──────────────────────────────────

/// The step keys in display order.
const STEP_KEYS: &[&str] = &[
    "COMPILED", "R1CS", "WITGEN_COMPILE", "AD_COMPILE",
    "WITGEN_RUN", "WITGEN_CORRECT", "WITGEN_NOLEAK",
    "AD_RUN", "AD_CORRECT", "AD_NOLEAK",
];

struct TestResult {
    name: String,
    steps: HashMap<String, Status>,
    rows: Option<usize>,
    cols: Option<usize>,
}

/// Determined purely from child output:
/// - `started && ended ok` → Pass
/// - `started && ended fail` → Fail
/// - `started && no end` → Crash
/// - `never started` → Skip
#[derive(Clone, Copy, PartialEq)]
enum Status {
    Pass,
    Fail,
    Crash,
    Skip,
}

impl Status {
    fn emoji(self) -> &'static str {
        match self {
            Status::Pass => "✅",
            Status::Fail => "❌",
            Status::Crash => "💥",
            Status::Skip => "➖",
        }
    }
}

fn run_parent(output_path: &Path) {
    let tests_dir = PathBuf::from("noir_tests");
    let mut entries: Vec<PathBuf> = fs::read_dir(&tests_dir)
        .expect("Cannot read noir_tests/")
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    entries.sort();

    let exe = env::current_exe().expect("Cannot determine own exe path");
    let mut results = Vec::new();

    for dir in &entries {
        let name = dir.file_name().unwrap().to_string_lossy().to_string();
        let abs = fs::canonicalize(dir).unwrap();
        eprintln!("Running: {name}");

        let mut child = Command::new(&exe)
            .args(["--run-single", abs.to_str().unwrap()])
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .expect("Failed to spawn child");

        let stdout = child.stdout.take().unwrap();
        let lines: Vec<String> = BufReader::new(stdout)
            .lines()
            .map_while(Result::ok)
            .collect();

        let _ = child.wait();
        results.push(parse_child_output(&name, &lines));
    }

    let md = render_markdown(&results);
    fs::write(output_path, &md).expect("Cannot write output file");
    eprintln!("Wrote {}", output_path.display());
    print!("{md}");
}

fn parse_child_output(name: &str, lines: &[String]) -> TestResult {
    let mut started = HashMap::<String, bool>::new();
    let mut ended = HashMap::<String, bool>::new();
    let mut rows = None;
    let mut cols = None;

    for line in lines {
        let parts: Vec<&str> = line.split(':').collect();
        match parts.as_slice() {
            ["START", key] => { started.insert(key.to_string(), true); }
            ["END", key, "ok", ..] => {
                ended.insert(key.to_string(), true);
                if *key == "R1CS" && parts.len() >= 5 {
                    rows = parts[3].parse().ok();
                    cols = parts[4].parse().ok();
                }
            }
            ["END", key, "fail"] => { ended.insert(key.to_string(), false); }
            _ => {}
        }
    }

    let steps = STEP_KEYS
        .iter()
        .map(|&key| {
            let status = if let Some(&ok) = ended.get(key) {
                if ok { Status::Pass } else { Status::Fail }
            } else if started.contains_key(key) {
                Status::Crash
            } else {
                Status::Skip
            };
            (key.to_string(), status)
        })
        .collect();

    TestResult { name: name.to_string(), steps, rows, cols }
}

// ── Regression & growth checks ───────────────────────────────────────

struct ParsedRow {
    name: String,
    cells: Vec<String>,
    rows: Option<usize>,
    cols: Option<usize>,
}

fn parse_status_rows(path: &Path) -> Vec<ParsedRow> {
    let content = fs::read_to_string(path)
        .unwrap_or_else(|_| panic!("Cannot read {}", path.display()));
    let mut result = Vec::new();
    for line in content.lines().skip(2) {
        let cells: Vec<String> = line.split('|')
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .collect();
        if cells.len() < 11 { continue; }
        let rows = cells[3].parse().ok();
        let cols = cells[4].parse().ok();
        result.push(ParsedRow {
            name: cells[0].clone(),
            cells,
            rows,
            cols,
        });
    }
    result
}

const REGRESSION_COLS: &[(usize, &str)] = &[
    (1, "Compiled"), (2, "R1CS"),
    (5, "Witgen"), (6, "Witgen Correct"), (7, "Witgen No Leak"),
    (8, "AD"), (9, "AD Correct"), (10, "AD No Leak"),
];

fn check_regression(baseline_path: &Path, current_path: &Path) -> i32 {
    let baseline = parse_status_rows(baseline_path);
    let current = parse_status_rows(current_path);

    let base_map: HashMap<&str, &ParsedRow> = baseline.iter()
        .map(|r| (r.name.as_str(), r))
        .collect();

    let mut regressions = Vec::new();
    for cur in &current {
        let Some(base) = base_map.get(cur.name.as_str()) else { continue };
        for &(col, col_name) in REGRESSION_COLS {
            let base_val = &base.cells[col];
            let cur_val = &cur.cells[col];
            if base_val == "✅" && cur_val != "✅" {
                regressions.push(format!("  {} / {}: ✅ → {}", cur.name, col_name, cur_val));
            }
        }
    }

    if regressions.is_empty() {
        eprintln!("No regressions detected.");
        0
    } else {
        eprintln!("REGRESSIONS DETECTED:");
        for r in &regressions {
            eprintln!("{r}");
        }
        1
    }
}

fn check_growth(baseline_path: &Path, current_path: &Path) {
    let baseline = parse_status_rows(baseline_path);
    let current = parse_status_rows(current_path);

    let base_map: HashMap<&str, &ParsedRow> = baseline.iter()
        .map(|r| (r.name.as_str(), r))
        .collect();

    let mut warnings = Vec::new();
    for cur in &current {
        let Some(base) = base_map.get(cur.name.as_str()) else { continue };
        if let (Some(br), Some(cr)) = (base.rows, cur.rows) {
            if cr > br {
                warnings.push(format!(
                    "| {} | Constraints | {} | {} | +{} ({:+.1}%) |",
                    cur.name, br, cr, cr - br, (cr as f64 - br as f64) / br as f64 * 100.0
                ));
            }
        }
        if let (Some(bc), Some(cc)) = (base.cols, cur.cols) {
            if cc > bc {
                warnings.push(format!(
                    "| {} | Witnesses | {} | {} | +{} ({:+.1}%) |",
                    cur.name, bc, cc, cc - bc, (cc as f64 - bc as f64) / bc as f64 * 100.0
                ));
            }
        }
    }

    if warnings.is_empty() {
        println!("No R1CS constraint or witness count growth detected.");
        return;
    }

    println!("**R1CS constraint or witness count growth detected:**\n");
    println!("| Test | Metric | Before | After | Change |");
    println!("|------|--------|--------|-------|--------|");
    for w in &warnings {
        println!("{w}");
    }
}

fn render_markdown(results: &[TestResult]) -> String {
    let mut md = String::new();
    md.push_str("| Test | Compiled | R1CS | Rows | Cols | Witgen | Witgen Correct | Witgen No Leak | AD | AD Correct | AD No Leak |\n");
    md.push_str("|------|----------|------|------|------|--------|----------------|----------------|----|------------|------------|\n");

    for r in results {
        let s = |key: &str| r.steps.get(key).copied().unwrap_or(Status::Skip).emoji();
        let rows = r.rows.map_or("-".to_string(), |v| v.to_string());
        let cols = r.cols.map_or("-".to_string(), |v| v.to_string());
        md.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |\n",
            r.name,
            s("COMPILED"),
            s("R1CS"),
            rows,
            cols,
            s("WITGEN_RUN"),
            s("WITGEN_CORRECT"),
            s("WITGEN_NOLEAK"),
            s("AD_RUN"),
            s("AD_CORRECT"),
            s("AD_NOLEAK"),
        ));
    }

    md
}
