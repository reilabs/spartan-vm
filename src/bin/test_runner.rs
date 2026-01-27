use std::{
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

fn status(line: &str) {
    let stdout = std::io::stdout();
    let mut out = stdout.lock();
    let _ = writeln!(out, "{line}");
    let _ = out.flush();
}

fn run_single(root: PathBuf) {
    // 1. Compile
    let project = match Project::new(root.clone()) {
        Ok(p) => p,
        Err(_) => { status("COMPILED:fail"); return; }
    };
    let mut driver = Driver::new(project, false);
    if driver.run_noir_compiler().is_err() { status("COMPILED:fail"); return; }
    if driver.monomorphize().is_err() { status("COMPILED:fail"); return; }
    if driver.explictize_witness().is_err() { status("COMPILED:fail"); return; }
    status("COMPILED:ok");

    // 2. R1CS
    let r1cs = match driver.generate_r1cs() {
        Ok(r) => r,
        Err(_) => { status("R1CS:fail"); return; }
    };
    let rows = r1cs.constraints.len();
    let cols = r1cs.witness_layout.size();
    status(&format!("R1CS:ok:{rows}:{cols}"));

    // 3. Compile witgen
    let mut witgen_binary = match driver.compile_witgen() {
        Ok(b) => b,
        Err(_) => { status("WITGEN_COMPILE:fail"); return; }
    };
    status("WITGEN_COMPILE:ok");

    // 4. Compile AD
    let mut ad_binary = match driver.compile_ad() {
        Ok(b) => b,
        Err(_) => { status("AD_COMPILE:fail"); return; }
    };
    status("AD_COMPILE:ok");

    // 5. Load inputs & run witgen
    let file_path = root.join("Prover.toml");
    let ordered_params = match load_inputs(&file_path, &driver) {
        Some(p) => p,
        None => { status("WITGEN_RUN:fail"); return; }
    };

    let witgen_result = interpreter::run(
        &mut witgen_binary,
        r1cs.witness_layout,
        r1cs.constraints_layout,
        &ordered_params,
    );
    status("WITGEN_RUN:ok");

    // 6. Check witgen correctness
    let correct = r1cs.check_witgen_output(
        &witgen_result.out_wit_pre_comm,
        &witgen_result.out_wit_post_comm,
        &witgen_result.out_a,
        &witgen_result.out_b,
        &witgen_result.out_c,
    );
    status(if correct { "WITGEN_CORRECT:ok" } else { "WITGEN_CORRECT:fail" });

    // 7. Witgen leak check
    let tmpdir = tempfile::tempdir().unwrap();
    let leftover = witgen_result.instrumenter.plot(&tmpdir.path().join("wt.png"));
    status(if leftover == 0 { "WITGEN_NOLEAK:ok" } else { "WITGEN_NOLEAK:fail" });

    // 8. Run AD
    let mut rng = rand::rngs::StdRng::seed_from_u64(42);
    let ad_coeffs: Vec<Field> = (0..r1cs.constraints.len())
        .map(|_| ark_bn254::Fr::rand(&mut rng))
        .collect();

    let (ad_a, ad_b, ad_c, ad_instrumenter) = interpreter::run_ad(
        &mut ad_binary,
        &ad_coeffs,
        r1cs.witness_layout,
        r1cs.constraints_layout,
    );
    status("AD_RUN:ok");

    // 9. Check AD correctness
    let ad_correct = r1cs.check_ad_output(&ad_coeffs, &ad_a, &ad_b, &ad_c);
    status(if ad_correct { "AD_CORRECT:ok" } else { "AD_CORRECT:fail" });

    // 10. AD leak check
    let leftover = ad_instrumenter.plot(&tmpdir.path().join("ad.png"));
    status(if leftover == 0 { "AD_NOLEAK:ok" } else { "AD_NOLEAK:fail" });
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

/// The ordered pipeline steps as they appear in the child's stdout protocol.
/// Each step lists its key and the index of its prerequisite (None = first step).
const STEPS: &[(&str, Option<usize>)] = &[
    ("COMPILED",        None),    // 0
    ("R1CS",            Some(0)), // 1
    ("WITGEN_COMPILE",  Some(1)), // 2
    ("AD_COMPILE",      Some(2)), // 3
    ("WITGEN_RUN",      Some(3)), // 4
    ("WITGEN_CORRECT",  Some(4)), // 5
    ("WITGEN_NOLEAK",   Some(5)), // 6
    ("AD_RUN",          Some(6)), // 7
    ("AD_CORRECT",      Some(7)), // 8
    ("AD_NOLEAK",       Some(8)), // 9
];

struct TestResult {
    name: String,
    steps: Vec<Status>,
    rows: Option<usize>,
    cols: Option<usize>,
}

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

fn step_index(key: &str) -> Option<usize> {
    STEPS.iter().position(|(k, _)| *k == key)
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
    let mut steps: Vec<Option<Status>> = vec![None; STEPS.len()];
    let mut rows = None;
    let mut cols = None;

    // Parse reported lines into the steps vec
    for line in lines {
        let parts: Vec<&str> = line.split(':').collect();
        let (key, ok) = match parts.as_slice() {
            [key, "ok", ..] => (*key, true),
            [key, "fail"] => (*key, false),
            _ => continue,
        };
        if let Some(idx) = step_index(key) {
            steps[idx] = Some(if ok { Status::Pass } else { Status::Fail });
            // R1CS carries extra fields
            if key == "R1CS" && ok && parts.len() >= 4 {
                rows = parts[2].parse().ok();
                cols = parts[3].parse().ok();
            }
        }
    }

    // Resolve None entries: if a prerequisite failed or crashed, it's Skip; otherwise Crash.
    let resolved: Vec<Status> = (0..STEPS.len())
        .map(|i| {
            if let Some(s) = steps[i] {
                return s;
            }
            // Not reported — check prerequisite
            if let Some(prereq) = STEPS[i].1 {
                if let Some(s) = steps[prereq] {
                    if s == Status::Fail {
                        return Status::Skip;
                    }
                    // prereq passed but this wasn't reported => crash
                } else {
                    // prereq also wasn't reported => skip (cascading)
                    return Status::Skip;
                }
            }
            Status::Crash
        })
        .collect();

    TestResult { name: name.to_string(), steps: resolved, rows, cols }
}

fn render_markdown(results: &[TestResult]) -> String {
    let mut md = String::new();
    md.push_str("| Test | Compiled | R1CS | Rows | Cols | Witgen | Witgen Correct | Witgen No Leak | AD | AD Correct | AD No Leak |\n");
    md.push_str("|------|----------|------|------|------|--------|----------------|----------------|----|------------|------------|\n");

    for r in results {
        let rows = r.rows.map_or("-".to_string(), |v| v.to_string());
        let cols = r.cols.map_or("-".to_string(), |v| v.to_string());
        md.push_str(&format!(
            "| {} | {} | {} | {} | {} | {} | {} | {} | {} | {} | {} |\n",
            r.name,
            r.steps[0].emoji(), // COMPILED
            r.steps[1].emoji(), // R1CS
            rows,
            cols,
            r.steps[4].emoji(), // WITGEN_RUN
            r.steps[5].emoji(), // WITGEN_CORRECT
            r.steps[6].emoji(), // WITGEN_NOLEAK
            r.steps[7].emoji(), // AD_RUN
            r.steps[8].emoji(), // AD_CORRECT
            r.steps[9].emoji(), // AD_NOLEAK
        ));
    }

    md
}
