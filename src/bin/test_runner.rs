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

struct TestResult {
    name: String,
    compiled: Status,
    r1cs: Status,
    rows: Option<usize>,
    cols: Option<usize>,
    witgen_compile: Status,
    ad_compile: Status,
    witgen_run: Status,
    witgen_correct: Status,
    witgen_noleak: Status,
    ad_run: Status,
    ad_correct: Status,
    ad_noleak: Status,
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
    let mut r = TestResult {
        name: name.to_string(),
        compiled: Status::Crash,
        r1cs: Status::Crash,
        rows: None,
        cols: None,
        witgen_compile: Status::Crash,
        ad_compile: Status::Crash,
        witgen_run: Status::Crash,
        witgen_correct: Status::Crash,
        witgen_noleak: Status::Crash,
        ad_run: Status::Crash,
        ad_correct: Status::Crash,
        ad_noleak: Status::Crash,
    };

    // Track which steps we've seen to distinguish crash vs skip
    let mut seen_compiled = false;
    let mut seen_r1cs = false;
    let mut seen_witgen_compile = false;
    let mut seen_ad_compile = false;
    let mut seen_witgen_run = false;
    let mut seen_witgen_correct = false;
    let mut seen_witgen_noleak = false;
    let mut seen_ad_run = false;
    let mut seen_ad_correct = false;

    for line in lines {
        let parts: Vec<&str> = line.split(':').collect();
        match parts.as_slice() {
            ["COMPILED", "ok"] => { r.compiled = Status::Pass; seen_compiled = true; }
            ["COMPILED", "fail"] => { r.compiled = Status::Fail; seen_compiled = true; }
            ["R1CS", "ok", rows, cols] => {
                r.r1cs = Status::Pass;
                r.rows = rows.parse().ok();
                r.cols = cols.parse().ok();
                seen_r1cs = true;
            }
            ["R1CS", "fail"] => { r.r1cs = Status::Fail; seen_r1cs = true; }
            ["WITGEN_COMPILE", "ok"] => { r.witgen_compile = Status::Pass; seen_witgen_compile = true; }
            ["WITGEN_COMPILE", "fail"] => { r.witgen_compile = Status::Fail; seen_witgen_compile = true; }
            ["AD_COMPILE", "ok"] => { r.ad_compile = Status::Pass; seen_ad_compile = true; }
            ["AD_COMPILE", "fail"] => { r.ad_compile = Status::Fail; seen_ad_compile = true; }
            ["WITGEN_RUN", "ok"] => { r.witgen_run = Status::Pass; seen_witgen_run = true; }
            ["WITGEN_RUN", "fail"] => { r.witgen_run = Status::Fail; seen_witgen_run = true; }
            ["WITGEN_CORRECT", "ok"] => { r.witgen_correct = Status::Pass; seen_witgen_correct = true; }
            ["WITGEN_CORRECT", "fail"] => { r.witgen_correct = Status::Fail; seen_witgen_correct = true; }
            ["WITGEN_NOLEAK", "ok"] => { r.witgen_noleak = Status::Pass; seen_witgen_noleak = true; }
            ["WITGEN_NOLEAK", "fail"] => { r.witgen_noleak = Status::Fail; seen_witgen_noleak = true; }
            ["AD_RUN", "ok"] => { r.ad_run = Status::Pass; seen_ad_run = true; }
            ["AD_RUN", "fail"] => { r.ad_run = Status::Fail; seen_ad_run = true; }
            ["AD_CORRECT", "ok"] => { r.ad_correct = Status::Pass; seen_ad_correct = true; }
            ["AD_CORRECT", "fail"] => { r.ad_correct = Status::Fail; seen_ad_correct = true; }
            ["AD_NOLEAK", "ok"] => { r.ad_noleak = Status::Pass; }
            ["AD_NOLEAK", "fail"] => { r.ad_noleak = Status::Fail; }
            _ => {}
        }
    }

    // Mark unseen steps as skip (prior step failed) vs crash (process died)
    // The child stops printing after a failure, so anything after the last seen line
    // that wasn't reported is a skip if the prior step failed, crash otherwise.
    if !seen_compiled { /* already Crash */ }
    else if r.compiled == Status::Fail {
        r.r1cs = Status::Skip; r.witgen_compile = Status::Skip; r.ad_compile = Status::Skip;
        r.witgen_run = Status::Skip; r.witgen_correct = Status::Skip; r.witgen_noleak = Status::Skip;
        r.ad_run = Status::Skip; r.ad_correct = Status::Skip; r.ad_noleak = Status::Skip;
    } else if !seen_r1cs { /* crash during r1cs */ }
    else if r.r1cs == Status::Fail {
        r.witgen_compile = Status::Skip; r.ad_compile = Status::Skip;
        r.witgen_run = Status::Skip; r.witgen_correct = Status::Skip; r.witgen_noleak = Status::Skip;
        r.ad_run = Status::Skip; r.ad_correct = Status::Skip; r.ad_noleak = Status::Skip;
    } else if !seen_witgen_compile { /* crash */ }
    else if r.witgen_compile == Status::Fail {
        r.ad_compile = Status::Skip;
        r.witgen_run = Status::Skip; r.witgen_correct = Status::Skip; r.witgen_noleak = Status::Skip;
        r.ad_run = Status::Skip; r.ad_correct = Status::Skip; r.ad_noleak = Status::Skip;
    } else if !seen_ad_compile { /* crash */ }
    else if r.ad_compile == Status::Fail {
        r.witgen_run = Status::Skip; r.witgen_correct = Status::Skip; r.witgen_noleak = Status::Skip;
        r.ad_run = Status::Skip; r.ad_correct = Status::Skip; r.ad_noleak = Status::Skip;
    } else {
        // Witgen branch
        if !seen_witgen_run { /* crash */ }
        else if r.witgen_run == Status::Fail {
            r.witgen_correct = Status::Skip; r.witgen_noleak = Status::Skip;
        } else {
            if !seen_witgen_correct { /* crash */ }
            if !seen_witgen_noleak && r.witgen_correct != Status::Crash { /* crash at noleak */ }
        }
        // AD branch
        if !seen_ad_run {
            // Could be crash or skip depending on witgen noleak status
            // If witgen branch completed, this is a crash
        } else if r.ad_run == Status::Fail {
            r.ad_correct = Status::Skip; r.ad_noleak = Status::Skip;
        } else {
            if !seen_ad_correct { /* crash */ }
        }
    }

    r
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
            r.compiled.emoji(),
            r.r1cs.emoji(),
            rows,
            cols,
            r.witgen_run.emoji(),
            r.witgen_correct.emoji(),
            r.witgen_noleak.emoji(),
            r.ad_run.emoji(),
            r.ad_correct.emoji(),
            r.ad_noleak.emoji(),
        ));
    }

    md
}
