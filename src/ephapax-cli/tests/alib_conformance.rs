// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//
// alib_conformance.rs — the aLib conformer (plan rung E6, experiment X8).
//
// Compiles stdlib/ALib.eph with the real `ephapax compile` pipeline, runs
// the module under wasmtime with the host imports the compiler emits
// (env.print_i32, env.print_string), and evaluates every pinned aLib vector
// in tests/alib_vectors/ (aggregate-library a877c2e; see PROVENANCE.adoc).
//
// Every vector is classified PASS, FAIL or SKIP, and every SKIP carries a
// reason:
//
//   SKIP out-of-domain   the vector's data is outside this binding's types
//                        (aLib Number is bound to I32 only, so a decimal
//                        argument or result is out; if_then_else is bound at
//                        A = I32 only, so string-valued vectors are out).
//   SKIP unimplemented   no binding for the operation (the string and
//                        collection groups: no host <-> wasm String or
//                        Collection ABI exists yet).
//
// Ratchet: the test fails if
//   - the pinned vector files change (SHA-256 check), or
//   - PASS drops below PASS_FLOOR, or
//   - any vector is FAIL and not listed in KNOWN_FAILS.
// When PASS rises above the floor the test prints a notice; raise the floor
// in the PR that causes it. The full per-vector table is printed with
// `cargo test --test alib_conformance -- --nocapture`.

use serde_json::Value;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fmt::Write as _;
use std::path::{Path, PathBuf};
use std::process::Command;
use wasmtime::{Engine, Instance, Linker, Module, Store, Val};

/// Recorded floor: 90 of 156 vectors pass at a877c2e (see the report in
/// tests/alib_vectors/PROVENANCE.adoc for the reconciliation with the
/// survey's 89/1/13/51 against 48b7694).
const PASS_FLOOR: usize = 90;

/// Vectors that are known to FAIL, as `category/op#index` (1-based).
/// Empty: any FAIL is unexpected.
const KNOWN_FAILS: &[&str] = &[];

/// Pinned vector files and their SHA-256 (aggregate-library a877c2e).
const PINNED: &[(&str, &str)] = &[
    (
        "arithmetic.json",
        "d38140c9b75f3fbbbad35ad2750ad6bc1336635cc201e4794f365133b7cc033d",
    ),
    (
        "collection.json",
        "6e5bc689712509e02e27a6a1707966f429a23cfd862ede9cc761d1d9f14bbc93",
    ),
    (
        "comparison.json",
        "40f90f945b15e91f29068a8845d7d1099d552ceecb340a10807065c45b453443",
    ),
    (
        "conditional.json",
        "0e3a592286d3506741103240d40aa27c9c8b0ebe3ba7727316f6ea715683a0f5",
    ),
    (
        "logical.json",
        "ce252d1c5e65b4625b3153d0c4e0a598a1f9ed2e1ae268ea664086134aaf4088",
    ),
    (
        "string.json",
        "bee65a9ed2d2c9e44c5e6667ae5d6b101220bff36c33e9fe3c1ac1f9d3f42320",
    ),
];

/// Total vectors and operations in the pinned files.
const PINNED_VECTORS: usize = 156;
const PINNED_OPERATIONS: usize = 29;

// ---------------------------------------------------------------------------
// Binding: aLib operation -> ALib.eph export, with wasm-level value kinds.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq)]
enum Kind {
    /// aLib Number (or A) bound to ephapax I32.
    I32,
    /// aLib Boolean bound to ephapax Bool (wasm i32 0/1).
    Bool,
}

struct Binding {
    export: &'static str,
    params: &'static [Kind],
    result: Kind,
}

/// The binding table. Keyed by `category/op` because `length` names two
/// aLib operations.
fn binding(key: &str) -> Option<Binding> {
    use Kind::{Bool, I32};
    let b = |export, params, result| {
        Some(Binding {
            export,
            params,
            result,
        })
    };
    match key {
        "arithmetic/absolute" => b("absolute", &[I32], I32),
        "arithmetic/add" => b("add", &[I32, I32], I32),
        "arithmetic/divide" => b("divide", &[I32, I32], I32),
        "arithmetic/max" => b("max", &[I32, I32], I32),
        "arithmetic/min" => b("min", &[I32, I32], I32),
        "arithmetic/modulo" => b("modulo", &[I32, I32], I32),
        "arithmetic/multiply" => b("multiply", &[I32, I32], I32),
        "arithmetic/negate" => b("negate", &[I32], I32),
        "arithmetic/subtract" => b("subtract", &[I32, I32], I32),
        "comparison/equal" => b("equal", &[I32, I32], Bool),
        "comparison/not_equal" => b("not_equal", &[I32, I32], Bool),
        "comparison/less_than" => b("less_than", &[I32, I32], Bool),
        "comparison/less_equal" => b("less_equal", &[I32, I32], Bool),
        "comparison/greater_than" => b("greater_than", &[I32, I32], Bool),
        "comparison/greater_equal" => b("greater_equal", &[I32, I32], Bool),
        "logical/and" => b("and_", &[Bool, Bool], Bool),
        "logical/or" => b("or_", &[Bool, Bool], Bool),
        "logical/not" => b("not_", &[Bool], Bool),
        "conditional/if_then_else" => b("if_then_else", &[Bool, I32, I32], I32),
        _ => None,
    }
}

/// A binding table: the current one, or the frozen historical one.
type Bind = fn(&str) -> Option<Binding>;

/// The operations bound when the survey measured 89/1/13/51 (48b7694).
/// Frozen: a binding added to `binding` later must not reach the
/// historical reproduction, or it could silently change that tally.
const HISTORICAL_BOUND: &[&str] = &[
    "arithmetic/absolute",
    "arithmetic/add",
    "arithmetic/divide",
    "arithmetic/max",
    "arithmetic/min",
    "arithmetic/modulo",
    "arithmetic/multiply",
    "arithmetic/negate",
    "arithmetic/subtract",
    "comparison/equal",
    "comparison/not_equal",
    "comparison/less_than",
    "comparison/less_equal",
    "comparison/greater_than",
    "comparison/greater_equal",
    "logical/and",
    "logical/or",
    "logical/not",
    "conditional/if_then_else",
];

/// The historical binding table: `binding`, restricted to `HISTORICAL_BOUND`.
fn historical_binding(key: &str) -> Option<Binding> {
    if HISTORICAL_BOUND.contains(&key) {
        binding(key)
    } else {
        None
    }
}

/// Why a whole category has no binding yet.
fn unimplemented_reason(category: &str) -> &'static str {
    match category {
        "string" => "no host<->wasm String ABI; String.len lowering is wrong today (probes s1/s6)",
        "collection" => "no host<->wasm Collection ABI and no lambda arguments (closures are E9)",
        _ => "operation has no ALib.eph binding",
    }
}

// ---------------------------------------------------------------------------
// Values and the wasm runner
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq)]
enum V {
    I32(i32),
    Bool(bool),
}

impl V {
    fn to_val(self) -> Val {
        match self {
            V::I32(n) => Val::I32(n),
            V::Bool(b) => Val::I32(i32::from(b)),
        }
    }
}

impl std::fmt::Display for V {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            V::I32(n) => write!(f, "{n}"),
            V::Bool(b) => write!(f, "{b}"),
        }
    }
}

struct Runner {
    store: Store<()>,
    instance: Instance,
}

/// Errors from calling into the module. A trap or an ill-typed result is a
/// FAIL of the vector, not a harness error.
impl Runner {
    fn new(wasm: &[u8]) -> Self {
        let engine = Engine::default();
        let module = Module::new(&engine, wasm).expect("compiled ALib module loads in wasmtime");
        let mut store = Store::new(&engine, ());
        let mut linker = Linker::new(&engine);
        linker
            .func_wrap("env", "print_i32", |_v: i32| {})
            .expect("define env.print_i32");
        linker
            .func_wrap("env", "print_string", |_p: i32, _l: i32| {})
            .expect("define env.print_string");
        let instance = linker
            .instantiate(&mut store, &module)
            .expect("ALib module instantiates");
        Runner { store, instance }
    }

    fn call(&mut self, b: &Binding, args: &[V]) -> Result<V, String> {
        let func = self
            .instance
            .get_func(&mut self.store, b.export)
            .ok_or_else(|| format!("export `{}` missing from ALib.wasm", b.export))?;
        let params: Vec<Val> = args.iter().map(|a| a.to_val()).collect();
        let mut results = [Val::I32(0)];
        func.call(&mut self.store, &params, &mut results)
            .map_err(|e| format!("trap in `{}`: {e}", b.export))?;
        let raw = results[0]
            .i32()
            .ok_or_else(|| format!("`{}` returned a non-i32 value", b.export))?;
        match b.result {
            Kind::I32 => Ok(V::I32(raw)),
            Kind::Bool => match raw {
                0 => Ok(V::Bool(false)),
                1 => Ok(V::Bool(true)),
                n => Err(format!("`{}` returned {n}, not a Bool (0/1)", b.export)),
            },
        }
    }
}

// ---------------------------------------------------------------------------
// Condition expressions (aLib vectors/GRAMMAR.adoc: `condition = expr`)
// ---------------------------------------------------------------------------

#[derive(Debug)]
enum Expr {
    Call(String, Vec<Expr>),
    Bool(bool),
    Num(String),
    Str(String),
}

struct Parser<'a> {
    s: &'a [u8],
    i: usize,
}

impl<'a> Parser<'a> {
    fn ws(&mut self) {
        while self.i < self.s.len() && (self.s[self.i] == b' ' || self.s[self.i] == b'\t') {
            self.i += 1;
        }
    }

    fn expr(&mut self) -> Result<Expr, String> {
        self.ws();
        let c = *self.s.get(self.i).ok_or("unexpected end of condition")?;
        if c == b'"' {
            let start = self.i + 1;
            let end = start
                + self.s[start..]
                    .iter()
                    .position(|&b| b == b'"')
                    .ok_or("unterminated string")?;
            self.i = end + 1;
            return Ok(Expr::Str(
                String::from_utf8_lossy(&self.s[start..end]).into(),
            ));
        }
        if c == b'-' || c.is_ascii_digit() {
            let start = self.i;
            self.i += 1;
            while self.i < self.s.len()
                && (self.s[self.i].is_ascii_digit() || self.s[self.i] == b'.')
            {
                self.i += 1;
            }
            return Ok(Expr::Num(
                String::from_utf8_lossy(&self.s[start..self.i]).into(),
            ));
        }
        if c.is_ascii_alphabetic() || c == b'_' {
            let start = self.i;
            while self.i < self.s.len()
                && (self.s[self.i].is_ascii_alphanumeric() || self.s[self.i] == b'_')
            {
                self.i += 1;
            }
            let name = String::from_utf8_lossy(&self.s[start..self.i]).into_owned();
            self.ws();
            if self.s.get(self.i) == Some(&b'(') {
                self.i += 1;
                let mut args = Vec::new();
                self.ws();
                if self.s.get(self.i) == Some(&b')') {
                    self.i += 1;
                } else {
                    loop {
                        args.push(self.expr()?);
                        self.ws();
                        match self.s.get(self.i) {
                            Some(b',') => self.i += 1,
                            Some(b')') => {
                                self.i += 1;
                                break;
                            }
                            _ => return Err("expected `,` or `)`".into()),
                        }
                    }
                }
                return Ok(Expr::Call(name, args));
            }
            return match name.as_str() {
                "true" => Ok(Expr::Bool(true)),
                "false" => Ok(Expr::Bool(false)),
                _ => Err(format!(
                    "identifier `{name}` in a condition (conditions have no parameters)"
                )),
            };
        }
        Err(format!("unexpected character `{}`", c as char))
    }
}

fn parse_condition(src: &str) -> Result<Expr, String> {
    let mut p = Parser {
        s: src.as_bytes(),
        i: 0,
    };
    let e = p.expr()?;
    p.ws();
    if p.i != p.s.len() {
        return Err(format!("trailing input in condition `{src}`"));
    }
    Ok(e)
}

/// Outcome of evaluating one vector.
enum Verdict {
    Pass,
    Fail(String),
    SkipOutOfDomain(String),
    SkipUnimplemented(String),
}

/// A reason to stop evaluating a vector without a PASS/FAIL verdict.
enum Stop {
    OutOfDomain(String),
    Unimplemented(String),
    Fail(String),
}

/// Find the aLib category of an operation name used inside a condition.
/// `length` is ambiguous (string/collection); neither is bound, so it is
/// reported unimplemented.
fn category_of(op: &str, ops: &BTreeMap<String, String>) -> Option<String> {
    ops.get(op).cloned()
}

fn eval(
    e: &Expr,
    want: Kind,
    runner: &mut Runner,
    ops: &BTreeMap<String, String>,
    bind: Bind,
) -> Result<V, Stop> {
    match e {
        Expr::Bool(b) => match want {
            Kind::Bool => Ok(V::Bool(*b)),
            Kind::I32 => Err(Stop::Fail(format!(
                "Boolean literal where I32 expected: {b}"
            ))),
        },
        Expr::Num(s) => match want {
            Kind::I32 => s
                .parse::<i32>()
                .map(V::I32)
                .map_err(|_| Stop::OutOfDomain(format!("number `{s}` is not an I32"))),
            Kind::Bool => Err(Stop::Fail(format!("number `{s}` where Boolean expected"))),
        },
        Expr::Str(s) => Err(Stop::OutOfDomain(format!(
            "string literal \"{s}\" in a condition"
        ))),
        Expr::Call(op, args) => {
            let cat = category_of(op, ops)
                .ok_or_else(|| Stop::Fail(format!("unknown operation `{op}`")))?;
            let key = format!("{cat}/{op}");
            let b = bind(&key).ok_or_else(|| {
                Stop::Unimplemented(format!(
                    "condition calls `{key}`: {}",
                    unimplemented_reason(&cat)
                ))
            })?;
            if b.result != want {
                return Err(Stop::Fail(format!(
                    "`{key}` returns {:?}, {want:?} expected",
                    b.result
                )));
            }
            if args.len() != b.params.len() {
                return Err(Stop::Fail(format!(
                    "`{key}` called with {} argument(s)",
                    args.len()
                )));
            }
            let mut vals = Vec::new();
            for (a, k) in args.iter().zip(b.params) {
                vals.push(eval(a, *k, runner, ops, bind)?);
            }
            runner.call(&b, &vals).map_err(Stop::Fail)
        }
    }
}

/// Lower one JSON vector argument at a declared parameter kind.
fn lower_arg(
    v: &Value,
    k: Kind,
    runner: &mut Runner,
    ops: &BTreeMap<String, String>,
    bind: Bind,
) -> Result<V, Stop> {
    match (k, v) {
        (Kind::Bool, Value::Bool(b)) => Ok(V::Bool(*b)),
        // A Boolean-typed string is a condition expression (GRAMMAR.adoc).
        (Kind::Bool, Value::String(s)) => {
            let e = parse_condition(s).map_err(|m| Stop::Fail(format!("bad condition: {m}")))?;
            eval(&e, Kind::Bool, runner, ops, bind)
        }
        (Kind::I32, Value::Number(n)) => n
            .as_i64()
            .and_then(|i| i32::try_from(i).ok())
            .map(V::I32)
            .ok_or_else(|| {
                Stop::OutOfDomain(format!(
                    "argument {n} is not an I32 (decimal or out of range)"
                ))
            }),
        (Kind::I32, Value::String(s)) => Err(Stop::OutOfDomain(format!(
            "argument \"{s}\" is a String; this binding is at I32"
        ))),
        (k, other) => Err(Stop::Fail(format!(
            "argument {other} does not fit parameter kind {k:?}"
        ))),
    }
}

fn lower_expected(v: &Value, k: Kind) -> Result<V, Stop> {
    match (k, v) {
        (Kind::Bool, Value::Bool(b)) => Ok(V::Bool(*b)),
        (Kind::I32, Value::Number(n)) => n
            .as_i64()
            .and_then(|i| i32::try_from(i).ok())
            .map(V::I32)
            .ok_or_else(|| Stop::OutOfDomain(format!("expected result {n} is not an I32"))),
        (Kind::I32, Value::String(s)) => Err(Stop::OutOfDomain(format!(
            "expected result \"{s}\" is a String; this binding is at I32"
        ))),
        (k, other) => Err(Stop::Fail(format!(
            "expected result {other} does not fit {k:?}"
        ))),
    }
}

fn run_vector(
    key: &str,
    category: &str,
    op: &Value,
    vector: &Value,
    runner: &mut Runner,
    ops: &BTreeMap<String, String>,
    bind: Bind,
) -> Verdict {
    let Some(b) = bind(key) else {
        return Verdict::SkipUnimplemented(unimplemented_reason(category).into());
    };
    let result = (|| -> Result<Verdict, Stop> {
        // Positional or keyed input; keyed order comes from `parameters`.
        let params = op["parameters"].as_array().expect("parameters array");
        let input = &vector["input"];
        let raw: Vec<&Value> = match input {
            Value::Array(a) => a.iter().collect(),
            Value::Object(o) => params
                .iter()
                .map(|p| {
                    let name = p["name"].as_str().expect("keyed parameter has a name");
                    o.get(name).expect("keyed input has every parameter")
                })
                .collect(),
            other => panic!("{key}: input is neither list nor object: {other}"),
        };
        assert_eq!(
            raw.len(),
            b.params.len(),
            "{key}: arity mismatch with binding"
        );
        // Check the expected output's domain first, so a decimal result is a
        // SKIP even when every argument is in the I32 domain.
        let want = lower_expected(&vector["output"], b.result)?;
        let mut args = Vec::new();
        for (v, k) in raw.iter().zip(b.params) {
            args.push(lower_arg(v, *k, runner, ops, bind)?);
        }
        let got = runner.call(&b, &args).map_err(Stop::Fail)?;
        if got == want {
            Ok(Verdict::Pass)
        } else {
            let shown: Vec<String> = args.iter().map(ToString::to_string).collect();
            Ok(Verdict::Fail(format!(
                "{}({}) = {got}, want {want}",
                b.export,
                shown.join(", ")
            )))
        }
    })();
    match result {
        Ok(v) => v,
        Err(Stop::OutOfDomain(m)) => Verdict::SkipOutOfDomain(m),
        Err(Stop::Unimplemented(m)) => Verdict::SkipUnimplemented(m),
        Err(Stop::Fail(m)) => Verdict::Fail(m),
    }
}

// ---------------------------------------------------------------------------
// Harness
// ---------------------------------------------------------------------------

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repo root")
}

fn compile_alib(root: &Path, out_dir: &Path) -> Vec<u8> {
    let out = out_dir.join("ALib.wasm");
    let output = Command::new(env!("CARGO_BIN_EXE_ephapax"))
        .current_dir(root)
        .args([
            "compile",
            "stdlib/ALib.eph",
            "-o",
            out.to_str().expect("utf8 temp path"),
        ])
        .output()
        .expect("run ephapax compile");
    assert!(
        output.status.success(),
        "`ephapax compile stdlib/ALib.eph` failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::read(&out).expect("read ALib.wasm")
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().fold(String::new(), |mut s, b| {
        let _ = write!(s, "{b:02x}");
        s
    })
}

/// Load the pinned vector files, checking each SHA-256 and the format tag.
fn load_pinned(root: &Path) -> Vec<Value> {
    let vec_dir = root.join("tests/alib_vectors");
    PINNED
        .iter()
        .map(|(name, sha)| {
            let bytes = std::fs::read(vec_dir.join(name)).expect("read pinned vector file");
            let got = hex(&Sha256::digest(&bytes));
            assert_eq!(
                &got, sha,
                "pinned vector file {name} changed (re-pin deliberately)"
            );
            let json: Value = serde_json::from_slice(&bytes).expect("vector file is JSON");
            assert_eq!(
                json["format"], "alib-vectors-1",
                "{name}: unexpected format"
            );
            json
        })
        .collect()
}

/// Result of one conformance run.
#[derive(Default)]
struct Tally {
    pass: usize,
    fail: usize,
    out_of_domain: usize,
    unimplemented: usize,
    operations: usize,
    /// `category/op#n` of every FAIL, with its detail.
    fails: Vec<(String, String)>,
    /// One TSV line per vector: id, verdict, description, detail.
    table: String,
}

impl Tally {
    fn total(&self) -> usize {
        self.pass + self.fail + self.out_of_domain + self.unimplemented
    }

    fn summary(&self) -> String {
        format!(
            "{} vectors: {} pass / {} fail / {} skip out-of-domain / {} skip unimplemented",
            self.total(),
            self.pass,
            self.fail,
            self.out_of_domain,
            self.unimplemented
        )
    }
}

/// Evaluate every vector of `files` against the compiled module.
fn conform(files: &[Value], runner: &mut Runner, bind: Bind) -> Tally {
    // Operation name -> category, for condition calls.
    let mut ops = BTreeMap::new();
    for f in files {
        let cat = f["category"].as_str().expect("category").to_string();
        for op in f["operations"].as_array().expect("operations") {
            ops.insert(op["name"].as_str().expect("name").to_string(), cat.clone());
        }
    }
    let mut t = Tally::default();
    for f in files {
        let cat = f["category"].as_str().expect("category");
        for op in f["operations"].as_array().expect("operations") {
            t.operations += 1;
            let name = op["name"].as_str().expect("name");
            let key = format!("{cat}/{name}");
            for (i, v) in op["vectors"]
                .as_array()
                .expect("vectors")
                .iter()
                .enumerate()
            {
                let id = format!("{key}#{}", i + 1);
                let desc = v["description"].as_str().unwrap_or("");
                let (tag, detail) = match run_vector(&key, cat, op, v, runner, &ops, bind) {
                    Verdict::Pass => {
                        t.pass += 1;
                        ("PASS", String::new())
                    }
                    Verdict::Fail(m) => {
                        t.fail += 1;
                        t.fails.push((id.clone(), m.clone()));
                        ("FAIL", m)
                    }
                    Verdict::SkipOutOfDomain(m) => {
                        t.out_of_domain += 1;
                        ("SKIP-out-of-domain", m)
                    }
                    Verdict::SkipUnimplemented(m) => {
                        t.unimplemented += 1;
                        ("SKIP-unimplemented", m)
                    }
                };
                let _ = writeln!(t.table, "{id}\t{tag}\t{desc}\t{detail}");
            }
        }
    }
    t
}

/// Compile ALib.eph once per test and load it.
fn alib_runner(root: &Path) -> Runner {
    let tmp = tempfile::tempdir().expect("tempdir");
    let wasm = compile_alib(root, tmp.path());
    Runner::new(&wasm)
}

#[test]
fn alib_conformance_ratchet() {
    let root = repo_root();
    let files = load_pinned(&root);
    let mut runner = alib_runner(&root);
    let t = conform(&files, &mut runner, binding);

    println!("{}", t.table);
    println!(
        "aLib conformance (aggregate-library a877c2e): {}",
        t.summary()
    );

    assert_eq!(t.operations, PINNED_OPERATIONS, "operation count");
    assert_eq!(t.total(), PINNED_VECTORS, "vector count");
    let unexpected: Vec<String> = t
        .fails
        .iter()
        .filter(|(id, _)| !KNOWN_FAILS.contains(&id.as_str()))
        .map(|(id, m)| format!("{id}: {m}"))
        .collect();
    assert!(
        unexpected.is_empty(),
        "unexpected FAIL (not in KNOWN_FAILS):\n{}",
        unexpected.join("\n")
    );
    for k in KNOWN_FAILS {
        assert!(
            t.table.lines().any(|l| l.starts_with(&format!("{k}\t"))),
            "KNOWN_FAILS entry {k} names no vector"
        );
    }
    assert!(
        t.pass >= PASS_FLOOR,
        "PASS dropped below the recorded floor: {} < {PASS_FLOOR}",
        t.pass
    );
    if t.pass > PASS_FLOOR {
        println!(
            "NOTICE: {} pass > PASS_FLOOR {PASS_FLOOR}; raise PASS_FLOOR in this PR",
            t.pass
        );
    }
}

/// X8: reproduce the survey's scratch measurement (89 pass / 1 fail /
/// 13 out of the I32 domain / 51 unimplemented, against aggregate-library
/// 48b7694) with this Rust/wasmtime conformer.
///
/// 48b7694 has no JSON export, so the vectors are rebuilt from the pinned
/// a877c2e files by undoing exactly the two vector changes a877c2e made
/// (`git diff 48b7694 a877c2e -- specs/` touches only these):
///   - logical/not vector 3: input `["not(true)"]` back to the defective
///     literal `[true]` (output stays `true`), and
///   - string/substring: drop the two boundary vectors a877c2e appended
///     (vectors 7 and 8).
///
/// It binds only `HISTORICAL_BOUND`, so bindings added later leave this
/// tally unchanged; the ratchet test above tracks them.
#[test]
fn alib_reproduces_survey_baseline_48b7694() {
    let root = repo_root();
    let mut files = load_pinned(&root);
    for f in &mut files {
        let cat = f["category"].as_str().expect("category").to_string();
        for op in f["operations"].as_array_mut().expect("operations") {
            let name = op["name"].as_str().expect("name").to_string();
            let vectors = op["vectors"].as_array_mut().expect("vectors");
            match (cat.as_str(), name.as_str()) {
                ("logical", "not") => {
                    assert_eq!(vectors[2]["input"], serde_json::json!(["not(true)"]));
                    vectors[2]["input"] = serde_json::json!([true]);
                }
                ("string", "substring") => {
                    assert_eq!(vectors.len(), 8, "substring vector count at a877c2e");
                    vectors.truncate(6);
                }
                _ => {}
            }
        }
    }
    for key in HISTORICAL_BOUND {
        assert!(
            binding(key).is_some(),
            "historical binding {key} is gone from the binding table"
        );
    }
    let mut runner = alib_runner(&root);
    let t = conform(&files, &mut runner, historical_binding);
    println!("aLib conformance (reconstructed 48b7694): {}", t.summary());
    assert_eq!(
        (t.pass, t.fail, t.out_of_domain, t.unimplemented),
        (89, 1, 13, 51),
        "survey baseline not reproduced"
    );
    assert_eq!(t.fails.len(), 1);
    assert_eq!(
        t.fails[0].0, "logical/not#3",
        "the one FAIL is the spec defect"
    );
}

/// The pinned aLib modulo vectors use only nonnegative operands, and aLib
/// leaves the sign of a remainder with negative operands to the
/// implementation. This binding's choice is the truncated remainder (wasm
/// `i32.rem_s`: the result takes the dividend's sign). An unsigned lowering
/// would still pass the pinned vectors, so pin the choice here, through the
/// compiled `modulo` export, without touching the pinned files.
#[test]
fn alib_modulo_is_the_signed_truncated_remainder() {
    let root = repo_root();
    let mut runner = alib_runner(&root);
    let b = binding("arithmetic/modulo").expect("modulo is bound");
    for (a, d, want) in [(-7, 3, -1), (7, -3, 1), (-7, -3, -1), (7, 3, 1)] {
        let got = runner
            .call(&b, &[V::I32(a), V::I32(d)])
            .unwrap_or_else(|e| panic!("modulo({a}, {d}) failed: {e}"));
        assert_eq!(got, V::I32(want), "modulo({a}, {d})");
    }
}

#[test]
fn condition_parser_accepts_the_grammar_examples() {
    for src in [
        "greater_than(3, 5)",
        "not(true)",
        "equal(5, 5)",
        "f()",
        "g(-1.5, \"x\", h(true))",
    ] {
        parse_condition(src).unwrap_or_else(|e| panic!("{src}: {e}"));
    }
    for bad in ["x", "f(1", "f(1,)", "1 2"] {
        assert!(parse_condition(bad).is_err(), "{bad} should be rejected");
    }
}
