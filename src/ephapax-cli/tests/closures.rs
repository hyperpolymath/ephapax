// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// closures.rs: v2 plan rung E9, closures.
//
// A closure is a cell `(table index, environment)` for a closure function
// `(environment, parameter) -> result`. Each program here runs as wasm and
// in the interpreter, and the 2 must print the expected value.

use std::path::Path;
use std::process::{Command, Output};

/// Run the `ephapax` binary with `args`, in the directory `dir`.
fn ephapax(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_ephapax"))
        .current_dir(dir)
        .args(args)
        .output()
        .expect("spawn ephapax")
}

/// Write each program (name, text, output) and run it as wasm and in the
/// interpreter, with the flags `flags`.
fn each_runs(flags: &[&str], programs: &[(&str, &str, &str)]) {
    let tmp = tempfile::tempdir().expect("tempdir");
    for (name, text, want) in programs {
        let file = format!("{name}.eph");
        std::fs::write(tmp.path().join(&file), text).expect("write program");
        for mode in [&["run"][..], &["run", "--interp"]] {
            let args: Vec<&str> = [mode, flags, &[file.as_str()]].concat();
            let out = ephapax(tmp.path(), &args);
            assert!(
                out.status.success(),
                "{name} under {args:?} failed:\n{}",
                String::from_utf8_lossy(&out.stderr)
            );
            let stdout = String::from_utf8_lossy(&out.stdout);
            assert_eq!(stdout.trim(), *want, "{name} under {args:?}");
        }
    }
}

/// A function of the module is a value: an argument, a `let` value, or a
/// call with too few arguments. The wasm module had no table for it and
/// was not valid.
#[test]
fn a_named_function_is_a_value() {
    let inc = "fn inc(n: I32): I32 = n + 1\n\n";
    let apply = "fn apply(f: I32 -> I32, x: I32): I32 = f(x)\n\n";
    let add = "fn add(a: I32, b: I32): I32 = a + b\n\n";
    let add3 = "fn add3(a: I32, b: I32, c: I32): I32 = a + b + c\n\n";
    each_runs(
        &[],
        &[
            (
                "argument",
                &format!("{inc}{apply}fn main(): I32 = apply(inc, 41)\n"),
                "42",
            ),
            (
                "let_value",
                &format!("{add}fn main(): I32 = let f = add in f(40, 2)\n"),
                "42",
            ),
            (
                "too_few",
                &format!("{add}fn main(): I32 = let f = add(40) in f(2)\n"),
                "42",
            ),
            (
                "one_at_a_time",
                &format!(
                    "{add3}fn main(): I32 = let f = add3 in let g = f(30) in \
                     let h = g(10) in h(2)\n"
                ),
                "42",
            ),
            (
                "too_few_then_more",
                &format!("{add3}fn main(): I32 = add3(30, 10)(2)\n"),
                "42",
            ),
            (
                "no_parameter",
                "fn answer(): I32 = 42\n\nfn call(f: () -> I32): I32 = f(())\n\n\
                 fn main(): I32 = call(answer)\n",
                "42",
            ),
            // The name is free in the lambda and is not a local.
            (
                "in_a_lambda",
                &format!(
                    "{inc}{apply}fn main(): I32 = let g = fn(x: I32) -> apply(inc, x) in g(41)\n"
                ),
                "42",
            ),
            (
                "used_2_times",
                &format!("{inc}fn main(): I32 = let f = inc in let g = inc in f(g(40))\n"),
                "42",
            ),
            (
                "generic",
                &format!("fn id<T>(x: T): T = x\n\n{apply}fn main(): I32 = apply(id, 42)\n"),
                "42",
            ),
            // Each parameter and the result keep their width.
            (
                "wide",
                "fn pick(a: I64, b: F64): I64 = a + a\n\n\
                 fn main(): I64 = let f = pick(5000000000) in f(1.5)\n",
                "10000000000i64",
            ),
        ],
    );

    // An extern function is a value too. The host of `run` does not have
    // these functions, so the program is compiled only.
    let tmp = tempfile::tempdir().expect("tempdir");
    std::fs::write(
        tmp.path().join("ext.eph"),
        "extern \"c\" {\n    fn host_inc(n: I32): I32\n    fn host_now(): I64\n    \
         fn host_log(n: I32): ()\n}\n\n\
         fn apply(f: I32 -> I32, x: I32): I32 = f(x)\n\n\
         fn main(): I32 = let t = host_now in let l = host_log in let u = l(1) in \
         apply(host_inc, 41)\n",
    )
    .expect("write program");
    let out = ephapax(tmp.path(), &["compile", "ext.eph"]);
    assert!(
        out.status.success(),
        "compile failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let wasm = std::fs::read(tmp.path().join("ext.wasm")).expect("read module");
    wasmparser::validate(&wasm).expect("the module must be valid wasm");
}

/// The body of a lambda can hold a lambda. The inner closure function was
/// not in the module: "unknown function".
#[test]
fn a_lambda_in_a_lambda_runs() {
    each_runs(
        &[],
        &[
            (
                "curry",
                "fn main(): I32 = let add = fn(a: I32) -> fn(b: I32) -> a + b in add(40)(2)\n",
                "42",
            ),
            (
                "curry3",
                "fn main(): I32 = let add = fn(a: I32) -> fn(b: I32) -> fn(c: I32) -> a + b + c \
                 in add(30)(10)(2)\n",
                "42",
            ),
            (
                "compose",
                "fn compose(f: I32 -> I32, g: I32 -> I32): I32 -> I32 = fn(x: I32) -> f(g(x))\n\n\
                 fn main(): I32 = compose(fn(a: I32) -> a + 1, fn(b: I32) -> b * 2)(20) + 1\n",
                "42",
            ),
        ],
    );
}

/// A parameter or a `let` name hides a function of the module that has
/// the same name. The wasm call went to the function of the module.
#[test]
fn a_local_hides_a_function_of_the_same_name() {
    let f = "fn f(n: I32): I32 = 0\n\n";
    each_runs(
        &[],
        &[
            (
                "parameter",
                &format!(
                    "{f}fn apply(f: I32 -> I32, x: I32): I32 = f(x)\n\n\
                     fn main(): I32 = apply(fn(n: I32) -> n + 1, 41)\n"
                ),
                "42",
            ),
            (
                "let_name",
                &format!("{f}fn main(): I32 = let f = fn(n: I32) -> n + 1 in f(41)\n"),
                "42",
            ),
        ],
    );
}

/// A lambda with an I64, F32 or F64 parameter or result is behind the
/// flag `--unstable-core`. With the flag, the closure function has the
/// wasm type of its parameter and of its result. (Each closure had the
/// type `(i32, i32) -> i32`, and such a lambda was refused.)
#[test]
fn a_wide_lambda_is_behind_the_flag() {
    let programs = [
        (
            "f64",
            "fn main(): F64 = let f = fn(x: F64) -> x + 1.5 in f(40.5)\n",
            "42",
        ),
        (
            "f32",
            "fn main(): F32 = let f = fn(x: F32) -> x + 1.5f32 in f(40.5f32)\n",
            "42f32",
        ),
        (
            "i64",
            "fn main(): I64 = let f = fn(x: I64) -> x + 5000000000 in f(5000000000)\n",
            "10000000000i64",
        ),
        (
            "result_only",
            "fn main(): I64 = let f = fn(x: I32) -> 5000000000 + 5000000000 in f(1)\n",
            "10000000000i64",
        ),
        (
            "parameter_only",
            "fn main(): I32 = let f = fn(x: I64) -> 42 in f(5000000000)\n",
            "42",
        ),
        (
            "argument",
            "fn apply(f: F64 -> F64, x: F64): F64 = f(x)\n\n\
             fn main(): F64 = apply(fn(n: F64) -> n * 2.0, 21.0)\n",
            "42",
        ),
        (
            "captured",
            "fn main(): I64 = let k = 5000000000 in let f = fn(x: F64) -> k + k in f(1.5)\n",
            "10000000000i64",
        ),
        (
            "3_types",
            "fn main(): F64 = let f = fn(a: F64) -> fn(b: I64) -> fn(c: F32) -> a \
             in f(42.0)(5000000000)(1.5f32)\n",
            "42",
        ),
    ];
    each_runs(&["--unstable-core"], &programs);

    // Without the flag, each command refuses the program by name.
    let tmp = tempfile::tempdir().expect("tempdir");
    for (name, text, _) in programs {
        let file = format!("{name}.eph");
        std::fs::write(tmp.path().join(&file), text).expect("write program");
        for command in [&["check"][..], &["compile"], &["run"], &["run", "--interp"]] {
            let args: Vec<&str> = [command, &[file.as_str()]].concat();
            let out = ephapax(tmp.path(), &args);
            let stderr = String::from_utf8_lossy(&out.stderr);
            assert!(
                !out.status.success()
                    && stderr.contains("behind the flag `--unstable-core`: a lambda"),
                "{name} under {args:?}: exit {:?}, stderr:\n{stderr}",
                out.status.code()
            );
        }
    }
}
