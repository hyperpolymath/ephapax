// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// constants.rs: a top-level constant, `let K = 40` or `let K: I32 = 40`.
//
// The grammar had the declaration, and only the core parser read it: the
// surface parser refused it, the type checker did not check its value,
// and no backend had code for it. A constant is now a value that each
// function of its module can name. Its value is computed at each use (in
// wasm, a constant is a function with no parameter). Each program here
// runs as wasm and in the interpreter, and the 2 must print the expected
// value.

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

/// Write each program (name, text, output) into `dir` and run it as wasm
/// and in the interpreter, with the flags `flags`.
fn each_runs(dir: &Path, flags: &[&str], programs: &[(&str, &str, &str)]) {
    for (name, text, want) in programs {
        let file = format!("{name}.eph");
        std::fs::write(dir.join(&file), text).expect("write program");
        for mode in [&["run"][..], &["run", "--interp"]] {
            let args: Vec<&str> = [mode, flags, &[file.as_str()]].concat();
            let out = ephapax(dir, &args);
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

/// `check` refuses `text` with a message that has `error` in it.
fn check_refuses(dir: &Path, name: &str, text: &str, error: &str) {
    let file = format!("{name}.eph");
    std::fs::write(dir.join(&file), text).expect("write program");
    let out = ephapax(dir, &["check", &file]);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !out.status.success() && stderr.contains(error),
        "{name}: exit {:?}, stderr:\n{stderr}",
        out.status.code()
    );
}

#[test]
fn a_top_level_constant_runs() {
    let tmp = tempfile::tempdir().expect("tempdir");
    each_runs(
        tmp.path(),
        &[],
        &[
            ("plain", "let K = 40\n\nfn main(): I32 = K + 2\n", "42"),
            // A lower-case name, and a type in the declaration.
            (
                "lower_case",
                "let k: I32 = 40\n\nlet two = 2\n\nfn main(): I32 = k + two\n",
                "42",
            ),
            // A constant sees the constants before it and the functions
            // of the module. A function sees each constant.
            (
                "order",
                "fn double(n: I32): I32 = n * 2\n\nlet K = double(10)\n\nlet M = K + 1\n\n\
                 fn add(n: I32): I32 = n + K\n\nfn main(): I32 = add(1) + M\n",
                "42",
            ),
            // In the body of a lambda: a constant is not captured.
            (
                "in_a_lambda",
                "fn twice(f: I32 -> I32, x: I32): I32 = f(f(x))\n\nlet STEP = 20\n\n\
                 fn main(): I32 = twice(fn(n: I32) -> n + STEP, 2)\n",
                "42",
            ),
            // A `let` and a parameter hide a constant of the same name.
            (
                "hidden",
                "let K = 1000\n\nfn shadow(K: I32): I32 = K + 1\n\n\
                 fn main(): I32 = let K = 1 in K + shadow(40)\n",
                "42",
            ),
            // Each value type keeps its width.
            (
                "wide",
                "let BIG = 5000000000\n\nlet HALF = 1.5\n\nlet YES = true\n\n\
                 fn main(): I64 = if YES && HALF > 1.0 then BIG + BIG else BIG\n",
                "10000000000i64",
            ),
            // A closure, a pair, a list, and a value of a `data` type.
            (
                "values",
                "data Option(a) = None | Some(a)\n\nlet INC = fn(n: I32) -> n + 1\n\n\
                 let PAIR = (30, 2)\n\nlet XS = [4, 5]\n\nlet SOME: Option(I32) = Some(0)\n\n\
                 fn main(): I32 =\n  \
                 INC(PAIR.0 + PAIR.1 + XS[0] + XS[1]) + (match SOME of | None => 1 | Some(n) => n end)\n",
                "42",
            ),
            // The value uses a generic function.
            (
                "generic",
                "fn id<T>(x: T): T = x\n\nlet K = id(42)\n\nfn main(): I32 = K\n",
                "42",
            ),
            // A name with an upper-case first letter is a constructor
            // when a constructor of that name is in scope.
            (
                "constructor_first",
                "data T = K | J\n\nlet K = 40\n\nfn main(): I32 = match K of | K => 1 | J => 2 end\n",
                "1",
            ),
            // A function that uses a constant, as a value.
            (
                "function_value",
                "let K = 40\n\nfn get(): I32 = K\n\nfn main(): I32 = let g = get in g(()) + 2\n",
                "42",
            ),
        ],
    );
}

/// A constant belongs to its module: 2 modules can have a constant of
/// one name, and no module names a constant of another module.
#[test]
fn a_constant_is_private_to_its_module() {
    let tmp = tempfile::tempdir().expect("tempdir");
    std::fs::write(
        tmp.path().join("lib.eph"),
        "module lib\n\nlet K = 40\n\npub fn base(): I32 = K\n",
    )
    .expect("write module");
    each_runs(
        tmp.path(),
        &[],
        &[(
            "app",
            "module app\n\nimport lib\n\nlet K = 2\n\nfn main(): I32 = base() + K\n",
            "42",
        )],
    );
    check_refuses(
        tmp.path(),
        "other",
        "module other\n\nimport lib\n\nfn main(): I32 = K\n",
        "unknown constructor `K`",
    );
}

/// The forms behind the flag `--unstable-core` are behind it in the
/// value of a constant too.
#[test]
fn a_constant_follows_the_flag() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let wide = "let F = fn(x: F64) -> x + 1.5\n\nfn main(): F64 = F(40.5)\n";
    let list = "data IntList = Nil | Cons(I32, IntList)\n\nlet ONE: IntList = Cons(42, Nil)\n\n\
                fn head(l: IntList): I32 = match l of | Nil => 0 | Cons(h, t) => h end\n\n\
                fn main(): I32 = head(ONE)\n";
    each_runs(
        tmp.path(),
        &["--unstable-core"],
        &[("wide", wide, "42"), ("list", list, "42")],
    );
    check_refuses(
        tmp.path(),
        "wide",
        wide,
        "behind the flag `--unstable-core`: a lambda",
    );
    check_refuses(
        tmp.path(),
        "list",
        list,
        "behind the flag `--unstable-core`",
    );
}

#[test]
fn a_constant_that_is_not_valid_is_refused_by_name() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let main = "\n\nfn main(): I32 = 0\n";
    // (name, declarations, error)
    for (name, decls, error) in [
        // A constant sees only the constants before it, and not itself.
        (
            "later",
            "let A = B + 1\n\nlet B = 1",
            "Variable `B` not found in scope",
        ),
        ("itself", "let A = A + 1", "Variable `A` not found in scope"),
        // The value does not have the type of the declaration.
        ("wrong_type", "let K: Bool = 40", "Type mismatch"),
        // The value does not fix the type.
        (
            "type_unknown",
            "data Option(a) = None | Some(a)\n\nlet K = None",
            "The type of the constant `K` is not known from its value",
        ),
        // A string is in a region, and a constant is in no region.
        (
            "string",
            "let S = region r { String.new@r(\"ab\") }",
            "escapes region `r`",
        ),
        // A name is declared 1 time: 2 constants, a constant and a
        // function, and 2 functions (which gave a module that was not
        // valid).
        (
            "2_constants",
            "let K = 40\n\nlet K = 1.5",
            "`K` is declared 2 times in the module",
        ),
        (
            "constant_and_function",
            "let k = 40\n\nfn k(): F64 = 1.5",
            "`k` is declared 2 times in the module",
        ),
        (
            "2_functions",
            "fn f(): I32 = 1\n\nfn f(): I32 = 2",
            "`f` is declared 2 times in the module",
        ),
    ] {
        check_refuses(tmp.path(), name, &format!("{decls}{main}"), error);
    }
}
