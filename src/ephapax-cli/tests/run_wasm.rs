// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// run_wasm.rs, v2 plan rung E4 gate.
//
// `ephapax run` compiles the program and executes the wasm (wasmtime,
// in-process), forwarding its trailing arguments through the host imports
// `stdlib/Argv.eph` declares. The interpreter is `run --interp`; it is
// incomplete, and tests/interp-known-failures.txt lists the compiling
// corpus files on which it disagrees with the wasm path.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repo root")
}

fn ephapax(dir: &Path, args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_ephapax"))
        .current_dir(dir)
        .args(args)
        .output()
        .expect("spawn ephapax")
}

/// stdout of a successful `ephapax <args>`, trimmed.
fn stdout_of(dir: &Path, args: &[&str]) -> String {
    let out = ephapax(dir, args);
    assert!(
        out.status.success(),
        "ephapax {args:?} failed:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).trim().to_string()
}

/// Paths (one per line, `#` comments) in a repo-root-relative list file.
fn list(root: &Path, file: &str) -> BTreeSet<String> {
    std::fs::read_to_string(root.join(file))
        .unwrap_or_else(|e| panic!("read {file}: {e}"))
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(str::to_string)
        .collect()
}

/// Probe p1 (data/match, recursion, `let!`): 40 + 2 + 120.
#[test]
fn run_executes_the_compiled_wasm() {
    let tmp = tempfile::tempdir().expect("tempdir");
    std::fs::copy(
        repo_root().join("tests/probes/p1.eph.txt"),
        tmp.path().join("p1.eph"),
    )
    .expect("stage p1");
    assert_eq!(stdout_of(tmp.path(), &["run", "p1.eph"]), "162");
    // A bare file argument runs it the same way.
    assert_eq!(stdout_of(tmp.path(), &["p1.eph"]), "162");
}

/// An .eph program cannot yet read bytes out of a raw buffer, so it
/// reports the argument count and byte lengths; the bytes `argv_arg_get`
/// copies are checked host-side (src/runner.rs).
#[test]
fn run_forwards_arguments_through_argv() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let write = |name: &str, body: &str| {
        let src = format!("module {name}\n\nimport Argv\n\nfn main(): I32 = {body}\n");
        std::fs::write(tmp.path().join(format!("{name}.eph")), src).expect("write program");
    };
    // 1000 * argc + byte length of argv[1] (-1 when there is none).
    write(
        "count_len",
        "Argv.argv_count() * 1000 + Argv.argv_arg_len(1)",
    );
    write("arg0_len", "Argv.argv_arg_len(0)");
    write("last_len", "Argv.argv_arg_len(Argv.argv_count() - 1)");

    let run = |args: &[&str]| stdout_of(tmp.path(), args);
    // No arguments: argv is just the program path, so argc is 1.
    assert_eq!(run(&["run", "count_len.eph"]), "999");
    assert_eq!(run(&["run", "count_len.eph", "hello"]), "2005");
    assert_eq!(run(&["run", "count_len.eph", "ab", "c", "héllo"]), "4002");
    // argv[0] is the program path as given.
    assert_eq!(
        run(&["run", "arg0_len.eph", "x"]),
        "arg0_len.eph".len().to_string()
    );
    // Byte length, not character count: "héllo" is 6 bytes of UTF-8.
    assert_eq!(run(&["run", "last_len.eph", "ab", "c", "héllo"]), "6");
}

/// `run` and `run --interp` must give the same result on every compiling
/// corpus file, except the listed known failures. The list is a ratchet:
/// an entry that starts to agree must be removed.
#[test]
fn interpreter_and_wasm_agree_except_known_failures() {
    let root = repo_root();
    let known = list(&root, "tests/interp-known-failures.txt");
    let mut disagree = BTreeSet::new();
    for rel in list(&root, "tests/eph-corpus-compiles.txt") {
        let wasm = ephapax(&root, &["run", &rel]);
        let interp = ephapax(&root, &["run", "--interp", &rel]);
        if (wasm.status.success(), &wasm.stdout) != (interp.status.success(), &interp.stdout) {
            disagree.insert(rel);
        }
    }
    assert_eq!(
        disagree, known,
        "interpreter/wasm disagreements differ from tests/interp-known-failures.txt"
    );
}

/// A selective import (`import lib(inc)`) compiles and runs. Codegen
/// type-checks the merged module on its own; the import used to be kept
/// there and did not resolve.
#[test]
fn selective_import_runs() {
    let tmp = tempfile::tempdir().expect("tempdir");
    std::fs::write(
        tmp.path().join("lib.eph"),
        "module lib\n\npub fn inc(n: I32): I32 = n + 1\n",
    )
    .expect("write lib");
    std::fs::write(
        tmp.path().join("app.eph"),
        "module app\n\nimport lib(inc)\n\nfn main(): I32 = inc(41)\n",
    )
    .expect("write app");
    assert_eq!(stdout_of(tmp.path(), &["run", "app.eph"]), "42");
}

/// The entry point is the `main` of the module that was asked for. A
/// `main` in an imported module is not run.
#[test]
fn run_does_not_execute_the_main_of_an_imported_module() {
    let tmp = tempfile::tempdir().expect("tempdir");
    std::fs::write(
        tmp.path().join("lib.eph"),
        "module lib\n\npub fn inc(n: I32): I32 = n + 1\n\nfn main(): I32 = 99\n",
    )
    .expect("write lib");
    std::fs::write(
        tmp.path().join("app.eph"),
        "module app\n\nimport lib\n\nfn twice(n: I32): I32 = inc(inc(n))\n",
    )
    .expect("write app");
    for args in [&["run", "app.eph"][..], &["run", "--interp", "app.eph"]] {
        assert_eq!(stdout_of(tmp.path(), args), "", "{args:?}");
    }
}
