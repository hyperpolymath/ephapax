// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Stdlib import resolution — `import Argv` from a program that is NOT a
// sibling of stdlib/Argv.eph.
//
// Resolution order (import_resolver::load_program):
//   1. literal path / module-declaration index under the program's dir,
//   2. module-declaration index under the stdlib dir
//      (--stdlib flag > $EPHAPAX_STDLIB > repo stdlib/ for dev builds).
// Local files shadow stdlib modules of the same name (tier order).

use std::path::{Path, PathBuf};
use std::process::Command;

fn ephapax_bin() -> String {
    env!("CARGO_BIN_EXE_ephapax").to_string()
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repo root")
}

fn fixture() -> PathBuf {
    repo_root().join("tests/v2-grammar/fixtures/stdlib-import/app.eph")
}

/// The fixture compiles via the dev-default stdlib path (repo stdlib/).
#[test]
fn stdlib_import_compiles_via_default_path() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let out = tmp.path().join("app.wasm");
    let output = Command::new(ephapax_bin())
        .args(["compile"])
        .arg(fixture())
        .arg("-o")
        .arg(&out)
        .output()
        .expect("spawn ephapax");
    assert!(
        output.status.success(),
        "compile failed:\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let wasm = std::fs::read(&out).expect("read wasm");
    wasmparser::validate(&wasm).expect("emitted wasm failed validation");
}

/// The program works from a directory with NO sibling Argv.eph — the
/// point of the search path. Copy it to a tempdir and compile there.
#[test]
fn stdlib_import_compiles_from_unrelated_directory() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let src = tmp.path().join("app.eph");
    std::fs::copy(fixture(), &src).expect("copy fixture");
    let out = tmp.path().join("app.wasm");
    let output = Command::new(ephapax_bin())
        .args(["compile"])
        .arg(&src)
        .arg("-o")
        .arg(&out)
        .arg("--stdlib")
        .arg(repo_root().join("stdlib"))
        .output()
        .expect("spawn ephapax");
    assert!(
        output.status.success(),
        "compile failed:\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// An empty --stdlib dir means the import cannot resolve: the search
/// path must not silently fall back past an explicit flag.
#[test]
fn explicit_stdlib_flag_is_authoritative() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let empty = tmp.path().join("empty-stdlib");
    std::fs::create_dir(&empty).expect("mkdir");
    let src = tmp.path().join("app.eph");
    std::fs::copy(fixture(), &src).expect("copy fixture");
    let out = tmp.path().join("app.wasm");
    let output = Command::new(ephapax_bin())
        .args(["compile"])
        .arg(&src)
        .arg("-o")
        .arg(&out)
        .arg("--stdlib")
        .arg(&empty)
        .output()
        .expect("spawn ephapax");
    assert!(
        !output.status.success(),
        "compile unexpectedly succeeded with an empty --stdlib dir"
    );
}
