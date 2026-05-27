// SPDX-License-Identifier: PMPL-1.0-or-later
//
// End-to-end test for `ephapax compile --verify-ownership` (C7).
//
// Spawns the built `ephapax` binary, asks it to compile a small
// program, and asserts the verifier runs and reports clean output.
// The negative path (verifier catching codegen bugs) is unit-tested
// in `typed-wasm-verify`; this test exists to prove the CLI plumbing
// works — flag parsing → post-compile verification call → exit code
// → user-facing output.
//
// The two positive-assertion tests are gated by the
// `typed-wasm-verify` feature: with the feature OFF, the CLI prints a
// warning and skips verification, so the "verification: clean" line
// the tests look for is absent (by design). The third test —
// `compile_without_verify_flag_does_not_run_verifier` — works
// regardless because it asserts an *absence* of verifier output.

use std::process::Command;

fn ephapax_bin() -> String {
    env!("CARGO_BIN_EXE_ephapax").to_string()
}

#[cfg(feature = "typed-wasm-verify")]
#[test]
fn verify_ownership_clean_module() {
    let src = tempfile::NamedTempFile::with_suffix(".eph").expect("tempfile");
    std::fs::write(src.path(), "fn add(a: I32, b: I32): I32 = a + b\n")
        .expect("write source");
    let out = tempfile::NamedTempFile::new().expect("output tempfile");

    let result = Command::new(ephapax_bin())
        .arg("compile")
        .arg(src.path())
        .arg("-o")
        .arg(out.path())
        .arg("--verify-ownership")
        .arg("--verbose")
        .output()
        .expect("ephapax must run");

    assert!(
        result.status.success(),
        "expected exit 0, got status: {:?}\nstdout: {}\nstderr: {}",
        result.status,
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );

    let stdout = String::from_utf8_lossy(&result.stdout);
    assert!(
        stdout.contains("typed-wasm L7+L10 verification: clean"),
        "expected verifier-clean line in stdout:\n{}",
        stdout
    );
}

#[cfg(feature = "typed-wasm-verify")]
#[test]
fn verify_ownership_linear_program() {
    // A program that takes a linear String param and consumes it
    // exactly once should verify clean. This exercises the
    // ownership-section-emission path from C6 plus the verifier
    // wiring from C7.
    let src = tempfile::NamedTempFile::with_suffix(".eph").expect("tempfile");
    // `s` is Linear (String); returning it consumes it exactly once,
    // satisfying the source-level linear typechecker. The emitted wasm
    // therefore has param_kinds = [Linear] in the ownership section
    // and a body that uses local 0 exactly once.
    std::fs::write(src.path(), "fn echo(s: String): String = s\n")
        .expect("write source");
    let out = tempfile::NamedTempFile::new().expect("output tempfile");

    let result = Command::new(ephapax_bin())
        .arg("compile")
        .arg(src.path())
        .arg("-o")
        .arg(out.path())
        .arg("--verify-ownership")
        .arg("--verbose")
        .output()
        .expect("ephapax must run");

    assert!(
        result.status.success(),
        "expected exit 0, got status: {:?}\nstdout: {}\nstderr: {}",
        result.status,
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );

    let stdout = String::from_utf8_lossy(&result.stdout);
    assert!(
        stdout.contains("typed-wasm L7+L10 verification: clean"),
        "expected verifier-clean line in stdout for linear program:\n{}",
        stdout
    );
}

#[test]
fn compile_without_verify_flag_does_not_run_verifier() {
    // Without --verify-ownership, the verifier line should not appear
    // in verbose output (and the build should not fail even if the
    // emitted module would hypothetically have issues — the verifier
    // isn't invoked).
    let src = tempfile::NamedTempFile::with_suffix(".eph").expect("tempfile");
    std::fs::write(src.path(), "fn add(a: I32, b: I32): I32 = a + b\n")
        .expect("write source");
    let out = tempfile::NamedTempFile::new().expect("output tempfile");

    let result = Command::new(ephapax_bin())
        .arg("compile")
        .arg(src.path())
        .arg("-o")
        .arg(out.path())
        .arg("--verbose")
        .output()
        .expect("ephapax must run");

    assert!(result.status.success(), "expected exit 0");

    let stdout = String::from_utf8_lossy(&result.stdout);
    assert!(
        !stdout.contains("typed-wasm L7+L10 verification"),
        "verifier should not run without --verify-ownership flag; stdout: {}",
        stdout
    );
}
