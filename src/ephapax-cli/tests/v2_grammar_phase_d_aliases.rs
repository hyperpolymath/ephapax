// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Phase D: clap aliases for the `compile` subcommand. Closes #36.
// Asserts that invoking the CLI as `compile-eph` and `compile-affine`
// both route to the same `Compile` subcommand. Probed by hypatia's
// `build-gossamer-gui.yml` workflow (see #36 for the probe order).

use std::process::Command;

fn ephapax_bin() -> String {
    // CARGO_BIN_EXE_ephapax is set by cargo for integration tests.
    env!("CARGO_BIN_EXE_ephapax").to_string()
}

fn fixture(name: &str) -> String {
    format!(
        "{}/../../tests/v2-grammar/fixtures/{}",
        env!("CARGO_MANIFEST_DIR"),
        name
    )
}

#[test]
fn compile_eph_alias_routes_to_compile() {
    let out = tempfile::NamedTempFile::new().expect("temp file");
    let status = Command::new(ephapax_bin())
        .arg("compile-eph")
        .arg(fixture("extern-callsite.eph"))
        .arg("-o")
        .arg(out.path())
        .output()
        .expect("ephapax compile-eph must run");
    assert!(
        status.status.success(),
        "compile-eph alias failed: stdout={} stderr={}",
        String::from_utf8_lossy(&status.stdout),
        String::from_utf8_lossy(&status.stderr)
    );
    let bytes = std::fs::read(out.path()).expect("output wasm exists");
    assert!(bytes.starts_with(b"\0asm"), "wasm magic bytes present");
}

#[test]
fn compile_affine_alias_routes_to_compile() {
    let out = tempfile::NamedTempFile::new().expect("temp file");
    let status = Command::new(ephapax_bin())
        .arg("compile-affine")
        .arg(fixture("extern-callsite.eph"))
        .arg("-o")
        .arg(out.path())
        .output()
        .expect("ephapax compile-affine must run");
    assert!(
        status.status.success(),
        "compile-affine alias failed: stdout={} stderr={}",
        String::from_utf8_lossy(&status.stdout),
        String::from_utf8_lossy(&status.stderr)
    );
    let bytes = std::fs::read(out.path()).expect("output wasm exists");
    assert!(bytes.starts_with(b"\0asm"), "wasm magic bytes present");
}
