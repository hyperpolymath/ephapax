// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Phase I regressions for hyperpolymath/ephapax#43. Cross-module type
// resolution — the final ingredient bridge.eph was waiting on.
//
// The CLI now walks the `import a/b/c` graph from a root .eph file,
// resolving each path against the root's parent directory (`a/b/c.eph`).
// Modules are desugared in topological order with a single shared
// `DataRegistry`, then type-checked against a shared `ModuleRegistry`.
// Public items from imported modules become visible in the importer.

use std::process::Command;

fn ephapax_bin() -> String {
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
fn cross_module_imports_compile_end_to_end() {
    let out = tempfile::NamedTempFile::new().expect("temp file");
    let status = Command::new(ephapax_bin())
        .arg("compile-eph")
        .arg(fixture("multi-module/app.eph"))
        .arg("-o")
        .arg(out.path())
        .arg("--verbose")
        .output()
        .expect("ephapax must run");
    assert!(
        status.status.success(),
        "cross-module compile failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&status.stdout),
        String::from_utf8_lossy(&status.stderr)
    );

    // Verbose mode should mention resolving multiple modules.
    let stdout = String::from_utf8_lossy(&status.stdout);
    assert!(
        stdout.contains("Resolved 2 module(s)"),
        "expected 2-module resolution log, got: {}",
        stdout
    );

    let bytes = std::fs::read(out.path()).expect("output wasm exists");
    assert!(bytes.starts_with(b"\0asm"));
    wasmparser::validate(&bytes).expect("cross-module wasm validates");
}
