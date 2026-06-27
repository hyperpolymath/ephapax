// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// Phase K — G6: qualified module-member access (`M.member`).
//
// Phase I (#43) made an imported module's public items visible
// *unqualified*. G6 adds the qualified *syntax* `M.member`, where `M` is
// the last segment of an imported module's path, desugaring to that same
// unqualified member (a constructor for an upper-case member, a function /
// value otherwise). Before this, any named member access errored at the
// parser with "Named field access not yet supported".

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

/// `app.eph` uses `lib.inc` (qualified function), `lib.On` (qualified
/// constructor), and `inc` (unqualified, phase I) — all resolving to the
/// imported module `lib`. End-to-end compile must succeed.
#[test]
fn qualified_module_member_access_compiles_end_to_end() {
    let out = tempfile::NamedTempFile::new().expect("temp file");
    let output = Command::new(ephapax_bin())
        .arg("compile-eph")
        .arg(fixture("qualified-import/app.eph"))
        .arg("-o")
        .arg(out.path())
        .output()
        .expect("ephapax must run");
    assert!(
        output.status.success(),
        "qualified-access compile failed:\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

/// A qualifier that names no imported module is a clean desugar error, not
/// a panic or a silent miscompile.
#[test]
fn unknown_qualifier_is_a_clean_error() {
    let dir = tempfile::tempdir().expect("temp dir");
    let app = dir.path().join("app.eph");
    std::fs::write(&app, "module app\nimport lib\nfn t(): I32 = nope.inc(1)\n")
        .expect("write app");
    std::fs::write(dir.path().join("lib.eph"), "module lib\npub fn inc(n: I32): I32 = n + 1\n")
        .expect("write lib");
    let out = tempfile::NamedTempFile::new().expect("temp file");
    let output = Command::new(ephapax_bin())
        .arg("compile-eph")
        .arg(&app)
        .arg("-o")
        .arg(out.path())
        .output()
        .expect("ephapax must run");
    assert!(!output.status.success(), "unknown qualifier must fail to compile");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("not an imported module"),
        "expected an 'unknown module' desugar error, got:\n{stderr}"
    );
}
