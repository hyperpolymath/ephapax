// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell
//
// Locks in that the coprocessor thin-FFI surface `stdlib/Coproc.eph` parses
// and type-checks under the surface parser. It is the first stdlib module
// authored in the parseable v2 grammar (the others are pre-v2 — see
// docs/v2-grammar-and-codegen-gaps-2026-06-16.adoc), so this guards against
// a v2-grammar regression silently breaking the typed coprocessor boundary.
//
// The end-to-end FFI seam test (build the Zig shim, dispatch(_, _, 20, 22)
// == 42 with `-L`) is documented in tools/coproc/README.adoc and run
// manually, since it needs the Zig toolchain.

use std::process::Command;

fn stdlib(name: &str) -> String {
    format!("{}/../../stdlib/{}", env!("CARGO_MANIFEST_DIR"), name)
}

#[test]
fn coproc_eph_typechecks() {
    let out = Command::new(env!("CARGO_BIN_EXE_ephapax"))
        .arg("check")
        .arg(stdlib("Coproc.eph"))
        .output()
        .expect("ephapax must run");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        out.status.success(),
        "stdlib/Coproc.eph must type-check.\nstdout: {stdout}\nstderr: {stderr}"
    );
    assert!(
        stdout.contains("checked successfully"),
        "expected a success line from `ephapax check`; got:\n{stdout}"
    );
}
