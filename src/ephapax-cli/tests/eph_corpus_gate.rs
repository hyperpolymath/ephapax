// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// eph_corpus_gate.rs — the whole-repo .eph corpus ratchet gate.
//
// Ground truth 2026-07-07: of the 119 .eph files in the repo, only 13
// compile through the real pipeline (`ephapax compile`). The rest are
// v1-era or speculative syntax (braces-form fn bodies, `&T` borrows,
// ADT `type X = A | B` declarations) awaiting v2 grammar phases. Nothing
// gated any of this, so the corpus rotted silently.
//
// This gate enforces the current truth in BOTH directions:
//   - every file in tests/eph-corpus-compiles.txt must compile
//     (regression gate), and
//   - every repo .eph that compiles must be in the list
//     (ratchet: a newly-supported file must be flipped deliberately,
//     in the same PR as the feature that enabled it).
//
// It also enforces the negative corpus: each conformance/invalid/*.eph must
// parse and desugar, and then be rejected by the type checker with the
// specific error it documents (a ParseError no longer satisfies it).
//
// The known-debt count is printed on every run — no silent caps.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

use ephapax_desugar::desugar;
use ephapax_parser::parse_surface_module;
use ephapax_typing::{type_check_module, TypeError};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repo root")
}

fn ephapax_bin() -> String {
    env!("CARGO_BIN_EXE_ephapax").to_string()
}

/// All .eph files under the repo, repo-root-relative with '/' separators,
/// excluding build/VCS/agent-scratch directories.
fn corpus(root: &Path) -> BTreeSet<String> {
    fn walk(dir: &Path, root: &Path, out: &mut BTreeSet<String>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let name = entry.file_name();
            let name = name.to_string_lossy();
            if path.is_dir() {
                if matches!(
                    name.as_ref(),
                    "target" | ".git" | ".claude" | "node_modules" | ".zig-cache-global"
                ) {
                    continue;
                }
                walk(&path, root, out);
            } else if name.ends_with(".eph") {
                let rel = path
                    .strip_prefix(root)
                    .expect("under root")
                    .to_string_lossy()
                    .replace('\\', "/");
                out.insert(rel);
            }
        }
    }
    let mut out = BTreeSet::new();
    walk(root, root, &mut out);
    out
}

fn compiles(root: &Path, rel: &str, out_dir: &Path) -> bool {
    let out = out_dir.join("gate.wasm");
    Command::new(ephapax_bin())
        .current_dir(root)
        .args(["compile", rel, "-o", out.to_str().expect("utf8 tmp path")])
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

fn allowlist(root: &Path) -> BTreeSet<String> {
    let text = std::fs::read_to_string(root.join("tests/eph-corpus-compiles.txt"))
        .expect("read tests/eph-corpus-compiles.txt");
    text.lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(str::to_string)
        .collect()
}

#[test]
fn eph_corpus_ratchet() {
    let root = repo_root();
    let tmp = tempfile::tempdir().expect("tempdir");
    let expected = allowlist(&root);
    let all = corpus(&root);

    for listed in &expected {
        assert!(
            all.contains(listed),
            "allowlist entry does not exist on disk: {listed}"
        );
    }

    let mut passing = BTreeSet::new();
    for rel in &all {
        if compiles(&root, rel, tmp.path()) {
            passing.insert(rel.clone());
        }
    }

    let regressions: Vec<_> = expected.difference(&passing).collect();
    let unexpected: Vec<_> = passing.difference(&expected).collect();
    let debt = all.len() - passing.len();
    println!(
        "eph corpus: {} files, {} compile, {} known debt (v1->v2 migration backlog)",
        all.len(),
        passing.len(),
        debt
    );

    assert!(
        regressions.is_empty(),
        "REGRESSION — allowlisted files no longer compile: {regressions:?}"
    );
    assert!(
        unexpected.is_empty(),
        "RATCHET — newly compiling files must be added to \
         tests/eph-corpus-compiles.txt in the enabling PR: {unexpected:?}"
    );
}

/// A human description of the expected error and a predicate for it.
type Expectation = (&'static str, fn(&TypeError) -> bool);

/// The error each negative-corpus file must be rejected with: the
/// discipline violation its name documents (conformance/README.adoc,
/// E001–E005). Every file in conformance/invalid/ needs an entry here.
fn invalid_expectation(rel: &str) -> Option<Expectation> {
    use TypeError as E;
    let entry: Expectation = match rel {
        "conformance/invalid/branch_inconsistent.eph" => (
            "E005 BranchLinearityMismatchDetailed { var: x, .. }",
            |e| matches!(e, E::BranchLinearityMismatchDetailed { var, .. } if var == "x"),
        ),
        "conformance/invalid/linear_not_consumed.eph" => (
            "E001 LinearVariableNotConsumed(x)",
            |e| matches!(e, E::LinearVariableNotConsumed(v) if v == "x"),
        ),
        "conformance/invalid/linear_used_twice.eph" => (
            "E002 LinearVariableReused(x)",
            |e| matches!(e, E::LinearVariableReused(v) if v == "x"),
        ),
        "conformance/invalid/region_escape.eph" => (
            "E003 RegionEscape { region: r, .. }",
            |e| matches!(e, E::RegionEscape { region, .. } if region == "r"),
        ),
        // The `let!` scope closes before the region does, so the checker
        // reports the leak there; the region-exit form is accepted too.
        "conformance/invalid/region_linear_not_consumed.eph" => (
            "E004 LinearVariableNotConsumed(conn) or RegionLinearNotConsumed { var: conn, .. }",
            |e| {
                matches!(e, E::LinearVariableNotConsumed(v) if v == "conn")
                    || matches!(e, E::RegionLinearNotConsumed { var, .. } if var == "conn")
            },
        ),
        _ => return None,
    };
    Some(entry)
}

/// The negative corpus must be rejected by the TYPE CHECKER, with the
/// specific error each file documents. A file that fails to parse (or
/// to desugar) does not satisfy this gate: it would stay "invalid" for
/// the wrong reason and stop testing the discipline it names.
#[test]
fn invalid_corpus_stays_invalid() {
    let root = repo_root();
    let tmp = tempfile::tempdir().expect("tempdir");
    let invalid: Vec<_> = corpus(&root)
        .into_iter()
        .filter(|p| p.starts_with("conformance/invalid/"))
        .collect();
    assert!(
        !invalid.is_empty(),
        "conformance/invalid corpus missing — gate misconfigured"
    );

    let mut failures = Vec::new();
    for rel in &invalid {
        let Some((want, matches_expected)) = invalid_expectation(rel) else {
            failures.push(format!(
                "{rel}: no expected error recorded in invalid_expectation()"
            ));
            continue;
        };
        let src = std::fs::read_to_string(root.join(rel)).expect("read negative-corpus file");

        // Library pipeline: it must parse (surface grammar, no legacy
        // core-parser fallback) and desugar, and the type checker must
        // reject it with the documented error.
        let surface = match parse_surface_module(&src, rel) {
            Ok(m) => m,
            Err(e) => {
                failures.push(format!("{rel}: ParseError, want {want}: {e:?}"));
                continue;
            }
        };
        let core = match desugar(&surface) {
            Ok(m) => m,
            Err(e) => {
                failures.push(format!("{rel}: DesugarError, want {want}: {e}"));
                continue;
            }
        };
        let err = match type_check_module(&core) {
            Ok(()) => {
                failures.push(format!("{rel}: ACCEPTED by the type checker, want {want}"));
                continue;
            }
            Err(e) => e.error,
        };
        if !matches_expected(&err) {
            failures.push(format!("{rel}: rejected with {err:?}, want {want}"));
            continue;
        }

        // CLI: `ephapax compile` must fail normally (exit 1) and report
        // this same type error, not some other failure.
        let out = Command::new(ephapax_bin())
            .current_dir(&root)
            .args([
                "compile",
                rel,
                "-o",
                tmp.path()
                    .join("gate.wasm")
                    .to_str()
                    .expect("utf8 tmp path"),
            ])
            .output()
            .expect("run ephapax compile");
        let stderr = String::from_utf8_lossy(&out.stderr);
        let want_text = format!("{err:?}");
        if out.status.code() != Some(1)
            || !stderr.contains("Type error")
            || !stderr.contains(&want_text)
        {
            failures.push(format!(
                "{rel}: `ephapax compile` exit {:?}, want exit 1 with \"Type error\" and \
                 {want_text}; stderr:\n{stderr}",
                out.status.code()
            ));
        }
    }

    for name in [
        "branch_inconsistent",
        "linear_not_consumed",
        "linear_used_twice",
        "region_escape",
        "region_linear_not_consumed",
    ] {
        let rel = format!("conformance/invalid/{name}.eph");
        if !invalid.contains(&rel) {
            failures.push(format!("{rel}: expected negative-corpus file is missing"));
        }
    }

    assert!(
        failures.is_empty(),
        "negative corpus not rejected for the documented reason:\n{}",
        failures.join("\n")
    );
}
