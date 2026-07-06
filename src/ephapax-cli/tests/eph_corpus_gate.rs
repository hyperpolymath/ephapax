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
// It also enforces the negative corpus: conformance/invalid/*.eph must
// NOT compile.
//
// The known-debt count is printed on every run — no silent caps.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

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
        .args([
            "compile",
            rel,
            "-o",
            out.to_str().expect("utf8 tmp path"),
        ])
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
    let wrongly_accepted: Vec<_> = invalid
        .iter()
        .filter(|rel| compiles(&root, rel, tmp.path()))
        .collect();
    assert!(
        wrongly_accepted.is_empty(),
        "negative-corpus files were ACCEPTED by the compiler: {wrongly_accepted:?}"
    );
}
