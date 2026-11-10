// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
//
// driver_agreement.rs, v2 plan rung E3 gate.
//
// Every tool loads a program through `ephapax-driver`, so every tool must
// give the same verdict on every .eph file in the repo. The reference
// verdict is `ephapax_driver::load_program`; `check`, `compile`, `run`,
// the REPL and the query engine are each compared with it. The LSP is a
// binary crate, so its twin of this test lives in
// src/ephapax-lsp/src/main.rs.

use std::path::{Path, PathBuf};
use std::process::Command;

use ephapax_driver::DriverError;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("repo root")
}

/// All .eph files under the repo, repo-root-relative (same walk as
/// eph_corpus_gate.rs).
fn corpus(root: &Path) -> Vec<String> {
    fn walk(dir: &Path, root: &Path, out: &mut Vec<String>) {
        let Ok(entries) = std::fs::read_dir(dir) else {
            return;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            let name = entry.file_name().to_string_lossy().into_owned();
            if path.is_dir() {
                if !matches!(
                    name.as_str(),
                    "target" | ".git" | ".claude" | "node_modules" | ".zig-cache-global"
                ) {
                    walk(&path, root, out);
                }
            } else if name.ends_with(".eph") {
                let rel = path.strip_prefix(root).expect("under root");
                out.push(rel.to_string_lossy().replace('\\', "/"));
            }
        }
    }
    let mut out = Vec::new();
    walk(root, root, &mut out);
    out.sort();
    out
}

/// The text every CLI command prints for each way a program fails to load.
const LOAD_ERRORS: [&str; 6] = [
    "cannot read",
    "import cycle",
    "Parse error",
    "Desugar error",
    "Type error",
    "Codegen error",
];

fn load_error_text(e: &DriverError) -> &'static str {
    match e {
        DriverError::Io { .. } => LOAD_ERRORS[0],
        DriverError::Cycle { .. } => LOAD_ERRORS[1],
        DriverError::Parse { .. } => LOAD_ERRORS[2],
        DriverError::Desugar { .. } => LOAD_ERRORS[3],
        DriverError::Type { .. } => LOAD_ERRORS[4],
        DriverError::Unsupported { .. } => LOAD_ERRORS[5],
    }
}

#[test]
fn every_entry_point_agrees_on_every_corpus_file() {
    let root = repo_root();
    let tmp = tempfile::tempdir().expect("tempdir");
    let wasm_out = tmp.path().join("agree.wasm");
    let stdlib = ephapax_driver::stdlib_dir(None);
    let mut repl = ephapax_repl::Repl::new().expect("REPL initialises");
    let files = corpus(&root);
    assert!(files.len() > 100, "corpus walk found too few files");

    let mut failures = Vec::new();
    let mut loads = 0;
    for rel in &files {
        let path = root.join(rel);
        let want = ephapax_driver::load_program(&path, stdlib.as_deref())
            .err()
            .map(|e| load_error_text(&e));
        loads += usize::from(want.is_none());

        // check and compile: same exit status, same kind of error.
        let commands: [(&str, Vec<&str>); 3] = [
            ("check", vec!["check", rel]),
            (
                "compile",
                vec![
                    "compile",
                    rel,
                    "-o",
                    wasm_out.to_str().expect("utf8 tmp path"),
                ],
            ),
            ("run", vec!["run", rel]),
        ];
        for (name, args) in commands {
            let out = Command::new(env!("CARGO_BIN_EXE_ephapax"))
                .current_dir(&root)
                .args(&args)
                .output()
                .expect("spawn ephapax");
            let stderr = String::from_utf8_lossy(&out.stderr);
            let agrees = match want {
                Some(text) => !out.status.success() && stderr.contains(text),
                // `run` goes on to execute `main`, which may fail for its
                // own reasons (a host import `run` does not provide); it
                // must not fail to *load*.
                None if name == "run" => !LOAD_ERRORS.iter().any(|t| stderr.contains(t)),
                None => out.status.success(),
            };
            if !agrees {
                failures.push(format!(
                    "{rel}: `{name}` exit {:?}, driver says {want:?}; stderr:\n{stderr}",
                    out.status.code()
                ));
            }
        }

        // REPL `:load`.
        if repl.load_path(&path).is_ok() != want.is_none() {
            failures.push(format!("{rel}: REPL disagrees, driver says {want:?}"));
        }

        // Query engine (the id is the file path, so imports resolve).
        let id = path.to_string_lossy();
        let mut db = ephapax_query::QueryDb::new();
        db.set_source_text(
            &id,
            std::fs::read_to_string(&path).expect("read corpus file"),
        );
        if (db.parsed(&id).is_ok() && db.typed(&id).is_ok()) != want.is_none() {
            failures.push(format!(
                "{rel}: query engine disagrees, driver says {want:?}"
            ));
        }
    }

    println!("driver agreement: {} files, {} load", files.len(), loads);
    assert!(loads > 0, "no corpus file loads: gate misconfigured");
    assert!(
        failures.is_empty(),
        "entry points disagree with ephapax-driver:\n{}",
        failures.join("\n")
    );
}

/// An integer literal outside the I64 range used to become 0 without a
/// diagnostic. It is now `ParseError::IntegerOutOfRange` on every command,
/// and `-9223372036854775808` is one literal, `i64::MIN`.
#[test]
fn out_of_range_integer_literal_is_a_parse_error() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let run = |body: &str, args: &[&str]| {
        std::fs::write(
            tmp.path().join("lit.eph"),
            format!("module lit\n\nfn main(): I64 = {body}\n"),
        )
        .expect("write program");
        Command::new(env!("CARGO_BIN_EXE_ephapax"))
            .current_dir(tmp.path())
            .args(args)
            .output()
            .expect("spawn ephapax")
    };
    let commands: [&[&str]; 4] = [
        &["check", "lit.eph"],
        &["compile", "lit.eph"],
        &["run", "lit.eph"],
        &["run", "--interp", "lit.eph"],
    ];

    // (program text, the literal the error names)
    for (body, literal) in [
        ("9223372036854775808", "9223372036854775808"),
        ("-9223372036854775809", "-9223372036854775809"),
        ("-(9223372036854775808)", "9223372036854775808"),
    ] {
        for args in commands {
            let out = run(body, args);
            let stderr = String::from_utf8_lossy(&out.stderr);
            assert!(
                !out.status.success()
                    && stderr.contains(&format!("Integer literal `{literal}` is out of range")),
                "`{body}` under {args:?}: exit {:?}, stderr:\n{stderr}",
                out.status.code()
            );
        }
    }

    // Both ends of the range are literals, on both execution paths.
    for (body, want) in [
        ("9223372036854775807", "9223372036854775807i64"),
        ("-9223372036854775808", "-9223372036854775808i64"),
    ] {
        for args in [&commands[2], &commands[3]] {
            let out = run(body, args);
            assert_eq!(
                String::from_utf8_lossy(&out.stdout).trim(),
                want,
                "`{body}` under {args:?}"
            );
        }
    }
}

/// A limit of the typed lowering is a load error too: `check` must not
/// accept a program that `compile` refuses. Not lowered yet: a lambda
/// with a parameter or result that is not 32 bits wide.
#[test]
fn check_rejects_what_typed_codegen_cannot_lower() {
    let tmp = tempfile::tempdir().expect("tempdir");
    // (result type, body, text the error names)
    for (ty, body, what) in [
        (
            "F32",
            "let f = fn(x: F32) -> x + 1.0f32\n  f(2.0f32)",
            "lambda",
        ),
        ("F64", "let f = fn(x: I32) -> 1.5\n  f(1)", "lambda"),
    ] {
        std::fs::write(
            tmp.path().join("wide.eph"),
            format!("module wide\n\nfn main(): {ty} =\n  {body}\n"),
        )
        .expect("write program");
        for args in [&["check", "wide.eph"][..], &["compile", "wide.eph"]] {
            let out = Command::new(env!("CARGO_BIN_EXE_ephapax"))
                .current_dir(tmp.path())
                .args(args)
                .output()
                .expect("spawn ephapax");
            let stderr = String::from_utf8_lossy(&out.stderr);
            assert!(
                !out.status.success() && stderr.contains("Codegen error") && stderr.contains(what),
                "`{body}` under {args:?}: exit {:?}, stderr:\n{stderr}",
                out.status.code()
            );
        }
    }
}

/// The query engine reads a program's imports from disk, and an imported
/// file is not one of its inputs. A program with imports is therefore
/// never served from the parse memo: an edit to the imported file shows.
#[test]
fn query_engine_sees_an_edit_to_an_imported_file() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let lib = tmp.path().join("lib.eph");
    let app = tmp.path().join("app.eph");
    std::fs::write(&lib, "module lib\n\npub fn inc(n: I32): I32 = n + 1\n").expect("write lib");
    let app_text = "module app\n\nimport lib\n\nfn main(): I32 = inc(41)\n";
    std::fs::write(&app, app_text).expect("write app");

    let id = app.to_string_lossy();
    let mut db = ephapax_query::QueryDb::new();
    db.set_source_text(&id, app_text);
    assert!(db.typed(&id).is_ok(), "the program checks");

    // The root text is unchanged; only the imported file changes.
    std::fs::write(&lib, "module lib\n\npub fn inc(n: Bool): Bool = n\n").expect("rewrite lib");
    assert!(db.typed(&id).is_err(), "the stale memo was served");
}

/// `wasm` loads a program with imports one time for each demand, so the
/// program it compiles is the program it checked. It used to load it two
/// times, and an imported file could change between the two loads.
#[test]
fn query_engine_compiles_the_program_that_it_checked() {
    let tmp = tempfile::tempdir().expect("tempdir");
    std::fs::write(
        tmp.path().join("lib.eph"),
        "module lib\n\npub fn inc(n: I32): I32 = n + 1\n",
    )
    .expect("write lib");
    let app = tmp.path().join("app.eph");
    let app_text = "module app\n\nimport lib\n\nfn main(): I32 = inc(41)\n";
    std::fs::write(&app, app_text).expect("write app");

    let id = app.to_string_lossy();
    let mut db = ephapax_query::QueryDb::new();
    db.set_source_text(&id, app_text);
    assert!(db.wasm(&id).is_ok(), "the program compiles");
    let n = db.recompute_count();
    assert!(db.wasm(&id).is_ok());
    assert_eq!(db.recompute_count(), n + 1, "one load, and no other work");
}
