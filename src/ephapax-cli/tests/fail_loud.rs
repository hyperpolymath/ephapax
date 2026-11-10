// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! fail_loud.rs — the gate for rung E1 ("Fail loudly") of the v2 plan
//! (`docs/reports/2026-11-04-v2-survey/EPHAPAX-V2-ARCHITECTURE-AND-PLAN.adoc`).
//!
//! Before E1 each of these was accepted and silently ignored or
//! miscompiled: `perform`/`handle` compiled to an `unreachable` trap, raw
//! `__ffi` called an import index outside the import section (probe g5),
//! `@total`/`@pure`/`@comptime` were dropped by the parser, and `-O`,
//! `--debug` and `--mode` were accepted with no effect. Each one must now
//! either take effect or be rejected with a named error.
//!
//! `compile_match` still emits an `unreachable` fallback after its arms;
//! that is legitimate (the type checker proves it dead), so this gate does
//! not ban `unreachable` globally.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use ephapax_desugar::desugar;
use ephapax_parser::{parse_module, parse_surface_module, ParseError};
use ephapax_syntax::{Decl, Expr, ExprKind, Literal, Module, Ty, Visibility};
use ephapax_typing::{type_check_module, TypeError};
use ephapax_wasm::{compile_module, Codegen, UNSUPPORTED_PREFIX};
use wasmparser::{Operator, Parser, Payload, TypeRef};

const PERFORM: &str =
    include_str!("../../../docs/reports/2026-11-04-v2-survey/evidence/probes/perform.eph.txt");
const G5: &str =
    include_str!("../../../docs/reports/2026-11-04-v2-survey/evidence/probes/g5.eph.txt");

const PERFORM_ONLY: &str = "fn main(): I32 = perform ask()\n";

const HANDLE_ONLY: &str = "\
fn main(): I32 =
  handle 1 with
  | return(x) => x
  end
";

/// Probe g5 rewritten with a typed `extern` declaration (plus a second
/// import, so contiguity is tested across more than one extern fn).
const G5_EXTERN: &str = "\
extern \"env\" {
  fn foo(x: I32): I64
  fn bar(): I32
}
fn t(): I64 = foo(bar())
fn main(): I32 = 0
";

/// The `@total` loop: `spin` never terminates.
const TOTAL_LOOP: &str = "\
@total
fn spin(n: I32): I32 = spin(n)
fn main(): I32 = 0
";

/// An `@pure` function that calls an effectful extern.
const PURE_WITH_EFFECT: &str = "\
extern \"env\" {
  fn log(x: I32): I32
}
@pure
fn f(x: I32): I32 = log(x)
fn main(): I32 = f(1)
";

const COMPTIME: &str = "\
@comptime
fn k(): I32 = 42
fn main(): I32 = k()
";

const PLAIN: &str = "fn main(): I32 = 1 + 2\n";

fn ephapax(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_ephapax"))
        .args(args)
        .output()
        .expect("run ephapax")
}

fn write(dir: &Path, name: &str, src: &str) -> PathBuf {
    let p = dir.join(name);
    std::fs::write(&p, src).expect("write source");
    p
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).to_string()
}

/// Surface parse → desugar → type check (must succeed), falling back to
/// the core parser when the surface parser rejects the file, as
/// `ephapax check` does (the surface parser has no effect syntax).
fn checked_core(src: &str) -> Module {
    let core = match parse_surface_module(src, "probe") {
        Ok(surface) => desugar(&surface).expect("desugar"),
        Err(_) => parse_module(src, "probe").expect("core parse"),
    };
    type_check_module(&core).expect("type check");
    core
}

/// `ephapax compile` must fail with exit 1 and must not write a module.
fn assert_compile_rejected(name: &str, src: &str, needle: &str) {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = write(dir.path(), &format!("{name}.eph"), src);
    let wasm = dir.path().join(format!("{name}.wasm"));
    let out = ephapax(&[
        "compile",
        path.to_str().unwrap(),
        "-o",
        wasm.to_str().unwrap(),
    ]);
    let err = stderr(&out);
    assert_eq!(out.status.code(), Some(1), "{name}: exit\n{err}");
    assert!(
        err.contains(needle),
        "{name}: expected `{needle}` in\n{err}"
    );
    assert!(!wasm.exists(), "{name}: no module may be written");
}

// ---------------------------------------------------------------------------
// perform / handle
// ---------------------------------------------------------------------------

fn assert_codegen_unsupported(src: &str, what: &str) {
    let core = checked_core(src);
    let err = compile_module(&core).expect_err("codegen must refuse");
    assert!(
        err.0.starts_with(UNSUPPORTED_PREFIX) && err.0.contains(what),
        "unexpected CodegenError: {}",
        err.0
    );
}

#[test]
fn perform_probe_is_a_codegen_error_without_a_module() {
    assert_codegen_unsupported(PERFORM, "handle");
    assert_compile_rejected("perform", PERFORM, UNSUPPORTED_PREFIX);
}

#[test]
fn perform_alone_is_a_codegen_error() {
    assert_codegen_unsupported(PERFORM_ONLY, "perform ask");
    assert_compile_rejected("perform_only", PERFORM_ONLY, "perform ask");
}

#[test]
fn handle_alone_is_a_codegen_error() {
    assert_codegen_unsupported(HANDLE_ONLY, "handle");
    assert_compile_rejected("handle_only", HANDLE_ONLY, "handle");
}

#[test]
fn compile_program_refuses_perform() {
    let expr = Expr::dummy(ExprKind::Perform {
        op: "ask".into(),
        args: vec![],
    });
    let err = Codegen::new()
        .compile_program(&expr)
        .expect_err("compile_program must refuse perform");
    assert!(err.0.starts_with(UNSUPPORTED_PREFIX), "{}", err.0);
}

#[test]
fn check_rejects_what_compile_rejects() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = write(dir.path(), "perform.eph", PERFORM);
    let out = ephapax(&["check", path.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
    assert!(stderr(&out).contains(UNSUPPORTED_PREFIX));
}

// ---------------------------------------------------------------------------
// raw FFI (probe g5) and the extern rewrite
// ---------------------------------------------------------------------------

#[test]
fn g5_raw_ffi_is_a_named_error() {
    let surface = parse_surface_module(G5, "g5").expect("parse");
    let core = desugar(&surface).expect("desugar");
    let err = type_check_module(&core).expect_err("raw __ffi must be rejected");
    assert!(
        matches!(err.error, TypeError::RawFfiNotSupported(ref s) if s == "foo"),
        "got {:?}",
        err.error
    );

    let dir = tempfile::tempdir().expect("tempdir");
    let path = write(dir.path(), "g5.eph", G5);
    let out = ephapax(&["check", path.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
    assert!(stderr(&out).contains("Raw `__ffi(\"foo\", ...)` is not supported"));
    assert_compile_rejected("g5", G5, "RawFfiNotSupported");
}

/// Codegen refuses raw FFI even when handed an unchecked module (the
/// type checker is not the only line of defence).
#[test]
fn codegen_refuses_raw_ffi_in_unchecked_module() {
    let module = Module {
        name: "g5".into(),
        imports: vec![],
        decls: vec![Decl::Fn {
            name: "t".into(),
            visibility: Visibility::Private,
            type_params: vec![],
            params: vec![],
            ret_ty: Ty::Base(ephapax_syntax::BaseTy::I64),
            body: Expr::dummy(ExprKind::FFI {
                symbol: "foo".into(),
                args: vec![Expr::dummy(ExprKind::Lit(Literal::I32(1)))],
            }),
        }],
    };
    let err = compile_module(&module).expect_err("raw FFI must not lower");
    assert!(
        err.0.starts_with(UNSUPPORTED_PREFIX) && err.0.contains("__ffi"),
        "{}",
        err.0
    );
}

/// The scan must reach raw FFI below a supported node (here a `let`
/// value), not only at the top of a function body.
#[test]
fn codegen_refuses_raw_ffi_nested_in_a_let_value() {
    let ffi = Expr::dummy(ExprKind::FFI {
        symbol: "foo".into(),
        args: vec![],
    });
    let module = Module {
        name: "nested".into(),
        imports: vec![],
        decls: vec![Decl::Fn {
            name: "t".into(),
            visibility: Visibility::Private,
            type_params: vec![],
            params: vec![],
            ret_ty: Ty::Base(ephapax_syntax::BaseTy::I32),
            body: Expr::dummy(ExprKind::Let {
                name: "x".into(),
                ty: None,
                value: Box::new(ffi),
                body: Box::new(Expr::dummy(ExprKind::Lit(Literal::I32(0)))),
            }),
        }],
    };
    let err = compile_module(&module).expect_err("nested raw FFI must not lower");
    assert!(
        err.0.starts_with(UNSUPPORTED_PREFIX) && err.0.contains("__ffi"),
        "{}",
        err.0
    );
}

#[test]
fn g5_extern_rewrite_has_contiguous_imports_and_validates() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = write(dir.path(), "g5ext.eph", G5_EXTERN);
    let wasm_path = dir.path().join("g5ext.wasm");
    let out = ephapax(&[
        "compile",
        path.to_str().unwrap(),
        "-o",
        wasm_path.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "compile failed:\n{}", stderr(&out));
    let bytes = std::fs::read(&wasm_path).expect("read wasm");

    // Structural validation, twice: wasmparser, and wasmtime's own
    // validator + compiler (the in-process twin of `wasmtime compile`).
    wasmparser::validate(&bytes).expect("wasmparser validation");
    let engine = wasmtime::Engine::default();
    wasmtime::Module::new(&engine, &bytes).expect("wasmtime validates and compiles");

    // Function imports, in index order.
    let mut func_imports: Vec<(String, String)> = Vec::new();
    let mut calls: Vec<u32> = Vec::new();
    let mut defined_funcs = 0u32;
    for payload in Parser::new(0).parse_all(&bytes) {
        match payload.expect("parse") {
            Payload::ImportSection(reader) => {
                for import in reader {
                    let import = import.expect("import");
                    if let TypeRef::Func(_) = import.ty {
                        func_imports.push((import.module.to_string(), import.name.to_string()));
                    }
                }
            }
            Payload::FunctionSection(reader) => defined_funcs = reader.count(),
            Payload::CodeSectionEntry(body) => {
                let mut ops = body.get_operators_reader().expect("ops");
                while !ops.eof() {
                    if let Operator::Call { function_index } = ops.read().expect("op") {
                        calls.push(function_index);
                    }
                }
            }
            _ => {}
        }
    }
    assert_eq!(
        func_imports,
        vec![
            ("env".to_string(), "print_i32".to_string()),
            ("env".to_string(), "print_string".to_string()),
            ("env".to_string(), "foo".to_string()),
            ("env".to_string(), "bar".to_string()),
        ],
        "imports must be the builtins followed by the extern fns, contiguously"
    );
    let total = func_imports.len() as u32 + defined_funcs;
    assert!(
        calls.iter().all(|&i| i < total),
        "every call targets an existing function: {calls:?} (total {total})"
    );
    assert!(calls.contains(&2), "t calls foo at import index 2");
    assert!(calls.contains(&3), "t calls bar at import index 3");
}

// ---------------------------------------------------------------------------
// @total / @pure / @comptime
// ---------------------------------------------------------------------------

fn assert_annotation_rejected(src: &str, name: &str) {
    for (parser, result) in [
        ("surface", parse_surface_module(src, "a").map(|_| ())),
        ("core", parse_module(src, "a").map(|_| ())),
    ] {
        let errs = result.expect_err("annotation must be rejected");
        assert!(
            errs.iter().any(|e| matches!(
                e,
                ParseError::AnnotationNotEnforced { name: n, .. } if n == name
            )),
            "{parser} parser: expected AnnotationNotEnforced(@{name}), got {errs:?}"
        );
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let path = write(dir.path(), "a.eph", src);
    let out = ephapax(&["check", path.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
    assert!(
        stderr(&out).contains(&format!("Annotation `@{name}` is not enforced")),
        "{}",
        stderr(&out)
    );
    assert_compile_rejected("a", src, "is not enforced");
}

#[test]
fn total_loop_rejected_as_not_enforced() {
    assert_annotation_rejected(TOTAL_LOOP, "total");
}

#[test]
fn pure_with_effect_rejected_as_not_enforced() {
    assert_annotation_rejected(PURE_WITH_EFFECT, "pure");
}

#[test]
fn comptime_rejected_as_not_enforced() {
    assert_annotation_rejected(COMPTIME, "comptime");
}

// ---------------------------------------------------------------------------
// -O, --debug, --mode
// ---------------------------------------------------------------------------

#[test]
fn opt_level_above_zero_is_rejected() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = write(dir.path(), "p.eph", PLAIN);
    let wasm = dir.path().join("p.wasm");
    let out = ephapax(&[
        "compile",
        path.to_str().unwrap(),
        "-O2",
        "-o",
        wasm.to_str().unwrap(),
    ]);
    assert_eq!(out.status.code(), Some(1), "{}", stderr(&out));
    assert!(
        stderr(&out).contains("-O2 is not supported"),
        "{}",
        stderr(&out)
    );
    assert!(!wasm.exists());

    let out = ephapax(&[
        "compile",
        path.to_str().unwrap(),
        "-O0",
        "-o",
        wasm.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "-O0 is accepted: {}", stderr(&out));
    assert!(wasm.exists());
}

fn custom_section_names(bytes: &[u8]) -> Vec<String> {
    Parser::new(0)
        .parse_all(bytes)
        .filter_map(|p| match p.expect("parse") {
            Payload::CustomSection(c) => Some(c.name().to_string()),
            _ => None,
        })
        .collect()
}

#[test]
fn debug_flag_takes_effect() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = write(dir.path(), "p.eph", PLAIN);

    let plain = dir.path().join("plain.wasm");
    let out = ephapax(&[
        "compile",
        path.to_str().unwrap(),
        "-o",
        plain.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let plain_bytes = std::fs::read(&plain).expect("read");
    assert!(!custom_section_names(&plain_bytes).contains(&"ephapax.debug.mode".to_string()));
    assert!(!plain.with_extension("wasm.map").exists());

    let dbg = dir.path().join("dbg.wasm");
    let out = ephapax(&[
        "compile",
        path.to_str().unwrap(),
        "--debug",
        "-o",
        dbg.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let dbg_bytes = std::fs::read(&dbg).expect("read");
    wasmparser::validate(&dbg_bytes).expect("debug module validates");
    assert!(
        custom_section_names(&dbg_bytes).contains(&"ephapax.debug.mode".to_string()),
        "--debug must add the ephapax.debug.mode section"
    );
    let map = std::fs::read_to_string(dbg.with_extension("wasm.map")).expect("source map");
    assert!(!map.trim().is_empty(), "--debug must write a source map");
}

#[test]
fn mode_flag_is_rejected_by_check_and_compile() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = write(dir.path(), "p.eph", PLAIN);
    let p = path.to_str().unwrap();

    let out = ephapax(&["check", p]);
    assert!(out.status.success(), "{}", stderr(&out));

    for mode in ["affine", "linear"] {
        let out = ephapax(&["check", "--mode", mode, p]);
        assert_eq!(out.status.code(), Some(1), "check --mode {mode}");
        assert!(
            stderr(&out).contains(&format!("--mode {mode} is not supported")),
            "{}",
            stderr(&out)
        );

        let wasm = dir.path().join(format!("{mode}.wasm"));
        let out = ephapax(&["compile", p, "--mode", mode, "-o", wasm.to_str().unwrap()]);
        assert_eq!(out.status.code(), Some(1), "compile --mode {mode}");
        assert!(!wasm.exists());
    }
}
