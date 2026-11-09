// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! linearity_holes.rs — the gate for rung E0 ("Holes first") of the v2
//! plan (`docs/reports/2026-11-04-v2-survey/EPHAPAX-V2-ARCHITECTURE-AND-PLAN.adoc`).
//!
//! Every probe below was accepted by `ephapax check` before E0 (or, for
//! `rec1`, aborted the compiler with a stack overflow). Each one must now
//! be rejected with a *named* error kind, checked on the library pipeline
//! (surface parse → desugar → type check), and `ephapax check` must exit
//! with the compiler's normal failure status (1), never a signal.
//!
//! The survey probes are included verbatim from the evidence directory so
//! the gate cannot drift from the recorded finding.

use std::path::{Path, PathBuf};
use std::process::Command;

use ephapax_desugar::{desugar, DesugarError};
use ephapax_parser::{parse_module, parse_surface_module};
use ephapax_syntax::{Expr, ExprKind, Ty};
use ephapax_typing::{type_check_module, TypeChecker, TypeError};

const DUP2: &str =
    include_str!("../../../docs/reports/2026-11-04-v2-survey/evidence/probes/dup2.eph.txt");
const DUP4: &str =
    include_str!("../../../docs/reports/2026-11-04-v2-survey/evidence/probes/dup4.eph.txt");
const PAIRDUP: &str =
    include_str!("../../../docs/reports/2026-11-04-v2-survey/evidence/probes/pairdup.eph.txt");
const LAMCAP: &str =
    include_str!("../../../docs/reports/2026-11-04-v2-survey/evidence/probes/lamcap.eph.txt");
const REC1: &str =
    include_str!("../../../docs/reports/2026-11-04-v2-survey/evidence/probes/rec1.eph.txt");

/// A sum holding a linear string, duplicated through two aliases.
const SUMDUP: &str = "\
fn main(): I32 =
  region r {
    let s = String.new@r(\"hi\") in
    let x = inr[I32](s) in
    let a = x in
    let b = x in
    0
  }
";

/// A three-element tuple holding a linear string, duplicated.
const TUPLEDUP: &str = "\
fn main(): I32 =
  region r {
    let s = String.new@r(\"hi\") in
    let t = (s, 1, 2) in
    let a = t in
    let b = t in
    0
  }
";

/// A list of linear strings, duplicated.
const LISTDUP: &str = "\
fn main(): I32 =
  region r {
    let s = String.new@r(\"hi\") in
    let xs = [s] in
    let a = xs in
    let b = xs in
    0
  }
";

/// `(_, y)` over a pair whose first component is linear: the wildcard
/// would discard the string.
const WILDPAIR: &str = "\
fn main(): I32 =
  region r {
    let s = String.new@r(\"hi\") in
    let p = (s, 1) in
    let (_, y) = p in
    y
  }
";

/// A duplicate binder in one pattern: the second `x` would shadow (and
/// discard) the first.
const DUPBINDER: &str = "\
fn main(): I32 =
  let p = (1, 2) in
  let (x, x) = p in
  x
";

/// Tuple projection `t.0` from a tuple of two linear strings: `t.1`
/// would be lost.
const TUPLEIDX: &str = "\
fn main(): I32 =
  region r {
    let a = String.new@r(\"a\") in
    let b = String.new@r(\"b\") in
    let t = (a, b) in
    let c = t.0 in
    drop(c);
    0
  }
";

/// List index from a list of linear strings: the other elements would
/// be lost.
const LISTIDX: &str = "\
fn main(): I32 =
  region r {
    let a = String.new@r(\"a\") in
    let b = String.new@r(\"b\") in
    let xs = [a, b] in
    let c = xs[0] in
    drop(c);
    0
  }
";

/// Destructuring a linear pair is the supported way to take it apart, so
/// it must still type-check (and the string must be consumed).
const DESTRUCT_OK: &str = "\
fn main(): I32 =
  region r {
    let s = String.new@r(\"hi\") in
    let p = (s, 1) in
    let (a, y) = p in
    drop(a);
    y
  }
";

/// Pair destructuring lowers to a core `match`; its wasm must compute
/// the right value (3 + 4 * 10).
const DESTRUCT_VAL: &str = "\
fn main(): I32 =
  let p = (3, 4) in
  let (a, b) = p in
  a + b * 10
";

/// A three-field constructor payload is destructured with one core
/// `match` on a right-nested pair pattern.
const DESTRUCT3: &str = "\
data Tri = T(I32, I32, I32)
fn sum(t: Tri): I32 =
  match t of
  | T(a, b, c) => a + b * 10 + c * 100
  end
fn main(): I32 = sum(T(1, 2, 3))
";

/// A closure that only reads an unrestricted capture is fine.
const LAMBDA_UNRESTRICTED_CAPTURE: &str = "\
fn main(): I32 =
  let n = 5 in
  let f = fn(u: ()) -> n in
  f(()) + f(())
";

#[derive(Debug)]
enum PipelineError {
    Desugar(DesugarError),
    Type(TypeError),
}

/// Library pipeline used by `ephapax check`: surface parse → desugar →
/// type check, falling back to the core parser when the surface parser
/// rejects the file (as `check_files` does; `pairdup` needs it).
fn pipeline(src: &str) -> Result<(), PipelineError> {
    let core = match parse_surface_module(src, "probe") {
        Ok(surface) => desugar(&surface).map_err(PipelineError::Desugar)?,
        Err(_) => parse_module(src, "probe").expect("probe must parse"),
    };
    type_check_module(&core).map_err(|e| PipelineError::Type(e.error))
}

fn type_error(src: &str) -> TypeError {
    match pipeline(src) {
        Err(PipelineError::Type(e)) => e,
        other => panic!("expected a type error, got {other:?}"),
    }
}

fn ephapax_bin() -> String {
    env!("CARGO_BIN_EXE_ephapax").to_string()
}

fn write_probe(dir: &Path, name: &str, src: &str) -> PathBuf {
    let path = dir.join(format!("{name}.eph"));
    std::fs::write(&path, src).expect("write probe");
    path
}

/// `ephapax check` must reject the probe with exit status 1 (the CLI's
/// normal error exit), not a crash or abort.
fn assert_cli_rejects(name: &str, src: &str) -> String {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = write_probe(dir.path(), name, src);
    let out = Command::new(ephapax_bin())
        .arg("check")
        .arg(&path)
        .output()
        .expect("run ephapax check");
    let stderr = String::from_utf8_lossy(&out.stderr).to_string();
    assert_eq!(
        out.status.code(),
        Some(1),
        "{name}: expected exit 1 (normal error), got {:?}\nstderr:\n{stderr}",
        out.status
    );
    stderr
}

#[test]
fn dup2_let_bang_reused_rejected() {
    assert!(matches!(
        type_error(DUP2),
        TypeError::LinearVariableReused(ref v) if v == "x"
    ));
    assert_cli_rejects("dup2", DUP2);
}

#[test]
fn dup4_let_bang_passed_twice_rejected() {
    assert!(matches!(
        type_error(DUP4),
        TypeError::LinearVariableReused(ref v) if v == "x"
    ));
    assert_cli_rejects("dup4", DUP4);
}

#[test]
fn pairdup_rejected() {
    // Escalation note (plan E0, "Depends"): this relies on the
    // conservative compound join in `Ty::is_linear`; D5 (W1) may relax it.
    assert!(matches!(
        type_error(PAIRDUP),
        TypeError::LinearVariableReused(ref v) if v == "p"
    ));
    assert_cli_rejects("pairdup", PAIRDUP);
}

#[test]
fn lamcap_rejected() {
    assert!(matches!(
        type_error(LAMCAP),
        TypeError::LinearCaptureConsumed(ref v) if v == "s"
    ));
    assert_cli_rejects("lamcap", LAMCAP);
}

#[test]
fn sum_of_linear_duplication_rejected() {
    assert!(matches!(
        type_error(SUMDUP),
        TypeError::LinearVariableReused(ref v) if v == "x"
    ));
    assert_cli_rejects("sumdup", SUMDUP);
}

#[test]
fn tuple_of_linear_duplication_rejected() {
    assert!(matches!(
        type_error(TUPLEDUP),
        TypeError::LinearVariableReused(ref v) if v == "t"
    ));
    assert_cli_rejects("tupledup", TUPLEDUP);
}

#[test]
fn list_of_linear_duplication_rejected() {
    assert!(matches!(
        type_error(LISTDUP),
        TypeError::LinearVariableReused(ref v) if v == "xs"
    ));
    assert_cli_rejects("listdup", LISTDUP);
}

/// The surface has no dereference syntax, so the double-borrow probe is
/// built as core AST (the form desugar and the S-expression IR produce):
///
/// ```text
/// region r {
///   let! s = String.new@r("hi") in
///   let b1 = &s in let b2 = &s in
///   drop(*b1); drop(*b2); drop(s); 0 }
/// ```
#[test]
fn double_borrow_then_drop_rejected() {
    let e = Expr::dummy;
    let var = |n: &str| Expr::dummy(ExprKind::Var(n.into()));
    let borrow_s = || {
        Expr::dummy(ExprKind::Borrow {
            inner: Box::new(var("s")),
            mutable: false,
        })
    };
    let drop_deref = |n: &str| {
        Expr::dummy(ExprKind::Drop(Box::new(Expr::dummy(ExprKind::Deref(
            Box::new(var(n)),
        )))))
    };
    let body = e(ExprKind::Block(vec![
        drop_deref("b1"),
        drop_deref("b2"),
        e(ExprKind::Drop(Box::new(var("s")))),
        e(ExprKind::Lit(ephapax_syntax::Literal::I32(0))),
    ]));
    let program = e(ExprKind::Region {
        name: "r".into(),
        body: Box::new(e(ExprKind::LetLin {
            name: "s".into(),
            ty: None,
            value: Box::new(e(ExprKind::StringNew {
                region: "r".into(),
                value: "hi".into(),
            })),
            body: Box::new(e(ExprKind::Let {
                name: "b1".into(),
                ty: None,
                value: Box::new(borrow_s()),
                body: Box::new(e(ExprKind::Let {
                    name: "b2".into(),
                    ty: None,
                    value: Box::new(borrow_s()),
                    body: Box::new(body),
                })),
            })),
        })),
    });
    let err = TypeChecker::new()
        .check(&program)
        .expect_err("double borrow then drop must be rejected");
    assert!(
        matches!(err.error, TypeError::CannotMoveOutOfBorrow(Ty::String(_))),
        "got {:?}",
        err.error
    );
}

#[test]
fn deref_of_unrestricted_borrow_still_allowed() {
    let mut tc = TypeChecker::new();
    tc.check(&Expr::dummy(ExprKind::Deref(Box::new(Expr::dummy(
        ExprKind::Borrow {
            inner: Box::new(Expr::dummy(ExprKind::Lit(ephapax_syntax::Literal::I32(7)))),
            mutable: false,
        },
    )))))
    .expect("deref of a borrow of an I32 copies it");
}

#[test]
fn wildcard_over_linear_pair_component_rejected() {
    assert!(matches!(
        type_error(WILDPAIR),
        TypeError::LinearPatternDiscard(Ty::String(_))
    ));
    assert_cli_rejects("wildpair", WILDPAIR);
}

#[test]
fn duplicate_pattern_binder_rejected() {
    assert!(matches!(
        type_error(DUPBINDER),
        TypeError::DuplicatePatternBinder(ref v) if v == "x"
    ));
    assert_cli_rejects("dupbinder", DUPBINDER);
}

#[test]
fn tuple_projection_from_linear_tuple_rejected() {
    assert!(matches!(
        type_error(TUPLEIDX),
        TypeError::LinearProjectionDiscard(_)
    ));
    assert_cli_rejects("tupleidx", TUPLEIDX);
}

#[test]
fn list_index_from_linear_list_rejected() {
    assert!(matches!(
        type_error(LISTIDX),
        TypeError::LinearProjectionDiscard(Ty::List(_))
    ));
    assert_cli_rejects("listidx", LISTIDX);
}

#[test]
fn rec1_is_a_named_desugar_error_not_a_crash() {
    match pipeline(REC1) {
        Err(PipelineError::Desugar(DesugarError::RecursiveType { name, .. })) => {
            assert_eq!(name, "L");
        }
        other => panic!("expected DesugarError::RecursiveType, got {other:?}"),
    }
    let stderr = assert_cli_rejects("rec1", REC1);
    assert!(
        stderr.contains("recursive type `L`"),
        "stderr should name the recursive type:\n{stderr}"
    );
}

#[test]
fn nested_data_application_is_not_mistaken_for_recursion() {
    let src = "\
data Option(a) = None | Some(a)
fn f(x: Option(Option(I32))): I32 = 0
fn main(): I32 = 0
";
    pipeline(src).expect("Option(Option(I32)) is not recursive");
}

#[test]
fn destructuring_a_linear_pair_still_checks() {
    pipeline(DESTRUCT_OK).expect("destructuring is the supported way to split a linear pair");
}

#[test]
fn closure_reading_unrestricted_capture_still_checks() {
    pipeline(LAMBDA_UNRESTRICTED_CAPTURE).expect("unrestricted captures may be reused");
}

/// Compile with the CLI and run `main` under wasmtime.
fn compile_and_run(name: &str, src: &str) -> i32 {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = write_probe(dir.path(), name, src);
    let wasm_path = dir.path().join(format!("{name}.wasm"));
    let out = Command::new(ephapax_bin())
        .arg("compile")
        .arg(&path)
        .arg("-o")
        .arg(&wasm_path)
        .output()
        .expect("run ephapax compile");
    assert!(
        out.status.success(),
        "{name} must compile:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let bytes = std::fs::read(&wasm_path).expect("read wasm");
    let engine = wasmtime::Engine::default();
    let module = wasmtime::Module::new(&engine, &bytes).expect("module");
    let mut store = wasmtime::Store::new(&engine, ());
    let mut linker = wasmtime::Linker::new(&engine);
    linker
        .func_wrap("env", "print_i32", |_v: i32| {})
        .expect("print_i32");
    linker
        .func_wrap("env", "print_string", |_p: i32, _l: i32| {})
        .expect("print_string");
    let instance = linker
        .instantiate(&mut store, &module)
        .expect("instantiate");
    let main = instance
        .get_typed_func::<(), i32>(&mut store, "main")
        .expect("main");
    main.call(&mut store, ()).expect("main must not trap")
}

#[test]
fn pair_destructuring_lowering_computes_correct_value() {
    assert_eq!(compile_and_run("destruct_val", DESTRUCT_VAL), 43);
}

#[test]
fn multi_field_constructor_destructuring_checks() {
    // Type-level only. The wasm for a nested pair payload is wrong on
    // the base commit too (`fst((1, (2, 3)))` evaluates to 521 with the
    // pre-E0 compiler), a codegen defect outside E0, so this gate does
    // not assert the runtime value of a three-field payload.
    pipeline(DESTRUCT3).expect("three-field constructor destructuring type-checks");
}
