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

/// Projection from a three-element tuple goes through `check_tuple_index`
/// (a two-element tuple is a pair): `.2` would lose the linear `s`.
const TUPLEIDX3: &str = "\
fn main(): I32 =
  region r {
    let s = String.new@r(\"a\") in
    let t = (s, 1, 2) in
    t.2
  }
";

/// Pair destructuring whose body is an `I64` extern call: the lowered
/// core `match` must carry an `i64` result, not the default `i32`.
const DESTRUCT_I64: &str = "\
extern \"c\" {
  fn clock_gettime(): I64
}
fn f(p: (I32, I32)): I64 =
  let (a, b) = p in clock_gettime()
fn main(): I32 = 0
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
fn three_element_tuple_projection_from_linear_tuple_rejected() {
    assert!(matches!(
        type_error(TUPLEIDX3),
        TypeError::LinearProjectionDiscard(Ty::Tuple(_))
    ));
    assert_cli_rejects("tupleidx3", TUPLEIDX3);
}

#[test]
fn list_index_from_linear_list_rejected() {
    assert!(matches!(
        type_error(LISTIDX),
        TypeError::LinearProjectionDiscard(Ty::List(_))
    ));
    assert_cli_rejects("listidx", LISTIDX);
}

/// `rec1` has a `data` type that refers to itself. It aborted the compiler
/// with a stack overflow, and then it was a named desugar error. Since
/// rung E9 the core has recursive types: the probe desugars and checks,
/// and the command line refuses it by name without `--unstable-core`.
#[test]
fn rec1_is_behind_the_flag_not_a_crash() {
    assert!(pipeline(REC1).is_ok(), "{:?}", pipeline(REC1));
    let stderr = assert_cli_rejects("rec1", REC1);
    assert!(
        stderr.contains("behind the flag `--unstable-core`: the recursive type `L`"),
        "stderr should name the flag and the recursive type:\n{stderr}"
    );

    let dir = tempfile::tempdir().expect("tempdir");
    let path = write_probe(dir.path(), "rec1", REC1);
    let out = Command::new(ephapax_bin())
        .args(["check", "--unstable-core"])
        .arg(&path)
        .output()
        .expect("run ephapax check");
    assert!(
        out.status.success(),
        "with the flag:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
}

/// Each recursive form that has no lowering is a named desugar error.
#[test]
fn a_recursive_form_with_no_lowering_is_a_named_desugar_error() {
    let refused = |src: &str| match pipeline(src) {
        Err(PipelineError::Desugar(error)) => error,
        other => panic!("expected a desugar error, got {other:?}"),
    };
    // 2 `data` types that refer to each other.
    assert!(matches!(
        refused(
            "data Tree = Leaf | Node(Forest)\ndata Forest = FNil | FCons(Tree, Forest)\n\
             fn f(t: Tree): I32 = 0\nfn main(): I32 = 0\n"
        ),
        DesugarError::MutualRecursion { cycle } if cycle == "Tree -> Forest -> Tree"
    ));
    // A `data` type that refers to itself with other type arguments.
    assert!(matches!(
        refused(
            "data Grow(a) = Stop | More(Grow((a, a)))\nfn f(t: Grow(I32)): I32 = 0\n\
             fn main(): I32 = 0\n"
        ),
        DesugarError::NonRegularRecursion { name, .. } if name == "Grow"
    ));
    // A `type` alias that refers to itself with no `data` type between.
    assert!(matches!(
        refused("type A = (I32, B)\ntype B = (I32, A)\nfn f(t: A): I32 = 0\nfn main(): I32 = 0\n"),
        DesugarError::RecursiveAlias { .. }
    ));
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
fn multi_field_constructor_destructuring_computes_correct_value() {
    // A three-field payload is a nested pair. Before the bump pointer was
    // initialised, the first heap cell overwrote it and this read back
    // corrupted fields (`fst((1, (2, 3)))` gave 521).
    pipeline(DESTRUCT3).expect("three-field constructor destructuring type-checks");
    assert_eq!(compile_and_run("destruct3", DESTRUCT3), 321);
}

#[test]
fn pair_destructuring_keeps_an_i64_result_type() {
    pipeline(DESTRUCT_I64).expect("type-checks");
    let dir = tempfile::tempdir().expect("tempdir");
    let path = write_probe(dir.path(), "destruct_i64", DESTRUCT_I64);
    let out = Command::new(ephapax_bin())
        .arg("compile")
        .arg(&path)
        .arg("-o")
        .arg(dir.path().join("destruct_i64.wasm"))
        .output()
        .expect("run ephapax compile");
    assert!(
        out.status.success(),
        "an I64 arm body must give valid wasm:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
}

// ---------------------------------------------------------------------
// Shadowing (W0 follow-up). Before the fix a binder that reused an outer
// name overwrote the outer context entry and never gave it back, so the
// outer binding's consumption check ran against the inner entry (or
// against nothing): a shadowed `let!` could leak, and a consumed `let!`
// shadowed by an unused `let` was falsely reported as unconsumed. Every
// negative probe below was accepted by `ephapax check` (exit 0) on the
// base commit c0ff0a0, except `SHADOW_LAMBDA_CAPTURE` (rejected for the
// wrong reason, `UnnecessaryDrop`) and `SHADOW_INNER_UNCONSUMED` (the
// dual, which must keep working).
// ---------------------------------------------------------------------

/// A linear string shadowed by an affine `let` and never consumed.
const SHADOW_LET_LEAK: &str = "\
fn main(): I32 =
  region r {
    let! s = String.new@r(\"hi\") in
    let s = 5 in
    s
  }
";

/// A linear string shadowed by a second `let!` that *is* consumed: the
/// outer string still leaks.
const SHADOW_LET_BANG_LEAK: &str = "\
fn main(): I32 =
  region r {
    let! s = String.new@r(\"hi\") in
    let! s = String.new@r(\"ho\") in
    drop(s);
    0
  }
";

/// `let!` of an unrestricted value, shadowed and consumed through the
/// inner name only.
const SHADOW_LET_BANG_INT_LEAK: &str = "\
fn main(): I32 =
  let! x = 5 in
  let! x = 6 in
  x
";

/// The dual: the outer `let!` is consumed by the inner value, and the
/// inner `let!` itself is never consumed — its own check must remain.
const SHADOW_INNER_UNCONSUMED: &str = "\
fn main(): I32 =
  let! x = 5 in
  let! x = x + 1 in
  0
";

/// A pair-pattern binder that shadows a linear string, which then leaks.
const SHADOW_PATTERN_LEAK: &str = "\
fn main(): I32 =
  region r {
    let! s = String.new@r(\"hi\") in
    let p = (1, 2) in
    let (s, y) = p in
    y
  }
";

/// A `case` binder that shadows a linear string, which then leaks.
const SHADOW_CASE_LEAK: &str = "\
fn main(): I32 =
  region r {
    let! s = String.new@r(\"hi\") in
    let v = inl[I32](1) in
    case v of inl(s) -> s inr(t) -> t end
  }
";

/// A lambda parameter that shadows a linear string, which then leaks.
const SHADOW_LAMBDA_PARAM_LEAK: &str = "\
fn main(): I32 =
  region r {
    let! s = String.new@r(\"hi\") in
    let f = fn(n: I32) -> n + 1 in
    let g = fn(s: I32) -> s + 1 in
    f(1) + g(2)
  }
";

/// A closure that frees its capture and then shadows the name: the
/// capture check must still see the captured binding (else the string is
/// freed by every call and again by the enclosing scope).
const SHADOW_LAMBDA_CAPTURE: &str = "\
fn main(): I32 =
  region r {
    let! s = String.new@r(\"hi\") in
    let f = fn(u: ()) -> let s = drop(s) in 0 in
    drop(s);
    0
  }
";

/// Two parameters with one name: the second hides the first (linear)
/// one for the whole body.
const DUPLICATE_PARAMETER_LEAK: &str = "\
fn f(s: String@r, s: I32): I32 = s
fn main(): I32 =
  region r {
    let! a = String.new@r(\"hi\") in
    f(a, 2)
  }
";

/// Consuming a `let!` in the value of a shadowing `let` is fine; the
/// base commit wrongly reported the outer `s` as unconsumed.
const SHADOW_CONSUMED_THEN_REBOUND_OK: &str = "\
fn main(): I32 =
  region r {
    let! s = String.new@r(\"hi\") in
    let s = drop(s) in
    0
  }
";

/// Ordinary shadowing of unrestricted values keeps working.
const SHADOW_UNRESTRICTED_OK: &str = "\
fn main(): I32 =
  let x = 5 in
  let x = x + 1 in
  let f = fn(x: I32) -> x + 1 in
  f(x) + x
";

/// Pattern and `case` binders that do not shadow anything linear, with
/// the outer string consumed after them.
const SHADOW_SCOPED_BINDERS_OK: &str = "\
fn main(): I32 =
  region r {
    let! s = String.new@r(\"hi\") in
    let v = inl[I32](1) in
    let n = case v of inl(s) -> s inr(t) -> t end in
    let p = (1, 2) in
    let (s2, y) = p in
    drop(s);
    n + s2 + y
  }
";

fn assert_not_consumed(name: &str, src: &str, var: &str) {
    let err = type_error(src);
    assert!(
        matches!(err, TypeError::LinearVariableNotConsumed(ref v) if v == var),
        "{name}: expected LinearVariableNotConsumed({var}), got {err:?}"
    );
    assert_cli_rejects(name, src);
}

#[test]
fn shadowed_let_bang_by_let_must_still_be_consumed() {
    assert_not_consumed("shadow_let_leak", SHADOW_LET_LEAK, "s");
}

#[test]
fn shadowed_let_bang_by_let_bang_must_still_be_consumed() {
    assert_not_consumed("shadow_let_bang_leak", SHADOW_LET_BANG_LEAK, "s");
    assert_not_consumed("shadow_let_bang_int_leak", SHADOW_LET_BANG_INT_LEAK, "x");
}

#[test]
fn shadowing_let_bang_keeps_its_own_consumption_check() {
    assert_not_consumed("shadow_inner_unconsumed", SHADOW_INNER_UNCONSUMED, "x");
}

#[test]
fn shadowed_by_pattern_binder_must_still_be_consumed() {
    assert_not_consumed("shadow_pattern_leak", SHADOW_PATTERN_LEAK, "s");
}

#[test]
fn shadowed_by_case_binder_must_still_be_consumed() {
    assert_not_consumed("shadow_case_leak", SHADOW_CASE_LEAK, "s");
}

#[test]
fn shadowed_by_lambda_parameter_must_still_be_consumed() {
    assert_not_consumed("shadow_lambda_param_leak", SHADOW_LAMBDA_PARAM_LEAK, "s");
}

#[test]
fn closure_consuming_then_shadowing_a_capture_rejected() {
    let err = type_error(SHADOW_LAMBDA_CAPTURE);
    assert!(
        matches!(err, TypeError::LinearCaptureConsumed(ref v) if v == "s"),
        "expected LinearCaptureConsumed(s), got {err:?}"
    );
    assert_cli_rejects("shadow_lambda_capture", SHADOW_LAMBDA_CAPTURE);
}

#[test]
fn duplicate_function_parameter_rejected() {
    let err = type_error(DUPLICATE_PARAMETER_LEAK);
    assert!(
        matches!(err, TypeError::DuplicateParameter(ref v) if v == "s"),
        "expected DuplicateParameter(s), got {err:?}"
    );
    assert_cli_rejects("duplicate_parameter_leak", DUPLICATE_PARAMETER_LEAK);
}

#[test]
fn rebinding_a_consumed_let_bang_still_checks() {
    pipeline(SHADOW_CONSUMED_THEN_REBOUND_OK)
        .expect("the outer `s` is consumed by the shadowing binding's value");
}

#[test]
fn shadowing_unrestricted_values_still_checks() {
    pipeline(SHADOW_UNRESTRICTED_OK).expect("unrestricted shadowing is ordinary scoping");
}

#[test]
fn scoped_pattern_and_case_binders_still_check() {
    pipeline(SHADOW_SCOPED_BINDERS_OK).expect("binders are scoped to their arm");
}
