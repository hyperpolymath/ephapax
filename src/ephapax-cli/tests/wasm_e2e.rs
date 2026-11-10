// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! End-to-end WASM tests: parse -> type-check -> compile -> run via wasmtime.
//!
//! Tests the full pipeline from source text to executing WASM module.

use ephapax_parser::parse;
use ephapax_typing::TypeChecker;
use ephapax_wasm::Codegen;

/// Full pipeline: parse -> type-check -> compile to WASM bytes.
///
/// Asserts the emitted module passes structural validation. This is the
/// in-process (wasmparser) twin of the `wasm-tools validate` gate run by
/// `just validate-wasm` / CI, so EVERY e2e program is checked for
/// structural validity here — not only the subset that `run()`
/// instantiates via wasmtime.
fn compile(source: &str) -> Vec<u8> {
    let expr = parse(source).expect("parse failed");
    let mut tc = TypeChecker::new();
    tc.check(&expr).expect("type-check failed");
    let mut codegen = Codegen::new();
    let wasm = codegen.compile_program(&expr).unwrap();
    wasmparser::validate(&wasm).expect("emitted wasm failed wasmparser validation");
    wasm
}

/// Compile and run via wasmtime, asserting no traps.
/// Provides stub implementations for env::print_i32 and env::print_string.
fn run(source: &str) {
    let wasm_bytes = compile(source);

    let engine = wasmtime::Engine::default();
    let module = wasmtime::Module::new(&engine, &wasm_bytes).expect("WASM module creation failed");
    let mut store = wasmtime::Store::new(&engine, ());
    let mut linker = wasmtime::Linker::new(&engine);

    // Provide runtime imports: print_i32(i32) and print_string(i32, i32)
    linker
        .func_wrap("env", "print_i32", |_val: i32| {})
        .expect("failed to define print_i32");
    linker
        .func_wrap("env", "print_string", |_ptr: i32, _len: i32| {})
        .expect("failed to define print_string");

    let instance = linker
        .instantiate(&mut store, &module)
        .expect("WASM instantiation failed");
    let main_fn = instance
        .get_typed_func::<(), ()>(&mut store, "main")
        .expect("main function not found");
    main_fn
        .call(&mut store, ())
        .expect("WASM execution trapped");
}

// =========================================================================
// Basic expressions — compile and run without trapping
// =========================================================================

#[test]
fn e2e_integer_literal() {
    run("42");
}

#[test]
fn e2e_bool_literal() {
    run("true");
}

#[test]
fn e2e_unit_literal() {
    run("()");
}

#[test]
fn e2e_let_binding() {
    run("let x = 42 in x");
}

#[test]
fn e2e_nested_let() {
    run("let x = 1 in let y = 2 in x");
}

#[test]
fn e2e_if_true() {
    run("if true then 1 else 2");
}

#[test]
fn e2e_if_false() {
    run("if false then 1 else 2");
}

#[test]
fn e2e_pair() {
    run("(1, 2)");
}

#[test]
fn e2e_lambda_application() {
    run("(fn(x: I32) -> x)(42)");
}

#[test]
fn e2e_let_bang() {
    run("let! x = 42 in x");
}

#[test]
fn e2e_arithmetic() {
    run("let x = 1 + 2 in x");
}

#[test]
fn e2e_comparison() {
    run("1 < 2");
}

// =========================================================================
// WASM module validity
// =========================================================================

#[test]
fn e2e_wasm_header_valid() {
    let wasm = compile("42");
    assert!(wasm.len() >= 8, "WASM too small: {} bytes", wasm.len());
    assert_eq!(&wasm[0..4], b"\x00asm", "bad WASM magic");
    assert_eq!(&wasm[4..8], &[1, 0, 0, 0], "bad WASM version");
}

// =========================================================================
// Core `match` on a hand-built module: the result of `main` is checked
// =========================================================================

/// Compile a module whose only function is `main(): <ret_ty> = body`, run
/// it, and return the result of `main`.
fn run_main<R: wasmtime::WasmResults>(ret_ty: ephapax_syntax::Ty, body: ephapax_syntax::Expr) -> R {
    use ephapax_syntax::{Decl, Module, Visibility};
    let module = Module {
        name: "t".into(),
        imports: vec![],
        decls: vec![Decl::Fn {
            name: "main".into(),
            visibility: Visibility::Private,
            type_params: vec![],
            params: vec![],
            ret_ty,
            body,
        }],
    };
    let wasm = ephapax_wasm::compile_module(&module).expect("the module compiles");
    wasmparser::validate(&wasm).expect("emitted wasm failed wasmparser validation");

    let engine = wasmtime::Engine::default();
    let module = wasmtime::Module::new(&engine, &wasm).expect("WASM module creation failed");
    let mut store = wasmtime::Store::new(&engine, ());
    let mut linker = wasmtime::Linker::new(&engine);
    linker
        .func_wrap("env", "print_i32", |_val: i32| {})
        .expect("failed to define print_i32");
    linker
        .func_wrap("env", "print_string", |_ptr: i32, _len: i32| {})
        .expect("failed to define print_string");
    let instance = linker
        .instantiate(&mut store, &module)
        .expect("WASM instantiation failed");
    instance
        .get_typed_func::<(), R>(&mut store, "main")
        .expect("main function not found")
        .call(&mut store, ())
        .expect("WASM execution trapped")
}

/// A tuple pattern reads the 8-byte slots of the tuple, each at its own
/// type. It used to follow pair pointers, which a tuple does not have.
#[test]
fn e2e_tuple_pattern_reads_the_tuple_slots() {
    use ephapax_syntax::{BaseTy, Expr, ExprKind, Literal, MatchArm, Pattern, Ty};
    let lit = |l| Expr::dummy(ExprKind::Lit(l));
    // match (1, 5000000000, 3) of | (a, b, c) => b end
    let body = Expr::dummy(ExprKind::Match {
        scrutinee: Box::new(Expr::dummy(ExprKind::TupleLit(vec![
            lit(Literal::I32(1)),
            lit(Literal::I64(5_000_000_000)),
            lit(Literal::I32(3)),
        ]))),
        arms: vec![MatchArm {
            pattern: Pattern::Tuple(vec![
                Pattern::Var("a".into()),
                Pattern::Var("b".into()),
                Pattern::Var("c".into()),
            ]),
            guard: None,
            body: Expr::dummy(ExprKind::Var("b".into())),
        }],
    });
    let result: i64 = run_main(Ty::Base(BaseTy::I64), body);
    assert_eq!(result, 5_000_000_000);
}

/// A name that one `match` arm binds is not in scope in the next arm.
/// The next arm used to read the binder of the arm that did not match.
#[test]
fn e2e_match_arm_binder_ends_with_its_arm() {
    use ephapax_syntax::{BaseTy, Expr, ExprKind, Literal, MatchArm, Pattern, Ty};
    let lit = |n| Expr::dummy(ExprKind::Lit(Literal::I32(n)));
    let var = |name: &str| Expr::dummy(ExprKind::Var(name.into()));
    // let y = 5 in match (1, 2) of | (0, y) => y | _ => y end
    let matched = Expr::dummy(ExprKind::Match {
        scrutinee: Box::new(Expr::dummy(ExprKind::Pair {
            left: Box::new(lit(1)),
            right: Box::new(lit(2)),
        })),
        arms: vec![
            MatchArm {
                pattern: Pattern::Pair(
                    Box::new(Pattern::Literal(Literal::I32(0))),
                    Box::new(Pattern::Var("y".into())),
                ),
                guard: None,
                body: var("y"),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                guard: None,
                body: var("y"),
            },
        ],
    });
    let body = Expr::dummy(ExprKind::Let {
        name: "y".into(),
        ty: None,
        value: Box::new(lit(5)),
        body: Box::new(matched),
    });
    let result: i32 = run_main(Ty::Base(BaseTy::I32), body);
    assert_eq!(result, 5);
}
