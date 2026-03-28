// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! End-to-end WASM tests: parse -> type-check -> compile -> run via wasmtime.
//!
//! Tests the full pipeline from source text to executing WASM module.

use ephapax_parser::parse;
use ephapax_typing::TypeChecker;
use ephapax_wasm::Codegen;

/// Full pipeline: parse -> type-check -> compile to WASM bytes
fn compile(source: &str) -> Vec<u8> {
    let expr = parse(source).expect("parse failed");
    let mut tc = TypeChecker::new();
    tc.check(&expr).expect("type-check failed");
    let mut codegen = Codegen::new();
    codegen.compile_program(&expr)
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
#[ignore = "codegen: closure table not yet emitted — tracked"]
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
