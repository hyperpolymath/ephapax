// SPDX-License-Identifier: PMPL-1.0-or-later
// End-to-end integration tests

use ephapax_parser::parse_module;
use ephapax_typing::type_check_module;
use ephapax_wasm::compile_module;

#[test]
fn test_e2e_hello_world() {
    let code = r#"
fn main(_unit: ()): I32 =
    let x = 1 + 2 in
    let y = x * 3 in
    y
"#;

    let module = parse_module(code, "test").expect("parse failed");
    type_check_module(&module).expect("type check failed");
    let wasm = compile_module(&module).expect("WASM compilation failed");
    assert!(!wasm.is_empty(), "WASM output should not be empty");
    assert!(wasm.len() > 100, "WASM output should be substantial");
}

#[test]
fn test_e2e_arithmetic() {
    let code = r#"
fn add(x: I32, y: I32): I32 = x + y
fn mul(x: I32, y: I32): I32 = x * y

fn main(_unit: ()): I32 =
    let sum = add(10, 20) in
    let product = mul(5, 6) in
    sum + product
"#;

    let module = parse_module(code, "test").expect("parse failed");
    type_check_module(&module).expect("type check failed");
    let wasm = compile_module(&module).expect("WASM compilation failed");
    assert!(!wasm.is_empty());
}

#[test]
fn test_e2e_conditionals() {
    let code = r#"
fn abs(x: I32): I32 =
    if x < 0 then
        0 - x
    else
        x

fn main(_unit: ()): I32 =
    let a = abs(-5) in
    let b = abs(10) in
    a + b
"#;

    let module = parse_module(code, "test").expect("parse failed");
    type_check_module(&module).expect("type check failed");
    let wasm = compile_module(&module).expect("WASM compilation failed");
    assert!(!wasm.is_empty());
}

#[test]
fn test_e2e_pairs() {
    let code = r#"
fn swap(p: (I32, I32)): (I32, I32) =
    let x = p.0 in
    let y = p.1 in
    (y, x)

fn main(_unit: ()): I32 =
    let p = (10, 20) in
    let swapped = swap(p) in
    let x = swapped.0 in
    let y = swapped.1 in
    x + y
"#;

    let module = parse_module(code, "test").expect("parse failed");
    type_check_module(&module).expect("type check failed");
    let wasm = compile_module(&module).expect("WASM compilation failed");
    assert!(!wasm.is_empty());
}

#[test]
fn test_e2e_nested_let() {
    let code = r#"
fn compute(_unit: ()): I32 =
    let a = 1 in
    let b = 2 in
    let c = a + b in
    let d = c * 2 in
    let e = d + 10 in
    e

fn main(_unit: ()): I32 = compute(())
"#;

    let module = parse_module(code, "test").expect("parse failed");
    type_check_module(&module).expect("type check failed");
    let wasm = compile_module(&module).expect("WASM compilation failed");
    assert!(!wasm.is_empty());
}

#[test]
fn test_e2e_boolean_logic() {
    let code = r#"
fn logic(a: Bool, b: Bool): I32 =
    let and_result = if a && b then 1 else 0 in
    let or_result = if a || b then 10 else 0 in
    and_result + or_result

fn main(_unit: ()): I32 =
    let r1 = logic(true, true) in
    let r2 = logic(true, false) in
    let r3 = logic(false, true) in
    let r4 = logic(false, false) in
    r1 + r2 + r3 + r4
"#;

    let module = parse_module(code, "test").expect("parse failed");
    type_check_module(&module).expect("type check failed");
    let wasm = compile_module(&module).expect("WASM compilation failed");
    assert!(!wasm.is_empty());
}

#[test]
fn test_e2e_comparison_ops() {
    let code = r#"
fn compare(x: I32, y: I32): I32 =
    let eq = if x == y then 1 else 0 in
    let lt = if x < y then 10 else 0 in
    let gt = if x > y then 100 else 0 in
    eq + lt + gt

fn main(_unit: ()): I32 =
    let r1 = compare(5, 5) in
    let r2 = compare(3, 7) in
    let r3 = compare(9, 2) in
    r1 + r2 + r3
"#;

    let module = parse_module(code, "test").expect("parse failed");
    type_check_module(&module).expect("type check failed");
    let wasm = compile_module(&module).expect("WASM compilation failed");
    assert!(!wasm.is_empty());
}

#[test]
fn test_e2e_multiple_functions() {
    let code = r#"
fn square(x: I32): I32 = x * x
fn double(x: I32): I32 = x + x
fn inc(x: I32): I32 = x + 1

fn main(_unit: ()): I32 =
    let a = square(5) in
    let b = double(a) in
    let c = inc(b) in
    c
"#;

    let module = parse_module(code, "test").expect("parse failed");
    type_check_module(&module).expect("type check failed");
    let wasm = compile_module(&module).expect("WASM compilation failed");
    assert!(!wasm.is_empty());
}
