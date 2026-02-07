// SPDX-License-Identifier: PMPL-1.0-or-later
// Integration tests for Affine Mode

use ephapax_parser::parse_module;
use ephapax_typing::{type_check_module_with_mode, Mode};

#[test]
fn test_affine_implicit_drop() {
    let code = r#"
fn test(_unit: ()): I32 =
    region r {
        let s = String.new@r("hello") in
        42
    }
"#;

    let module = parse_module(code, "test").expect("parse failed");
    let result = type_check_module_with_mode(&module, Mode::Affine);
    assert!(result.is_ok(), "Affine mode should allow implicit drops");
}

#[test]
fn test_affine_still_prevents_double_use() {
    let code = r#"
fn test(_unit: ()): I32 =
    region r {
        let s = String.new@r("hello") in
        let _ = drop(s) in
        let _ = drop(s) in
        42
    }
"#;

    let module = parse_module(code, "test").expect("parse failed");
    let result = type_check_module_with_mode(&module, Mode::Affine);
    assert!(result.is_err(), "Affine mode should still prevent double-use");
}

#[test]
fn test_affine_multiple_resources() {
    let code = r#"
fn test(_unit: ()): I32 =
    region r {
        let s1 = String.new@r("first") in
        let s2 = String.new@r("second") in
        let s3 = String.new@r("third") in
        100
    }
"#;

    let module = parse_module(code, "test").expect("parse failed");
    let result = type_check_module_with_mode(&module, Mode::Affine);
    assert!(result.is_ok(), "Affine mode should allow multiple unconsumed resources");
}

#[test]
fn test_affine_borrow_without_consume() {
    let code = r#"
fn test(_unit: ()): I32 =
    region r {
        let s = String.new@r("test") in
        let len = String.len(&s) in
        len
    }
"#;

    let module = parse_module(code, "test").expect("parse failed");
    let result = type_check_module_with_mode(&module, Mode::Affine);
    assert!(result.is_ok(), "Affine mode should allow borrow without drop");
}

#[test]
fn test_affine_conditional_no_drop() {
    let code = r#"
fn test(flag: Bool): I32 =
    region r {
        let s = String.new@r("data") in
        let result = if flag then
            String.len(&s)
        else
            0
        in
        result
    }
"#;

    let module = parse_module(code, "test").expect("parse failed");
    let result = type_check_module_with_mode(&module, Mode::Affine);
    assert!(result.is_ok(), "Affine mode should allow unconsumed in both branches");
}

#[test]
fn test_affine_nested_regions() {
    let code = r#"
fn test(_unit: ()): I32 =
    region r1 {
        let s1 = String.new@r1("outer") in
        region r2 {
            let s2 = String.new@r2("inner") in
            42
        }
    }
"#;

    let module = parse_module(code, "test").expect("parse failed");
    let result = type_check_module_with_mode(&module, Mode::Affine);
    assert!(result.is_ok(), "Affine mode should allow nested region implicit drops");
}

#[test]
fn test_affine_partial_cleanup() {
    let code = r#"
fn test(_unit: ()): I32 =
    region r {
        let s1 = String.new@r("first") in
        let s2 = String.new@r("second") in
        let _ = drop(s1) in
        100
    }
"#;

    let module = parse_module(code, "test").expect("parse failed");
    let result = type_check_module_with_mode(&module, Mode::Affine);
    assert!(result.is_ok(), "Affine mode should allow partial cleanup");
}
