// SPDX-License-Identifier: PMPL-1.0-or-later
// Integration tests for Linear Mode

use ephapax_parser::parse_module;
use ephapax_typing::{type_check_module_with_mode, Mode};

#[test]
fn test_linear_requires_explicit_drop() {
    let code = r#"
fn test(_unit: ()): I32 =
    region r {
        let s = String.new@r("hello") in
        42
    }
"#;

    let module = parse_module(code, "test").expect("parse failed");
    let result = type_check_module_with_mode(&module, Mode::Linear);
    assert!(result.is_err(), "Linear mode should reject implicit drops");
}

#[test]
fn test_linear_explicit_drop_ok() {
    let code = r#"
fn test(_unit: ()): I32 =
    region r {
        let s = String.new@r("hello") in
        let _ = drop(s) in
        42
    }
"#;

    let module = parse_module(code, "test").expect("parse failed");
    let result = type_check_module_with_mode(&module, Mode::Linear);
    assert!(result.is_ok(), "Linear mode should accept explicit drops");
}

#[test]
fn test_linear_prevents_double_use() {
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
    let result = type_check_module_with_mode(&module, Mode::Linear);
    assert!(result.is_err(), "Linear mode should prevent double-use");
}

#[test]
fn test_linear_all_resources_consumed() {
    let code = r#"
fn test(_unit: ()): I32 =
    region r {
        let s1 = String.new@r("first") in
        let s2 = String.new@r("second") in
        let s3 = String.new@r("third") in
        let _ = drop(s1) in
        let _ = drop(s2) in
        let _ = drop(s3) in
        100
    }
"#;

    let module = parse_module(code, "test").expect("parse failed");
    let result = type_check_module_with_mode(&module, Mode::Linear);
    assert!(result.is_ok(), "Linear mode should accept all resources consumed");
}

#[test]
fn test_linear_borrow_then_drop() {
    let code = r#"
fn test(_unit: ()): I32 =
    region r {
        let s = String.new@r("test") in
        let len = String.len(&s) in
        let _ = drop(s) in
        len
    }
"#;

    let module = parse_module(code, "test").expect("parse failed");
    let result = type_check_module_with_mode(&module, Mode::Linear);
    assert!(result.is_ok(), "Linear mode should allow borrow then drop");
}

#[test]
fn test_linear_multiple_borrows() {
    let code = r#"
fn test(_unit: ()): I32 =
    region r {
        let s = String.new@r("test") in
        let len1 = String.len(&s) in
        let len2 = String.len(&s) in
        let len3 = String.len(&s) in
        let _ = drop(s) in
        len1 + len2 + len3
    }
"#;

    let module = parse_module(code, "test").expect("parse failed");
    let result = type_check_module_with_mode(&module, Mode::Linear);
    assert!(result.is_ok(), "Linear mode should allow multiple borrows then drop");
}

#[test]
fn test_linear_conditional_both_branches_drop() {
    let code = r#"
fn test(flag: Bool): I32 =
    region r {
        let s = String.new@r("data") in
        let result = if flag then
            let len = String.len(&s) in
            len
        else
            0
        in
        let _ = drop(s) in
        result
    }
"#;

    let module = parse_module(code, "test").expect("parse failed");
    let result = type_check_module_with_mode(&module, Mode::Linear);
    assert!(result.is_ok(), "Linear mode should accept drop after conditional");
}

#[test]
fn test_linear_nested_regions_all_dropped() {
    let code = r#"
fn test(_unit: ()): I32 =
    region r1 {
        let s1 = String.new@r1("outer") in
        let result = region r2 {
            let s2 = String.new@r2("inner") in
            let _ = drop(s2) in
            42
        } in
        let _ = drop(s1) in
        result
    }
"#;

    let module = parse_module(code, "test").expect("parse failed");
    let result = type_check_module_with_mode(&module, Mode::Linear);
    assert!(result.is_ok(), "Linear mode should accept nested regions with all drops");
}

#[test]
fn test_linear_partial_cleanup_fails() {
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
    let result = type_check_module_with_mode(&module, Mode::Linear);
    assert!(result.is_err(), "Linear mode should reject partial cleanup");
}
