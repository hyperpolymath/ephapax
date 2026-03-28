// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Integration tests: parse -> type-check pipeline
//!
//! Tests the full pipeline from source text to type-checked AST.
//! Each test parses Ephapax source and verifies the type checker accepts/rejects it.

use ephapax_parser::parse;
use ephapax_typing::TypeChecker;

/// Helper: parse and type-check, returning the result type
fn check(source: &str) -> Result<ephapax_syntax::Ty, String> {
    let expr = parse(source).map_err(|es| {
        es.into_iter()
            .map(|e| format!("{e}"))
            .collect::<Vec<_>>()
            .join("; ")
    })?;
    let mut tc = TypeChecker::new();
    tc.check(&expr).map_err(|e| format!("{e:?}"))
}

/// Helper: assert that source type-checks successfully
fn assert_checks(source: &str) {
    match check(source) {
        Ok(_) => {}
        Err(e) => panic!("Expected type-check success for `{source}`, got: {e}"),
    }
}

/// Helper: assert that source fails type-checking
fn assert_rejects(source: &str) {
    match check(source) {
        Ok(ty) => panic!("Expected type-check failure for `{source}`, got: {ty:?}"),
        Err(_) => {}
    }
}

// =========================================================================
// Basic expressions
// =========================================================================

#[test]
fn int_literal() {
    assert_checks("42");
}

#[test]
fn bool_literal() {
    assert_checks("true");
}

#[test]
fn unit_literal() {
    assert_checks("()");
}

#[test]
fn simple_let() {
    assert_checks("let x = 42 in x");
}

#[test]
fn nested_let() {
    assert_checks("let x = 1 in let y = 2 in x");
}

#[test]
fn lambda_identity() {
    assert_checks("fn(x: I32) -> x");
}

#[test]
fn lambda_application() {
    assert_checks("(fn(x: I32) -> x)(42)");
}

// =========================================================================
// Pairs
// =========================================================================

#[test]
fn pair_construction() {
    assert_checks("(1, 2)");
}

// fst/snd not yet in parser grammar — tested at AST level in ephapax-typing

// =========================================================================
// Conditionals
// =========================================================================

#[test]
fn if_expression() {
    assert_checks("if true then 1 else 2");
}

#[test]
fn if_branch_type_mismatch() {
    assert_rejects("if true then 1 else true");
}

// =========================================================================
// Linear types — let! must consume
// =========================================================================

#[test]
fn let_bang_consumed() {
    assert_checks("let! x = 42 in x");
}

#[test]
fn let_bang_unconsumed_rejected() {
    assert_rejects("let! x = 42 in 0");
}

// =========================================================================
// Functions with linear bindings
// =========================================================================

#[test]
fn lambda_uses_param() {
    assert_checks("fn(x: I32) -> x");
}

// =========================================================================
// Sums
// =========================================================================

#[test]
fn inl_expression() {
    assert_checks("inl[I32](true)");
}

#[test]
fn inr_expression() {
    assert_checks("inr[Bool](42)");
}

// =========================================================================
// Drop and Copy
// =========================================================================

#[test]
fn drop_expression() {
    assert_rejects("drop(42)"); // I32 is not linear — drop rejected
}

#[test]
fn copy_expression() {
    assert_checks("copy(42)"); // I32 is not linear — copy allowed
}

// =========================================================================
// Parse errors
// =========================================================================

#[test]
fn parse_error_incomplete() {
    assert!(parse("let x =").is_err());
}

#[test]
fn parse_error_invalid_token() {
    assert!(parse("@@@").is_err());
}

// =========================================================================
// End-to-end pipeline
// =========================================================================

#[test]
fn pipeline_complex_expression() {
    // Parse -> type-check a moderately complex expression
    let source = "let f = fn(x: I32) -> x in f(42)";
    assert_checks(source);
}

#[test]
fn pipeline_nested_pairs() {
    assert_checks("let p = (1, (2, 3)) in p");
}
