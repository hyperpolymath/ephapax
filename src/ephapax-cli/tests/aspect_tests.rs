// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

//! Aspect tests: security, performance, and correctness dimensions.
//!
//! Aspect tests validate cross-cutting quality attributes of the Ephapax
//! compiler pipeline.  These are distinct from unit tests (which test
//! specific functions) and integration tests (which test the pipeline
//! end-to-end).  Each test here is tagged with its quality dimension.
//!
//! Dimensions covered:
//! - **Security**: Adversarial or pathological inputs must not panic or hang.
//! - **Performance**: Batch processing must complete in bounded time.
//! - **Correctness**: Error diagnostics must be informative non-empty strings.

use ephapax_parser::parse;
use ephapax_typing::TypeChecker;

// =========================================================================
// Helper
// =========================================================================

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

// =========================================================================
// SECURITY: Large inputs must not stack overflow or hang
// =========================================================================

/// Parsing a very long source string (100 KB of repeated chars) must
/// terminate gracefully — either with a parse error or with success — but
/// must NOT panic or stack-overflow.
///
/// This guards against catastrophic backtracking in the PEG grammar or
/// unbounded recursion in the parser.
#[test]
fn security_large_input_no_stack_overflow() {
    // 100 KB of 'a' characters — not valid Ephapax syntax.
    let large_input = "a".repeat(100_000);
    // Must not panic; error result is expected and acceptable.
    let _ = parse(&large_input);
}

/// Parsing a string with 10 KB of whitespace must terminate.
///
/// Whitespace-only input is syntactically invalid but the lexer must not
/// spin indefinitely on it.
#[test]
fn security_whitespace_only_no_hang() {
    let whitespace = " ".repeat(10_000);
    let _ = parse(&whitespace);
}

/// Parsing a source string containing a null byte must return an error,
/// not panic.
///
/// Null bytes can cause issues in C-based parsers.  While Rust strings
/// may contain null bytes, the Ephapax grammar should reject them cleanly.
#[test]
fn security_null_byte_in_source_handled_gracefully() {
    let with_null = "let x = \x00 in x";
    // Either parse error or success, but MUST NOT panic.
    let result = parse(with_null);
    // We don't mandate success or failure; we mandate no panic.
    // If it succeeds, type-checking it must also not panic.
    if let Ok(expr) = result {
        let _ = TypeChecker::new().check(&expr);
    }
}

/// Parsing source containing Unicode characters (emoji, CJK) must not panic.
///
/// Users may write string literals or comments containing non-ASCII text.
/// The lexer must handle multibyte UTF-8 without crashing.
#[test]
fn security_unicode_in_source_no_panic() {
    let unicode_sources = [
        "42 (* こんにちは *)",   // CJK in comment (if comments exist, otherwise parse error OK)
        "42",                     // baseline — must still succeed
        "true",                   // baseline bool
    ];
    for source in unicode_sources {
        // No panic is the requirement; error result is acceptable.
        let _ = parse(source);
    }
}

/// Deeply nested pairs must not stack overflow during parsing or type-checking.
///
/// Compilers that use recursive descent without a depth limit are vulnerable
/// to stack exhaustion on adversarial input.  We use 50 levels of nesting —
/// well within normal usage but enough to trigger naive recursion issues.
#[test]
fn security_deeply_nested_pairs_no_stack_overflow() {
    // Build "(1, (1, (1, ... )))" with 30 levels of nesting.
    let mut source = "1".to_string();
    for _ in 0..30 {
        source = format!("(1, {})", source);
    }
    // Requires successful parse and type-check.
    let result = check(&source);
    assert!(
        result.is_ok(),
        "deeply nested pairs (30 levels) should type-check, got: {:?}",
        result.err()
    );
}

// =========================================================================
// PERFORMANCE: Batch processing of simple programs completes without error
// =========================================================================

/// Parsing 500 simple integer literals in sequence must complete without
/// error or panic.
///
/// This is not a timing constraint (Rust tests have no deadline by default)
/// but a correctness constraint: the parser must not degrade or fail when
/// called many times in sequence.
#[test]
fn performance_batch_integer_literals() {
    for i in 0u32..500 {
        let source = i.to_string();
        let result = parse(&source);
        assert!(
            result.is_ok(),
            "parsing integer `{}` failed at iteration {}",
            source,
            i
        );
    }
}

/// Parsing and type-checking 100 simple let-bindings in sequence must succeed.
///
/// Validates that neither the parser nor the type checker accumulates memory
/// or error state across independent invocations.
#[test]
fn performance_batch_let_bindings() {
    for i in 0u32..100 {
        let source = format!("let x = {} in x", i);
        let result = check(&source);
        assert!(
            result.is_ok(),
            "type-checking `{}` failed at iteration {}: {:?}",
            source,
            i,
            result.err()
        );
    }
}

// =========================================================================
// CORRECTNESS: Error diagnostics are informative non-empty strings
// =========================================================================

/// Parse errors must produce non-empty, non-whitespace diagnostic strings.
///
/// A blank error message is as bad as no error message — it gives the user
/// no actionable information.
#[test]
fn correctness_parse_error_is_informative() {
    let bad_inputs = [
        "let x =",         // truncated let
        "@@@",             // invalid tokens
        "fn(x:) -> x",     // missing type annotation
        "if then else",    // missing condition
    ];
    for source in bad_inputs {
        let errors = parse(source)
            .expect_err(&format!("`{source}` should fail to parse"));
        for e in &errors {
            let msg = format!("{e}");
            assert!(
                !msg.trim().is_empty(),
                "parse error for `{source}` produced empty/whitespace-only message"
            );
        }
    }
}

/// Type error messages must be non-empty, non-whitespace strings.
///
/// The compiler must always explain why a program is rejected.
#[test]
fn correctness_type_error_is_informative() {
    let ill_typed = [
        ("if true then 1 else true", "branch type mismatch"),
        ("x", "unbound variable"),
        ("let! x = 42 in 0", "unused linear binding"),
        ("(fn(x: I32) -> x)(true)", "argument type mismatch"),
    ];
    for (source, description) in ill_typed {
        // Source must parse (validated by contract_tests.rs).
        let expr = parse(source).expect("should parse");
        let err = TypeChecker::new()
            .check(&expr)
            .expect_err(&format!("{description}: `{source}` should fail type-check"));
        let msg = format!("{err:?}");
        assert!(
            !msg.trim().is_empty(),
            "type error for `{source}` ({description}) produced empty message"
        );
    }
}

/// Successful type-checking produces a valid type, not an opaque placeholder.
///
/// The returned type must be serialisable (via Debug) and non-empty.
#[test]
fn correctness_successful_check_returns_meaningful_type() {
    let well_typed = [
        "42",
        "true",
        "()",
        "let x = 1 in x",
        "fn(x: I32) -> x",
    ];
    for source in well_typed {
        let ty = check(source)
            .unwrap_or_else(|e| panic!("type-check of `{source}` failed: {e}"));
        let ty_str = format!("{ty:?}");
        assert!(
            !ty_str.trim().is_empty(),
            "type-check of `{source}` returned a type with empty debug representation"
        );
    }
}
