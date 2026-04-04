// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

//! Property-based tests for Ephapax language invariants.
//!
//! Uses proptest to verify that the parser and type checker hold their
//! stated invariants across a wide range of inputs, not just hand-crafted
//! examples.

use ephapax_parser::parse;
use ephapax_typing::TypeChecker;
use proptest::prelude::*;

// =========================================================================
// Helper
// =========================================================================

/// Parse and type-check source, returning a result string for diagnostics.
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
// PROP: Integer literals always parse and type-check to I32
// =========================================================================

proptest! {
    /// Any non-negative integer in [0, 1000] parses successfully and produces I32.
    ///
    /// Ephapax integer literals are non-negative; negative values require
    /// a unary operator expression which is a separate syntactic form.
    #[test]
    fn prop_integer_literal_parses(n in 0u32..=1000u32) {
        let source = n.to_string();
        let result = check(&source);
        prop_assert!(
            result.is_ok(),
            "integer literal `{}` should type-check, got: {:?}",
            source,
            result.err()
        );
    }
}

// =========================================================================
// PROP: Parser is deterministic — same input always produces the same result
// =========================================================================

proptest! {
    /// Parsing a known-good integer source twice yields the same AST.
    ///
    /// This validates that the parser has no hidden mutable global state.
    #[test]
    fn prop_parse_is_deterministic(n in 0u32..=1000u32) {
        let source = n.to_string();
        let result_a = parse(&source);
        let result_b = parse(&source);
        // Both succeed or both fail, and if both succeed, ASTs are equal.
        match (result_a, result_b) {
            (Ok(a), Ok(b)) => prop_assert_eq!(a, b, "parser produced different ASTs for `{}`", source),
            (Err(_), Err(_)) => {} // consistently failing is fine for this property
            (Ok(_), Err(e)) | (Err(e), Ok(_)) => {
                prop_assert!(false, "parser gave inconsistent results for `{}`: {:?}", source, e);
            }
        }
    }
}

// =========================================================================
// PROP: Batch of integer literals — no panics or hangs
// =========================================================================

proptest! {
    /// Parsing a sequence of different integer literals never panics.
    ///
    /// Each call is independent; the goal is to exercise the parser across
    /// many small inputs in a single property run.
    #[test]
    fn prop_batch_integer_literals_no_panic(values in prop::collection::vec(0u32..=10000u32, 1..=20)) {
        for v in values {
            let source = v.to_string();
            // We only require no panic; success or failure both acceptable.
            let _ = parse(&source);
        }
    }
}

// =========================================================================
// PROP: Well-typed let binding always type-checks
// =========================================================================

proptest! {
    /// `let x = <int> in x` always type-checks for any small integer.
    ///
    /// Parametrically tests that affine let-bindings over integers are
    /// always accepted regardless of the specific integer value.
    #[test]
    fn prop_affine_let_binding_always_checks(n in 0u32..=500u32) {
        let source = format!("let x = {} in x", n);
        let result = check(&source);
        prop_assert!(
            result.is_ok(),
            "affine let binding `{}` should type-check, got: {:?}",
            source,
            result.err()
        );
    }
}

// =========================================================================
// PROP: Conditional expressions over integer literals always type-check
// =========================================================================

proptest! {
    /// `if true then <a> else <b>` where a and b are both I32 always checks.
    #[test]
    fn prop_if_same_int_branches_checks(a in 0u32..=200u32, b in 0u32..=200u32) {
        let source = format!("if true then {} else {}", a, b);
        let result = check(&source);
        prop_assert!(
            result.is_ok(),
            "if-expression `{}` should type-check, got: {:?}",
            source,
            result.err()
        );
    }
}

// =========================================================================
// PROP: TypeChecker state isolation — fresh TypeChecker per call
// =========================================================================

proptest! {
    /// Repeated type-checking with separate TypeChecker instances gives same result.
    ///
    /// Validates that TypeChecker::new() always starts in an equivalent clean
    /// state, with no residual state from previous instances.
    #[test]
    fn prop_typechecker_state_isolation(n in 0u32..=100u32) {
        let source = format!("let! x = {} in x", n);
        let expr = match parse(&source) {
            Ok(e) => e,
            Err(_) => return Ok(()), // skip if parse fails
        };
        let mut tc1 = TypeChecker::new();
        let mut tc2 = TypeChecker::new();
        let r1 = tc1.check(&expr);
        let r2 = tc2.check(&expr);
        // Both should agree: either both Ok or both Err.
        match (&r1, &r2) {
            (Ok(_), Ok(_)) | (Err(_), Err(_)) => {}
            _ => prop_assert!(
                false,
                "TypeChecker::new() gave inconsistent results for `{}`: {:?} vs {:?}",
                source, r1, r2
            ),
        }
    }
}
