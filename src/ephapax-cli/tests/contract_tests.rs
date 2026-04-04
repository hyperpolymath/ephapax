// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)

//! Contract and invariant tests for the Ephapax type system.
//!
//! These tests encode hard invariants that MUST hold for the compiler to
//! be correct.  Unlike unit tests (which verify specific behaviours), these
//! tests verify _properties_ that should be unconditionally true of the
//! system at all times.
//!
//! Invariants encoded here:
//! 1. Empty programs are always rejected.
//! 2. Well-typed programs that pass type-checking produce non-empty WASM.
//! 3. Parsing is deterministic for the same source string.
//! 4. TypeChecker never leaks state between independent invocations.
//! 5. Unused linear (let!) bindings are always rejected (linearity enforcement).
//! 6. Ill-typed programs are rejected at the type-check phase, not the parse phase.
//! 7. Reflexive parse: parsing "42" twice gives equal ASTs.

use ephapax_parser::parse;
use ephapax_typing::TypeChecker;
use ephapax_wasm::Codegen;

// =========================================================================
// Helper: parse and type-check returning a diagnostic string on error
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
// INVARIANT 1: Empty programs are always rejected
// =========================================================================

/// An empty source string must never produce a valid expression.
///
/// The parser must enforce that every program has at least one top-level
/// expression.  Accepting the empty string would make the grammar ambiguous.
#[test]
fn invariant_empty_program_rejected() {
    assert!(
        parse("").is_err(),
        "INVARIANT VIOLATED: empty source must be rejected by the parser"
    );
}

// =========================================================================
// INVARIANT 2: Well-typed programs produce non-empty WASM bytes
// =========================================================================

/// If a program passes both parse and type-check, codegen must produce a
/// non-empty byte sequence that begins with the WASM magic header.
///
/// A zero-length or header-less output would indicate a codegen bug that
/// could silently produce invalid modules.
#[test]
fn invariant_well_typed_program_produces_valid_wasm() {
    let source = "let x = 42 in x";
    let expr = parse(source).expect("parse must succeed for well-typed source");
    let mut tc = TypeChecker::new();
    tc.check(&expr).expect("type-check must succeed");
    let mut codegen = Codegen::new();
    let wasm_bytes = codegen.compile_program(&expr);

    assert!(
        !wasm_bytes.is_empty(),
        "INVARIANT VIOLATED: well-typed program must produce non-empty WASM"
    );
    assert_eq!(
        &wasm_bytes[0..4],
        b"\x00asm",
        "INVARIANT VIOLATED: WASM output must start with magic bytes"
    );
}

// =========================================================================
// INVARIANT 3: Parsing is deterministic
// =========================================================================

/// Calling `parse` twice with the same source must produce identical ASTs.
///
/// The parser must be a pure function of its input — no global mutable
/// state, no randomisation, no ordering dependence.
#[test]
fn invariant_parse_is_deterministic() {
    let sources = [
        "42",
        "true",
        "()",
        "let x = 1 in x",
        "fn(x: I32) -> x",
        "(1, 2)",
    ];
    for source in sources {
        let a = parse(source).expect("first parse must succeed");
        let b = parse(source).expect("second parse must succeed");
        assert_eq!(
            a, b,
            "INVARIANT VIOLATED: parsing `{source}` gave different results on two calls"
        );
    }
}

// =========================================================================
// INVARIANT 4: TypeChecker has no state leakage between invocations
// =========================================================================

/// Two independent TypeChecker instances, each checking the same program,
/// must produce the same result.
///
/// This guards against accidental singleton state, static variables, or
/// shared mutable context that would make type-checking non-deterministic.
#[test]
fn invariant_typechecker_no_state_leakage() {
    let programs = [
        ("let x = 42 in x", true),
        ("let! x = 42 in x", true),
        ("let! x = 42 in 0", false), // unused linear — must be rejected
        ("if true then 1 else 2", true),
        ("x", false), // unbound variable — must be rejected
    ];

    for (source, expect_ok) in programs {
        let expr = match parse(source) {
            Ok(e) => e,
            Err(_) if !expect_ok => continue, // parse error is also a rejection
            Err(e) => panic!("parse failed unexpectedly for `{source}`: {e:?}"),
        };

        let r1 = TypeChecker::new().check(&expr);
        let r2 = TypeChecker::new().check(&expr);

        match (&r1, &r2) {
            (Ok(_), Ok(_)) => assert!(
                expect_ok,
                "INVARIANT VIOLATED: `{source}` should be rejected but was accepted"
            ),
            (Err(_), Err(_)) => assert!(
                !expect_ok,
                "INVARIANT VIOLATED: `{source}` should be accepted but was rejected"
            ),
            (Ok(_), Err(e)) | (Err(e), Ok(_)) => panic!(
                "INVARIANT VIOLATED: TypeChecker gave inconsistent results for `{source}`: {:?}",
                e
            ),
        }
    }
}

// =========================================================================
// INVARIANT 5: Linearity is enforced — unused linear bindings rejected
// =========================================================================

/// A `let!` binding that is not consumed in the body must be rejected.
///
/// This is the core invariant of the linear type system: linear resources
/// must be used exactly once.  Any weakening of this would break the
/// soundness proof.
#[test]
fn invariant_unused_linear_binding_rejected() {
    assert!(
        check("let! x = 42 in 0").is_err(),
        "INVARIANT VIOLATED: unused linear binding must be rejected (linearity enforcement)"
    );
}

/// A `let!` binding that IS consumed must be accepted.
///
/// Verifies that the linear check is not over-eager — it should accept
/// valid uses of linear bindings.
#[test]
fn invariant_consumed_linear_binding_accepted() {
    assert!(
        check("let! x = 42 in x").is_ok(),
        "INVARIANT VIOLATED: consumed linear binding must be accepted"
    );
}

/// Multiple linear bindings — each must be consumed in the body.
#[test]
fn invariant_nested_linear_bindings_both_consumed() {
    // Both x and y consumed: valid
    assert!(
        check("let! x = 1 in let! y = 2 in (x, y)").is_ok(),
        "INVARIANT VIOLATED: nested linear bindings both consumed must be accepted"
    );
}

/// Partially consuming nested linear bindings must be rejected.
#[test]
fn invariant_nested_linear_bindings_one_unconsumed_rejected() {
    // y is not consumed: invalid
    assert!(
        check("let! x = 1 in let! y = 2 in x").is_err(),
        "INVARIANT VIOLATED: unconsumed inner linear binding must be rejected"
    );
}

// =========================================================================
// INVARIANT 6: Type errors are rejected at type-check phase, not parse phase
// =========================================================================

/// A program that is syntactically valid but ill-typed must parse successfully
/// and fail only during type-checking.
///
/// Blurring parse errors and type errors would give misleading diagnostics
/// to users and break downstream tooling (LSP, REPL) that distinguishes the
/// two phases.
#[test]
fn invariant_type_error_is_typecheck_phase_not_parse_phase() {
    let ill_typed_programs = [
        "if true then 1 else true",    // branch type mismatch
        "(fn(x: I32) -> x)(true)",     // argument type mismatch
        "x",                           // unbound variable
        "let! x = 42 in 0",            // unused linear binding
    ];

    for source in ill_typed_programs {
        let parse_result = parse(source);
        assert!(
            parse_result.is_ok(),
            "INVARIANT VIOLATED: `{source}` should parse successfully \
             (syntax is valid even if type is wrong), got parse error"
        );

        // Now confirm the type checker rejects it.
        let expr = parse_result.unwrap();
        let tc_result = TypeChecker::new().check(&expr);
        assert!(
            tc_result.is_err(),
            "INVARIANT VIOLATED: `{source}` should be rejected by type checker"
        );
    }
}

// =========================================================================
// INVARIANT 7: Error messages are non-empty strings
// =========================================================================

/// A parse error must produce a non-empty diagnostic string.
///
/// Silent errors or empty error strings make the compiler unusable for
/// interactive development.
#[test]
fn invariant_parse_error_messages_are_non_empty() {
    let bad_sources = ["let x =", "@@@", "fn(x:) -> x"];
    for source in bad_sources {
        let errors = parse(source).expect_err(&format!("`{source}` should fail to parse"));
        assert!(
            !errors.is_empty(),
            "INVARIANT VIOLATED: parse(`{source}`) returned empty error list"
        );
        for e in &errors {
            let msg = format!("{e}");
            assert!(
                !msg.is_empty(),
                "INVARIANT VIOLATED: error message for `{source}` is empty string"
            );
        }
    }
}

/// A type error must produce a non-empty diagnostic string.
#[test]
fn invariant_type_error_messages_are_non_empty() {
    // Unbound variable — guaranteed type error
    let source = "x";
    let expr = parse(source).expect("should parse");
    let err = TypeChecker::new()
        .check(&expr)
        .expect_err("should fail to type-check");
    let msg = format!("{err:?}");
    assert!(
        !msg.is_empty(),
        "INVARIANT VIOLATED: type error message for `{source}` is empty string"
    );
}

// =========================================================================
// REFLEXIVE tests
// =========================================================================

/// Parsing "42" twice gives equal ASTs (reflexive parse).
#[test]
fn reflexive_parse_integer() {
    let a = parse("42").expect("parse must succeed");
    let b = parse("42").expect("parse must succeed");
    assert_eq!(a, b, "reflexive parse: same source must give equal ASTs");
}

/// Parsing "let x = 1 in x" twice gives equal ASTs.
#[test]
fn reflexive_parse_let_binding() {
    let a = parse("let x = 1 in x").expect("parse must succeed");
    let b = parse("let x = 1 in x").expect("parse must succeed");
    assert_eq!(a, b, "reflexive parse: same source must give equal ASTs");
}

/// TypeChecker::new() always starts in a valid initial state.
///
/// Validated by checking that a simple known-good program is accepted
/// immediately after construction, without any warm-up or initialization.
#[test]
fn reflexive_typechecker_new_is_valid_initial_state() {
    let expr = parse("42").expect("parse must succeed");
    // Three fresh TypeCheckers all agree on the same simple program.
    for _ in 0..3 {
        TypeChecker::new()
            .check(&expr)
            .expect("fresh TypeChecker must accept well-typed program immediately");
    }
}
