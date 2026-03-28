// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! JSON AST dump for Ephapax.
//!
//! Provides JSON serialization of the Ephapax AST, complementing the
//! S-expression representation in the parent module. The JSON output
//! mirrors the same structural encoding — modules, declarations,
//! expressions, types — but in a format consumable by standard JSON
//! tooling, language servers, and external analysis pipelines.

use ephapax_syntax::{Expr, Module};

/// Serialize a parsed [`Module`] to a pretty-printed JSON string.
///
/// The output structure mirrors the S-expression encoding:
/// ```json
/// {
///   "name": "example",
///   "decls": [
///     { "kind": "fn", "name": "main", "params": [], ... }
///   ]
/// }
/// ```
///
/// # Errors
///
/// Returns an error string if serde serialization fails (should not
/// happen for well-formed AST nodes).
pub fn module_to_json(module: &Module) -> Result<String, String> {
    serde_json::to_string_pretty(module).map_err(|e| format!("JSON serialization error: {}", e))
}

/// Serialize a parsed [`Module`] to a compact (single-line) JSON string.
///
/// Useful for piping into other tools where human readability is not
/// required.
///
/// # Errors
///
/// Returns an error string if serde serialization fails.
pub fn module_to_json_compact(module: &Module) -> Result<String, String> {
    serde_json::to_string(module).map_err(|e| format!("JSON serialization error: {}", e))
}

/// Serialize a single [`Expr`] to a pretty-printed JSON string.
///
/// Useful for the `parse` subcommand when a single expression (rather
/// than a full module) is provided.
///
/// # Errors
///
/// Returns an error string if serde serialization fails.
pub fn expr_to_json(expr: &Expr) -> Result<String, String> {
    serde_json::to_string_pretty(expr).map_err(|e| format!("JSON serialization error: {}", e))
}

/// Serialize a single [`Expr`] to a compact JSON string.
///
/// # Errors
///
/// Returns an error string if serde serialization fails.
pub fn expr_to_json_compact(expr: &Expr) -> Result<String, String> {
    serde_json::to_string(expr).map_err(|e| format!("JSON serialization error: {}", e))
}

#[cfg(test)]
mod tests {
    use super::*;
    use ephapax_syntax::{
        BaseTy, Decl, Expr, ExprKind, Literal, Module, Span, Ty, Visibility,
    };
    use smol_str::SmolStr;

    /// Verify that a minimal module round-trips through JSON without
    /// panicking and produces valid JSON containing expected fields.
    #[test]
    fn module_json_contains_expected_fields() {
        let module = Module {
            name: SmolStr::new("test_mod"),
            imports: vec![],
            decls: vec![Decl::Fn {
                name: SmolStr::new("main"),
                visibility: Visibility::Private,
                type_params: vec![],
                params: vec![],
                ret_ty: Ty::Base(BaseTy::I32),
                body: Expr {
                    kind: ExprKind::Lit(Literal::I32(42)),
                    span: Span::new(0, 10),
                },
            }],
        };

        let json = module_to_json(&module).expect("serialization should succeed");

        // Verify it is valid JSON by parsing it back
        let parsed: serde_json::Value =
            serde_json::from_str(&json).expect("output should be valid JSON");

        assert_eq!(parsed["name"], "test_mod");
        assert!(parsed["decls"].is_array());
        assert_eq!(parsed["decls"][0]["kind"], "fn");
        assert_eq!(parsed["decls"][0]["name"], "main");
    }

    /// Verify compact output produces valid single-line JSON.
    #[test]
    fn compact_json_is_single_line() {
        let module = Module {
            name: SmolStr::new("m"),
            imports: vec![],
            decls: vec![],
        };

        let json = module_to_json_compact(&module).expect("serialization should succeed");
        assert!(!json.contains('\n'), "compact JSON should be a single line");

        let parsed: serde_json::Value =
            serde_json::from_str(&json).expect("output should be valid JSON");
        assert_eq!(parsed["name"], "m");
    }

    /// Verify that a standalone expression serializes correctly.
    #[test]
    fn expr_json_literal() {
        let expr = Expr::dummy(ExprKind::Lit(Literal::Bool(true)));
        let json = expr_to_json(&expr).expect("serialization should succeed");

        let parsed: serde_json::Value =
            serde_json::from_str(&json).expect("output should be valid JSON");

        // The ExprKind is tagged — check the node discriminator
        assert_eq!(parsed["kind"]["node"], "lit");
    }
}
