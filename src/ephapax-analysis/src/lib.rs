// SPDX-License-Identifier: PMPL-1.0-or-later
// Static analysis passes for Ephapax compiler optimization

pub mod escape;
pub mod free_vars;
pub mod liveness;

pub use escape::{EscapeAnalysis, EscapeInfo};
pub use free_vars::{FreeVarAnalysis, FreeVars};
pub use liveness::{LivenessAnalysis, LiveVars};

/// Optimization result: variables that must be captured by closures
#[derive(Debug, Clone)]
pub struct CaptureSet {
    /// Variables that must be captured (free and escaping)
    pub must_capture: Vec<String>,
    /// Variables that could be optimized away
    pub can_elide: Vec<String>,
}

/// Combined analysis for closure optimization
pub fn analyze_closure_captures(
    lambda_body: &ephapax_syntax::Expr,
    scope_vars: &[String],
) -> CaptureSet {
    // Step 1: Find free variables in lambda body
    let free_vars = FreeVarAnalysis::analyze(lambda_body);

    // Step 2: Perform escape analysis
    let escape_info = EscapeAnalysis::analyze(lambda_body);

    // Step 3: Compute minimal capture set
    let mut must_capture = Vec::new();
    let mut can_elide = Vec::new();

    for var in scope_vars {
        if free_vars.is_free(var) {
            if escape_info.escapes(var) {
                must_capture.push(var.clone());
            } else {
                // Free but doesn't escape - can be stack-allocated
                can_elide.push(var.clone());
            }
        } else {
            // Not free - definitely can elide
            can_elide.push(var.clone());
        }
    }

    CaptureSet {
        must_capture,
        can_elide,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ephapax_syntax::*;

    #[test]
    fn test_minimal_capture() {
        // λ(x) -> x + c  (only captures c, not a or b)
        // Represented as: Expr::Lambda with body using 'c'

        // For now, this is a placeholder test
        // Real implementation requires full AST construction
        let scope_vars = vec!["a".to_string(), "b".to_string(), "c".to_string()];

        // Would need actual lambda expression here
        // For demonstration, assume we have a lambda that only uses 'c'

        // Expected: must_capture = ["c"], can_elide = ["a", "b"]
    }
}
