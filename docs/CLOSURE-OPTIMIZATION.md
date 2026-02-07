# Closure Environment Optimization

**Status**: Framework implemented, full optimization pending

This document describes the closure optimization system for Ephapax, which reduces WASM binary size by minimizing closure capture environments.

## Problem

Without optimization, lambdas capture their **entire enclosing environment**:

```ephapax
fn outer(a: I32, b: I32, c: I32, d: I32): (I32 -> I32) =
    let unused = a + b in
    λ(x: I32) -> x + c  // Only uses `c`, but captures a, b, c, d, unused
```

Result: 20 bytes captured (5 variables × 4 bytes), even though only 4 bytes are needed.

## Solution

**Escape analysis** + **free variable analysis** to capture only necessary variables:

```ephapax
// After optimization: only captures `c` (4 bytes)
λ(x: I32) -> x + c  // Captures: {c}
```

## Architecture

### Analysis Crate: `ephapax-analysis`

Three analysis passes:

1. **Free Variable Analysis** (`free_vars.rs`)
   - Identifies variables referenced in lambda body
   - Excludes lambda parameters
   - Returns: `Set<VarName>`

2. **Escape Analysis** (`escape.rs`)
   - Determines if variables escape their scope
   - Variables escape if:
     - Captured by a lambda
     - Returned from a function
     - Passed to a function that stores them
   - Returns: `Set<VarName>`

3. **Liveness Analysis** (`liveness.rs`)
   - Determines which variables are live at each program point
   - Used for dead code elimination
   - Returns: `Set<VarName>` at each point

### Minimal Capture Set

```rust
pub fn analyze_closure_captures(
    lambda_body: &Expr,
    scope_vars: &[String],
) -> CaptureSet {
    let free_vars = FreeVarAnalysis::analyze(lambda_body);
    let escape_info = EscapeAnalysis::analyze(lambda_body);

    let must_capture = scope_vars.iter()
        .filter(|var| free_vars.is_free(var) && escape_info.escapes(var))
        .cloned()
        .collect();

    CaptureSet { must_capture, ... }
}
```

## Integration with Codegen

### Current Implementation (Placeholder)

```rust
// In ephapax-wasm/src/lib.rs
struct Codegen {
    // ...
    optimize_closures: bool,
}

fn compile_lambda(&mut self, ...) {
    let captured_vars = self.find_free_vars(body, &bound_vars);

    if self.optimize_closures {
        // Future: Filter to minimal set using ephapax-analysis
        // Currently: Conservative (captures all free vars)
    }

    // Emit closure with capture environment...
}
```

### CLI Flag

```bash
ephapax compile program.eph --optimize-closures
```

## Expected Impact

| Metric | Before | After | Improvement |
|--------|--------|-------|-------------|
| Closure env size | 32 bytes | 8 bytes | 75% reduction |
| WASM binary size | 5.2 KB | 3.6 KB | 31% reduction |
| Heap allocations | 10 per closure | 2-3 per closure | 70% reduction |

## Testing

### Unit Tests

```rust
#[test]
fn test_minimal_capture() {
    // λ(x) -> x + c  (only captures c, not a or b)
    let scope_vars = vec!["a", "b", "c"];
    let capture_set = analyze_closure_captures(&lambda_expr, &scope_vars);

    assert_eq!(capture_set.must_capture, vec!["c"]);
    assert_eq!(capture_set.can_elide, vec!["a", "b"]);
}
```

### Integration Test

```bash
# Compile with optimization
ephapax compile closures.eph --optimize-closures -o optimized.wasm

# Measure size reduction
ls -lh closures.wasm optimized.wasm
```

## Limitations

1. **Conservative Analysis**: Currently captures all free variables
2. **No Inter-Procedural Analysis**: Doesn't track across function boundaries
3. **No Alias Analysis**: Assumes all pointers may alias

## Future Enhancements

1. **Full Escape Analysis Integration**
   - Use `ephapax-analysis` in separate compiler pass
   - Propagate escape information to codegen

2. **Closure Inlining**
   - Inline single-use closures
   - Eliminate closure allocation entirely

3. **Closure Specialization**
   - Generate specialized versions for common capture patterns
   - Zero-capture closures become plain functions

4. **Stack Allocation**
   - Allocate non-escaping closures on stack
   - Avoid heap allocation overhead

## References

- [Escape Analysis (Wikipedia)](https://en.wikipedia.org/wiki/Escape_analysis)
- [Lambda Lifting](https://en.wikipedia.org/wiki/Lambda_lifting)
- [Closure Conversion](https://matt.might.net/articles/closure-conversion/)

## Status

- ✅ Framework: Analysis crate created
- ✅ Free variable analysis implemented
- ✅ Escape analysis implemented
- ✅ Liveness analysis implemented
- ⏸️ Integration: Placeholder in codegen
- ⏸️ CLI: Flag available but not wired
- ⏸️ Testing: Unit tests for analysis passes
- ❌ Full optimization: Pending integration

**To complete**: Wire analysis results into `compile_lambda()` to actually reduce capture sets.
