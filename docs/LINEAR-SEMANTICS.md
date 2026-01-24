# Linear vs Affine Type Checking Semantics

## Overview

Ephapax supports two type disciplines:
- **Affine**: Resources used ≤1 times (can be dropped implicitly)
- **Linear**: Resources used =1 time exactly (must be consumed explicitly)

## Formal Distinction

### Type Discipline Rules

| Property | Affine | Linear |
|----------|---------|--------|
| **Weakening** | ✅ Allowed | ❌ Forbidden |
| **Contraction** | ❌ Forbidden | ❌ Forbidden |
| **Drop** | Implicit | Explicit via `drop()` |
| **Unused vars** | Warning | Error |

### Typing Judgments

**Affine:**
```
Γ ⊢ e : T   (Γ contains variables used ≤1 times)
```

**Linear:**
```
Γ ⊢ e : T ⊸ Δ   (Γ input context, Δ output context)
                 (All vars in Γ consumed, Δ contains remaining linear vars)
```

## Core Differences

### 1. Variable Usage

**Affine:**
```ephapax
fn example_affine() -> i32 {
    let x = alloc(42);  // Affine resource
    // x is silently dropped here - OK
    5
}
```

**Linear:**
```ephapax
fn example_linear() -> i32 {
    let! x = alloc(42);  // Linear resource
    // ERROR: x not consumed
    5
}

fn example_linear_correct() -> i32 {
    let! x = alloc(42);
    drop(x);  // Explicit consumption required
    5
}
```

### 2. Let Bindings

**Affine let:**
```
Γ ⊢ e₁ : T₁    Γ, x:T₁ ⊢ e₂ : T₂
─────────────────────────────────  (Let-Affine)
Γ ⊢ let x = e₁ in e₂ : T₂

Note: x may or may not be used in e₂
```

**Linear let:**
```
Γ₁ ⊢ e₁ : T₁ ⊸ Γ₂    Γ₂, x:T₁ ⊢ e₂ : T₂ ⊸ Γ₃    x ∈ consumed(e₂)
──────────────────────────────────────────────────────────────────  (Let-Linear)
Γ₁ ⊢ let! x = e₁ in e₂ : T₂ ⊸ Γ₃

Note: x MUST be used exactly once in e₂
```

### 3. Conditionals

**Affine:**
```ephapax
fn affine_branch(cond: bool) -> i32 {
    let x = alloc(42);
    if cond {
        use(x)  // x consumed in then-branch
    } else {
        5       // x dropped in else-branch - OK
    }
}
```

**Linear:**
```ephapax
fn linear_branch(cond: bool) -> i32 {
    let! x = alloc(42);
    if cond {
        use(x)     // x consumed in then-branch
    } else {
        drop(x);   // x MUST be consumed in else-branch too
        5
    }
}
```

**Typing rule:**
```
Γ ⊢ e_cond : Bool    Γ₁ ⊢ e_then : T ⊸ Γ₂    Γ₁ ⊢ e_else : T ⊸ Γ₃    Γ₂ = Γ₃
─────────────────────────────────────────────────────────────────────────────────  (If-Linear)
Γ ⊢ if e_cond { e_then } else { e_else } : T ⊸ Γ₂

Note: Both branches must consume the same linear variables (Γ₂ = Γ₃)
```

### 4. Function Application

**Affine:**
```
Γ ⊢ f : T₁ → T₂    Γ ⊢ arg : T₁
──────────────────────────────────  (App-Affine)
Γ ⊢ f(arg) : T₂
```

**Linear:**
```
Γ₁ ⊢ f : T₁ ⊸ T₂    Γ₂ ⊢ arg : T₁ ⊸ Γ₃    Γ₁ ∩ Γ₂ = ∅
───────────────────────────────────────────────────────  (App-Linear)
Γ₁ ∪ Γ₂ ⊢ f(arg) : T₂ ⊸ Γ₃

Note: f and arg cannot share linear variables (contexts must be disjoint)
```

## Implementation Strategy

### Affine Type Checker (Current - Idris2)

Located: `idris2/src/Ephapax/Affine/Typecheck.idr`

**Context Structure:**
```idris
record Entry where
  constructor MkEntry
  ty : Ty
  used : Bool      -- Has this variable been used?
  linear : Bool    -- Is this a linear resource? (for let!)

Context : Type
Context = List (String, Entry)
```

**Key Algorithm:**
1. Track usage with `used` flag
2. Mark variable as used when referenced
3. At scope exit: error if `linear && !used`, warning if `!linear && !used`
4. Allow implicit drops for non-linear values

### Linear Type Checker (To Implement - Ephapax)

**Context Structure:**
```ephapax
type Entry = {
    ty: Ty,
    consumed: bool  // Must be true at scope exit
}

type Context = List (String, Entry)
```

**Key Algorithm:**
1. **Thread contexts** through expressions:
   - Input context Γ₁
   - Output context Γ₂ (variables consumed in expression)
2. **Check consumption** at every scope exit
3. **Branch agreement**: Both branches must consume same variables
4. **No implicit drops**: All linear values need explicit `drop()`

### Error Messages

**Affine:**
- "Warning: variable `x` not used"
- "Error: linear variable `x` reused"

**Linear:**
- "Error: linear variable `x` not consumed"
- "Error: variable `x` consumed in then-branch but not else-branch"
- "Error: cannot use `x` after it has been consumed"

## Type System Summary

### Affine Type System

**Properties:**
- ✅ Prevents use-after-move (via usage tracking)
- ✅ Prevents double-free (via usage tracking)
- ⚠️  May leak resources (if not consumed)
- ✅ Ergonomic (implicit drops)

### Linear Type System

**Properties:**
- ✅ Prevents use-after-move (via context threading)
- ✅ Prevents double-free (via context threading)
- ✅ Prevents leaks (all resources must be consumed)
- ⚠️  Less ergonomic (explicit drops required)

## Gradual Migration Path

Code can mix both:
```ephapax
fn mixed_example() -> i32 {
    let x = alloc(5);       // Affine binding
    let! y = acquire();     // Linear binding

    let z = use(x);         // x may or may not be used later - OK
    let w = use(y);         // y MUST be consumed

    drop(y);                // Explicit drop required for linear
    w                       // x implicitly dropped - OK
}
```

## Testing Strategy

### Affine Tests
- ✅ Detect double-use
- ✅ Warn on unused non-linear vars
- ✅ Error on unused linear vars
- ✅ Allow implicit drops

### Linear Tests
- ✅ All affine tests (linear is stricter)
- ✅ Error on ANY unused linear var
- ✅ Error on branch disagreement
- ✅ Require explicit drops
- ✅ Thread contexts correctly through expressions

## References

- **Linear Logic**: Girard (1987)
- **Affine Types**: Ahmed et al. (2007)
- **Rust Ownership**: RFC 0458
- **Linear Haskell**: Bernardy et al. (2017)
