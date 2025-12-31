# Linear vs Affine Type Systems

## A Comprehensive Comparison for Ephapax

**Version**: 1.0.0
**Date**: 2025-12-31
**SPDX-License-Identifier**: EUPL-1.2

---

## Abstract

This document provides a rigorous comparison between linear and affine type systems, specifically in the context of Ephapax. We define both systems formally, prove their key properties, and analyze the tradeoffs for memory safety, expressiveness, and usability. This enables Ephapax to potentially support both modes.

---

## 1. Introduction

### 1.1 Substructural Type Systems

Classical type systems permit arbitrary use of variables (weakening and contraction):
- **Weakening**: Ignore unused variables
- **Contraction**: Use variables multiple times

Substructural type systems restrict these rules:

| System | Weakening | Contraction | Usage |
|--------|-----------|-------------|-------|
| **Unrestricted** | ✓ | ✓ | Any |
| **Affine** | ✓ | ✗ | ≤ 1 |
| **Relevant** | ✗ | ✓ | ≥ 1 |
| **Linear** | ✗ | ✗ | = 1 |

### 1.2 Ephapax Current Design

Ephapax currently uses **linear types** (use exactly once):
- Guarantees: No leaks, no use-after-free
- Limitation: Must explicitly consume every resource

### 1.3 Document Goals

1. Formally define both linear and affine systems for Ephapax
2. Prove soundness for each
3. Compare expressiveness and guarantees
4. Propose dual-mode support

---

## 2. Linear Type System (Current Ephapax)

### 2.1 Syntax Review

```
Linearity: l ::= Lin | Unr

Types: T ::= Base | String@r | T₁ × T₂ | T₁ + T₂ | T₁ → T₂ | &T

linear(T) = T ∈ {String@r, Ref[Lin](_), ...}
```

### 2.2 Linear Typing Judgment

```
R; Γ ⊢_Lin e : T ⊣ Γ'
```

**Key Property**: All linear variables in Γ must be used exactly once.

### 2.3 Linear Typing Rules

**Variable (Linear)**:
```
Γ(x) = (T, false)    linear(T)
─────────────────────────────────  (Lin-Var)
R; Γ ⊢_Lin x : T ⊣ Γ[x ↦ used]
```

**Let Binding**:
```
R; Γ ⊢_Lin e₁ : T₁ ⊣ Γ'
R; Γ', x:T₁ ⊢_Lin e₂ : T₂ ⊣ Γ'', (x:T₁, true)
linear(T₁) ⟹ x marked used in Γ''
─────────────────────────────────────────────────  (Lin-Let)
R; Γ ⊢_Lin let x = e₁ in e₂ : T₂ ⊣ Γ''
```

**Conditional**:
```
R; Γ ⊢_Lin e₁ : Bool ⊣ Γ'
R; Γ' ⊢_Lin e₂ : T ⊣ Γ''
R; Γ' ⊢_Lin e₃ : T ⊣ Γ''     ← Same output context!
───────────────────────────────────────────────────  (Lin-If)
R; Γ ⊢_Lin if e₁ then e₂ else e₃ : T ⊣ Γ''
```

### 2.4 Linear Properties

**Theorem 2.1** (Linear Soundness):
If `R; Γ ⊢_Lin e : T ⊣ Γ'`, then all linear variables in Γ are used exactly once during evaluation of e.

**Theorem 2.2** (No Leaks):
Linear resources cannot be discarded without explicit `drop`.

**Theorem 2.3** (No Aliasing):
Linear values have unique owners; no aliasing is possible.

---

## 3. Affine Type System (Alternative)

### 3.1 Affine Motivation

Affine types allow "use at most once" (≤ 1):
- More permissive: Can drop resources implicitly
- Still prevents: Use-after-free, double-free
- Does not prevent: Memory leaks (can discard without consuming)

### 3.2 Affine Typing Judgment

```
R; Γ ⊢_Aff e : T ⊣ Γ'
```

**Key Property**: All affine variables in Γ may be used at most once.

### 3.3 Affine Typing Rules

**Variable (Affine)**:
```
Γ(x) = (T, false)    affine(T)
─────────────────────────────────  (Aff-Var)
R; Γ ⊢_Aff x : T ⊣ Γ[x ↦ used]
```

(Same as linear for the use case)

**Let Binding (Affine)**:
```
R; Γ ⊢_Aff e₁ : T₁ ⊣ Γ'
R; Γ', x:T₁ ⊢_Aff e₂ : T₂ ⊣ Γ'', (x:T₁, _)
                              ↑ No requirement that x is used!
───────────────────────────────────────────────  (Aff-Let)
R; Γ ⊢_Aff let x = e₁ in e₂ : T₂ ⊣ Γ''
```

**Conditional (Affine)**:
```
R; Γ ⊢_Aff e₁ : Bool ⊣ Γ'
R; Γ' ⊢_Aff e₂ : T ⊣ Γ₂
R; Γ' ⊢_Aff e₃ : T ⊣ Γ₃
Γ'' = merge(Γ₂, Γ₃)        ← Branches may differ!
───────────────────────────────────────────────────  (Aff-If)
R; Γ ⊢_Aff if e₁ then e₂ else e₃ : T ⊣ Γ''
```

**Merge Operation**:
```
merge(Γ₂, Γ₃)(x) =
  match (Γ₂(x), Γ₃(x)) with
  | (used, used) → used
  | (used, unused) → used  ← conservative: mark as used
  | (unused, used) → used
  | (unused, unused) → unused
```

### 3.4 Implicit Drop

Affine types permit implicit drop at scope exit:

```
region r {
  let s = String.new@r("hello")
  42  // s is implicitly dropped!
}
```

This is equivalent to:
```
region r {
  let s = String.new@r("hello")
  drop(s);
  42
}
```

### 3.5 Affine Properties

**Theorem 3.1** (Affine Soundness):
If `R; Γ ⊢_Aff e : T ⊣ Γ'`, then all affine variables in Γ are used at most once.

**Theorem 3.2** (No Use-After-Free):
Affine resources cannot be accessed after consumption.

**Theorem 3.3** (No Double-Free):
Affine resources cannot be freed twice.

**Non-Theorem** (Leaks Possible):
Affine types do NOT guarantee no leaks. Resources may be discarded.

---

## 4. Formal Comparison

### 4.1 Type System Relationship

**Theorem 4.1** (Linear ⊂ Affine):
Every linear-typeable expression is affine-typeable:
```
R; Γ ⊢_Lin e : T ⊣ Γ'  ⟹  R; Γ ⊢_Aff e : T ⊣ Γ''
```
(with Γ' ⊆ Γ'' in the "used" sense)

*Proof*: Affine typing is strictly more permissive. Linear typing requires all uses; affine permits fewer. □

**Theorem 4.2** (Affine ⊄ Linear):
Some affine-typeable expressions are not linear-typeable:
```
let x = String.new@r("hi") in 42    // Affine: OK (x dropped)
                                     // Linear: ERROR (x unused)
```

### 4.2 Safety Guarantees Comparison

| Property | Linear | Affine |
|----------|--------|--------|
| No use-after-free | ✓ | ✓ |
| No double-free | ✓ | ✓ |
| No memory leaks | ✓ | ✗ |
| No dangling pointers | ✓ | ✓ |
| No aliasing | ✓ | ✓ |

### 4.3 Expressiveness Comparison

| Feature | Linear | Affine |
|---------|--------|--------|
| Implicit drop | ✗ | ✓ |
| Asymmetric branches | ✗ | ✓ |
| Early return | Complex | Simple |
| Error handling | Complex | Simple |

**Example**: Early Return

Affine (natural):
```
fn process(s: String@r) -> Result {
  if error_check() {
    return Err("failed")  // s implicitly dropped
  }
  // use s
}
```

Linear (requires explicit handling):
```
fn process(s: String@r) -> Result {
  if error_check() {
    drop(s);              // Must explicitly drop!
    return Err("failed")
  }
  // use s
}
```

### 4.4 Logic Correspondence

| Type System | Logic | Structural Rules |
|-------------|-------|------------------|
| Linear | Linear Logic | Neither W nor C |
| Affine | Affine Logic | Weakening only |
| Rust | Affine + Borrowing | Complex |

---

## 5. Semantic Differences

### 5.1 Denotational Semantics

**Linear**:
```
⟦T₁ ⊸ T₂⟧ = functions that consume input exactly once
```

**Affine**:
```
⟦T₁ → T₂⟧_Aff = functions that consume input at most once
```

The affine arrow is "larger" (more functions qualify).

### 5.2 Categorical Semantics

**Linear**: Symmetric monoidal closed categories (SMCCs)

**Affine**: SMCCs with a "discard" natural transformation:
```
discard_A : A → I
```

The discard map allows weakening.

### 5.3 Operational Semantics

**Linear Reduction**:
```
let x = v in e → e[v/x]    (x must occur in e)
```

**Affine Reduction**:
```
let x = v in e → e[v/x]    (x may or may not occur in e)
                            (if not: implicit drop of v)
```

---

## 6. Hybrid System: Ephapax with Both Modes

### 6.1 Multiplicity Annotations

Following Linear Haskell, we can parameterize by multiplicity:

```
Multiplicity: m ::= 1 | ω | ? | Aff

T₁ -[m]-> T₂    -- Function with multiplicity m

1   : exactly once (linear)
ω   : any number of times (unrestricted)
Aff : at most once (affine)
?   : inferred
```

### 6.2 Hybrid Typing Rules

**Multiplicity-Parameterized Variable**:
```
Γ(x) = (T, m, false)    m ≤ 1
─────────────────────────────────────  (Var-m)
R; Γ ⊢ x : T ⊣ Γ[x ↦ used]
```

**Let with Multiplicity**:
```
R; Γ ⊢ e₁ : T₁ ⊣ Γ'
R; Γ', x:T₁^m ⊢ e₂ : T₂ ⊣ Γ''
m = 1 ⟹ x used in Γ''
m = Aff ⟹ x used or unused (OK)
──────────────────────────────────────────  (Let-m)
R; Γ ⊢ let x : T₁^m = e₁ in e₂ : T₂ ⊣ Γ''
```

### 6.3 Mode Declaration

Allow files/modules to declare their mode:

```
#![linear]     // This module uses linear types (strict)

#![affine]     // This module uses affine types (relaxed)
```

Or per-binding:

```
let! x = e    // linear (must use)
let? y = e    // affine (may use)
let  z = e    // inferred
```

### 6.4 Interoperability

Linear code can call affine code (trivially).
Affine code calling linear code requires wrapping:

```
// Affine context calling linear function
let result = linear_fn(x)   // OK: x is consumed

// But returning unused linear value is an error
let unused : String@r^1 = ...
// ERROR: unused linear value
```

---

## 7. Rust Comparison

### 7.1 Rust's System

Rust uses affine types with borrowing:
- Ownership is affine (move = consume once)
- Borrowing allows multiple reads
- Mutable borrowing is exclusive

### 7.2 Key Differences from Ephapax

| Feature | Rust | Ephapax (Linear) | Ephapax (Affine) |
|---------|------|------------------|------------------|
| Default | Affine | Linear | Affine |
| Implicit drop | ✓ | ✗ | ✓ |
| Borrowing | Lifetimes | Second-class | Second-class |
| Complexity | High | Low | Low |
| Leak prevention | ✗ (can leak) | ✓ | ✗ |

### 7.3 Rust's `#[must_use]`

Rust has `#[must_use]` to encourage (not enforce) consumption:
```rust
#[must_use]
fn important() -> Resource { ... }

important();  // Warning: unused value
```

Ephapax's linear mode enforces this at the type level.

---

## 8. Formal Metatheory

### 8.1 Type Safety for Both Systems

**Theorem 8.1** (Linear Type Safety):
Progress and preservation hold for the linear type system.

**Theorem 8.2** (Affine Type Safety):
Progress and preservation hold for the affine type system.

### 8.2 Memory Safety

**Theorem 8.3** (Unified Memory Safety):
Both linear and affine systems prevent use-after-free and double-free.

*Proof*: Both systems require that resources are used at most once. Once consumed, the binding is marked "used" and cannot be accessed again. □

### 8.3 Leak Freedom (Linear Only)

**Theorem 8.4** (Linear Leak Freedom):
Linear types prevent memory leaks (within regions).

*Proof*: Linear variables must be used exactly once. "Used" includes drop or transformation. Therefore, no linear resource goes unconsumed. □

**Counter-Example (Affine Leaks)**:
```
// Affine: This compiles but leaks
region r {
  let s = String.new@r("leaked")
  ()   // s discarded, but region hasn't exited yet
       // Memory recovered at region exit, but could be large
}
```

---

## 9. Implementation Considerations

### 9.1 Type Checker Modifications

For affine mode:
1. Remove "unused linear variable" error
2. Allow asymmetric branches in conditionals
3. Add implicit drop at scope boundaries

### 9.2 Code Generation

For affine mode with implicit drop:
```
compile(let x = e₁ in e₂) =
  compile(e₁)
  local.set $x
  compile(e₂)
  // If x not used and linear, insert: local.get $x; call $drop
```

### 9.3 Runtime Impact

| Aspect | Linear | Affine |
|--------|--------|--------|
| Compile time | Same | Same |
| Runtime checks | None | None |
| Code size | Smaller (no implicit drops) | Larger (implicit drops) |
| Debugging | Easier (explicit) | Harder (implicit) |

---

## 10. Recommendations

### 10.1 Default Choice

**Recommendation**: Linear as default, affine as opt-in.

Rationale:
- Linear catches more bugs (leaks)
- Linear encourages explicit resource handling
- Affine available for convenience when needed

### 10.2 Migration Path

1. Start with linear-only (current Ephapax)
2. Add `#![affine]` module-level annotation
3. Add per-binding annotations (`let?`)
4. Consider multiplicity inference

### 10.3 Documentation

Clearly document:
- Differences between modes
- When to use each mode
- Implications for memory safety

---

## 11. TODO: Implementation

### 11.1 Type System

- [ ] Implement affine mode in type checker
- [ ] Add multiplicity annotations
- [ ] Implement mode inference

### 11.2 Proofs

- [ ] Formalize affine typing in Coq
- [ ] Prove affine soundness
- [ ] Prove hybrid system soundness

### 11.3 Tooling

- [ ] Add mode selection to CLI
- [ ] Implement IDE support for both modes
- [ ] Add migration tools (linear ↔ affine)

---

## 12. References

1. Walker, D. (2005). Substructural Type Systems. In *ATTAPL*, Chapter 1.

2. Bernardy, J.-P. et al. (2018). Linear Haskell: practical linearity in a higher-order polymorphic language. *PACMPL*, 2(POPL).

3. Tov, J.A. & Pucella, R. (2011). Practical affine types. *POPL*.

4. Mazurak, K., Zhao, J., & Zdancewic, S. (2010). Lightweight linear types in System F°. *TLDI*.

5. Jung, R. et al. (2018). RustBelt: Securing the foundations of the Rust programming language. *PACMPL*, 2(POPL).

6. Wadler, P. (1990). Linear types can change the world! In *Programming Concepts and Methods*.

---

*End of Linear vs Affine Comparison*
