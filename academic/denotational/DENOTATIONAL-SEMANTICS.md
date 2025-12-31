# Denotational Semantics of Ephapax

## Mathematical Meaning of Programs

**Version**: 1.0.0
**Date**: 2025-12-31
**SPDX-License-Identifier**: EUPL-1.2

---

## Abstract

We develop a denotational semantics for Ephapax, assigning mathematical meanings to types and expressions. This semantics validates the operational behavior and provides a foundation for reasoning about program equivalence.

---

## 1. Introduction

Denotational semantics assigns mathematical objects (denotations) to syntactic entities:
- Types denote sets or domains
- Expressions denote functions or elements
- Evaluation corresponds to mathematical computation

For linear type systems, the standard approach uses *coherence spaces* or *game semantics*.

---

## 2. Domain Structure

### 2.1 Base Domains

| Type | Denotation |
|------|------------|
| Unit | {()} — singleton set |
| Bool | {true, false} |
| I32 | Z₃₂ = {-2³¹, ..., 2³¹-1} |
| I64 | Z₆₄ |
| F32 | IEEE 754 single-precision |
| F64 | IEEE 754 double-precision |

### 2.2 String Domain

For region-scoped strings:

```
⟦String@r⟧ = String × Region_id
```

Where:
- String = Σ* (finite sequences over alphabet Σ)
- Region_id = ℕ (region identifier)

### 2.3 Function Domain

```
⟦T₁ → T₂⟧ = ⟦T₁⟧ →_lin ⟦T₂⟧
```

Where →_lin denotes linear functions (use argument exactly once).

In domain-theoretic terms, this is the space of *strict* functions that consume their input.

### 2.4 Product Domain

```
⟦T₁ × T₂⟧ = ⟦T₁⟧ ⊗ ⟦T₂⟧
```

The tensor product requires both components to be present.

### 2.5 Sum Domain

```
⟦T₁ + T₂⟧ = ⟦T₁⟧ + ⟦T₂⟧  (disjoint union)
```

---

## 3. Memory Model

### 3.1 Heap Domain

```
Heap = Loc →_fin Cell

Cell = String × Region_id | Free | ⊥
```

Where:
- Loc = ℕ (locations/addresses)
- →_fin denotes finite partial functions

### 3.2 Region Environment

```
RegionEnv = Region_id →_fin Loc
```

Maps region identifiers to their bump pointers.

### 3.3 Configuration

```
Config = Heap × RegionEnv × Env × Expr

Env = Var →_fin Value
```

---

## 4. Value Domain

### 4.1 Runtime Values

```
Value = Unit
      | Bool(bool)
      | Int(ℤ)
      | Loc(ℕ)
      | Closure(Var × Ty × Expr × Env)
      | Pair(Value × Value)
      | Inl(Value) | Inr(Value)
      | Borrow(ℕ)
```

### 4.2 Linear Resource Tracking

Values carry a *usage flag*:

```
TrackedValue = Value × {available, consumed}
```

This mirrors the Coq context tracking.

---

## 5. Expression Semantics

### 5.1 Semantic Function Type

```
⟦−⟧ : Expr → (Heap × RegionEnv × Env) → (Value × Heap)⊥
```

The ⊥ represents potential non-termination or errors.

### 5.2 Value Expressions

```
⟦()⟧(h, R, ρ) = (Unit, h)

⟦true⟧(h, R, ρ) = (Bool(true), h)

⟦false⟧(h, R, ρ) = (Bool(false), h)

⟦n⟧(h, R, ρ) = (Int(n), h)
```

### 5.3 Variables

```
⟦x⟧(h, R, ρ) =
  match ρ(x) with
  | (v, available) → (v, h)    [mark x consumed in ρ]
  | (v, consumed)  → ⊥         [use-after-free]
  | undefined      → ⊥         [unbound variable]
```

For unrestricted types, the consumed check is skipped.

### 5.4 String Operations

**Allocation**:
```
⟦String.new@r(s)⟧(h, R, ρ) =
  let l = fresh_loc(h)
  let h' = h[l ↦ (s, r)]
  (Loc(l), h')
```

**Concatenation**:
```
⟦String.concat(e₁, e₂)⟧(h, R, ρ) =
  let (Loc(l₁), h₁) = ⟦e₁⟧(h, R, ρ)
  let (Loc(l₂), h₂) = ⟦e₂⟧(h₁, R, ρ)
  let (s₁, r) = h₂(l₁)
  let (s₂, _) = h₂(l₂)
  let l' = fresh_loc(h₂)
  let h₃ = h₂[l₁ ↦ Free][l₂ ↦ Free][l' ↦ (s₁ ++ s₂, r)]
  (Loc(l'), h₃)
```

**Length**:
```
⟦String.len(&e)⟧(h, R, ρ) =
  let (Loc(l), h') = ⟦e⟧(h, R, ρ)  [borrow, not consume]
  let (s, _) = h'(l)
  (Int(length(s)), h')
```

### 5.5 Let Bindings

```
⟦let x = e₁ in e₂⟧(h, R, ρ) =
  let (v, h') = ⟦e₁⟧(h, R, ρ)
  let ρ' = ρ[x ↦ (v, available)]
  ⟦e₂⟧(h', R, ρ')
```

### 5.6 Functions

**Abstraction**:
```
⟦λ(x:T). e⟧(h, R, ρ) = (Closure(x, T, e, ρ), h)
```

**Application**:
```
⟦e₁ e₂⟧(h, R, ρ) =
  let (Closure(x, T, body, ρ_clo), h₁) = ⟦e₁⟧(h, R, ρ)
  let (v, h₂) = ⟦e₂⟧(h₁, R, ρ)
  let ρ' = ρ_clo[x ↦ (v, available)]
  ⟦body⟧(h₂, R, ρ')
```

### 5.7 Products

**Pair**:
```
⟦(e₁, e₂)⟧(h, R, ρ) =
  let (v₁, h₁) = ⟦e₁⟧(h, R, ρ)
  let (v₂, h₂) = ⟦e₂⟧(h₁, R, ρ)
  (Pair(v₁, v₂), h₂)
```

**Projections**:
```
⟦π₁(e)⟧(h, R, ρ) =
  let (Pair(v₁, v₂), h') = ⟦e⟧(h, R, ρ)
  (v₁, h')  [v₂ implicitly dropped if linear]

⟦π₂(e)⟧(h, R, ρ) =
  let (Pair(v₁, v₂), h') = ⟦e⟧(h, R, ρ)
  (v₂, h')  [v₁ implicitly dropped if linear]
```

### 5.8 Sums

**Injection**:
```
⟦inl[T](e)⟧(h, R, ρ) =
  let (v, h') = ⟦e⟧(h, R, ρ)
  (Inl(v), h')

⟦inr[T](e)⟧(h, R, ρ) =
  let (v, h') = ⟦e⟧(h, R, ρ)
  (Inr(v), h')
```

**Case**:
```
⟦case e of inl(x)→e₁; inr(y)→e₂⟧(h, R, ρ) =
  let (w, h') = ⟦e⟧(h, R, ρ)
  match w with
  | Inl(v) → ⟦e₁⟧(h', R, ρ[x ↦ (v, available)])
  | Inr(v) → ⟦e₂⟧(h', R, ρ[y ↦ (v, available)])
```

### 5.9 Conditionals

```
⟦if e₁ then e₂ else e₃⟧(h, R, ρ) =
  let (Bool(b), h') = ⟦e₁⟧(h, R, ρ)
  if b then ⟦e₂⟧(h', R, ρ)
       else ⟦e₃⟧(h', R, ρ)
```

### 5.10 Regions

**Region scope**:
```
⟦region r { e }⟧(h, R, ρ) =
  let bump = current_heap_ptr(h)
  let R' = R[r ↦ bump]
  let (v, h') = ⟦e⟧(h, R', ρ)
  let h'' = free_region(h', r)
  (v, h'')
```

**Free region**:
```
free_region(h, r) =
  { l ↦ (if region_of(h(l)) = r then Free else h(l)) | l ∈ dom(h) }
```

### 5.11 Borrowing

```
⟦&e⟧(h, R, ρ) =
  let (Loc(l), h') = ⟦e⟧_borrow(h, R, ρ)  [does NOT consume]
  (Borrow(l), h')
```

The `⟦−⟧_borrow` variant does not mark the variable as consumed.

### 5.12 Resource Management

**Drop**:
```
⟦drop(e)⟧(h, R, ρ) =
  let (Loc(l), h') = ⟦e⟧(h, R, ρ)
  let h'' = h'[l ↦ Free]
  (Unit, h'')
```

**Copy** (unrestricted only):
```
⟦copy(e)⟧(h, R, ρ) =
  let (v, h') = ⟦e⟧(h, R, ρ)  [must be unrestricted]
  (Pair(v, v), h')
```

---

## 6. Semantic Properties

### 6.1 Compositionality

**Theorem 6.1** (Compositionality):
The denotation of a compound expression depends only on the denotations of its subexpressions.

*Proof*: By structural induction. Each semantic clause is defined solely in terms of subexpression denotations. □

### 6.2 Determinism

**Theorem 6.2** (Determinism):
For any expression e and configuration (h, R, ρ), ⟦e⟧(h, R, ρ) has at most one value.

*Proof*: By induction on e. All semantic clauses are deterministic functions. □

### 6.3 Adequacy

**Theorem 6.3** (Adequacy):
If ⟦e⟧(h, R, ρ) = (v, h'), then (h, R, ρ, e) →* (h', R, ρ', v) in the operational semantics.

*Proof*: By induction on e, showing each denotational clause corresponds to operational reduction steps. □

### 6.4 Soundness

**Theorem 6.4** (Soundness with respect to typing):
If `R; Γ ⊢ e : T ⊣ Γ'` then ⟦e⟧ is a partial function of the appropriate type.

*Proof*: By induction on the typing derivation. □

---

## 7. Linearity in Denotational Terms

### 7.1 Resource Semantics

The key insight for linear types is tracking resource consumption:

```
⟦e⟧ : (Heap × Env) → (Value × Heap × ConsumedSet)
```

Where ConsumedSet ⊆ Var tracks which variables were consumed.

### 7.2 Linear Function Interpretation

A linear function consumes its argument exactly once:

```
⟦T₁ → T₂⟧ = { f : ⟦T₁⟧ → ⟦T₂⟧ | f uses its argument exactly once }
```

Formally, this can be captured via:
- Coherence spaces (Girard)
- Game semantics (Abramsky, Hyland)
- Relational semantics

### 7.3 Tensor vs. Cartesian Product

**Tensor Product** (linear):
```
⟦T₁ × T₂⟧ = ⟦T₁⟧ ⊗ ⟦T₂⟧
```
Both components must be provided and used.

**Cartesian Product** (with projections):
In non-linear settings, (A × B) → A is valid.
In Ephapax, this is only valid if B is unrestricted (droppable).

---

## 8. Domain-Theoretic Considerations

### 8.1 CPOs and Continuity

For recursion (if added), we would need:
- Complete partial orders (CPOs)
- Continuous functions
- Least fixed points

### 8.2 Current Status

Ephapax currently has no general recursion:
- All functions terminate
- Denotations are total functions (modulo runtime errors)
- No need for ⊥ or fixed points

### 8.3 Future: Adding Recursion

If recursion is added:
```
⟦fix f. e⟧ = ⊔_{n≥0} f^n(⊥)
```

The least fixed point in the appropriate CPO.

---

## 9. Program Equivalence

### 9.1 Denotational Equality

**Definition**: e₁ ≈_den e₂ iff ⟦e₁⟧ = ⟦e₂⟧

### 9.2 Contextual Equivalence

**Definition**: e₁ ≈_ctx e₂ iff for all contexts C[−]:
```
C[e₁] ⇓ v  ⟺  C[e₂] ⇓ v
```

### 9.3 Full Abstraction

**Conjecture** (Full Abstraction):
For the appropriate semantic model:
```
e₁ ≈_den e₂  ⟺  e₁ ≈_ctx e₂
```

*Status*: Open problem. Requires careful choice of semantic domain.

---

## 10. Examples

### 10.1 String Concatenation

```
region r {
  let s1 = String.new@r("hello")
  let s2 = String.new@r("world")
  String.len(&(String.concat(s1, s2)))
}
```

Denotation:
```
(h₀, R₀, ρ₀)
  →[enter region] (h₀, R₀[r ↦ bump₀], ρ₀)
  →[String.new] (h₁ = h₀[l₁ ↦ ("hello", r)], ..., ρ₁ = ρ₀[s1 ↦ l₁])
  →[String.new] (h₂ = h₁[l₂ ↦ ("world", r)], ..., ρ₂ = ρ₁[s2 ↦ l₂])
  →[concat] (h₃ = h₂[l₁ ↦ Free][l₂ ↦ Free][l₃ ↦ ("helloworld", r)], ...)
  →[len] (Int(10), h₃)
  →[exit region] (Int(10), h₄ = h₃[l₃ ↦ Free])
```

Final value: Int(10)

### 10.2 Function Application

```
let f = fn(x: String@r) -> String.len(&x) in
let s = String.new@r("test")
f(s)
```

Denotation:
```
⟦f⟧ = Closure(x, String@r, String.len(&x), ρ₀)
⟦s⟧ = Loc(l) where h(l) = ("test", r)
⟦f(s)⟧ = ⟦String.len(&x)⟧(h, R, ρ₀[x ↦ Loc(l)])
       = Int(4)
```

---

## 11. TODO: Proof Obligations

### 11.1 Formal Proofs Needed

- [ ] Full adequacy theorem (operational/denotational correspondence)
- [ ] Soundness with respect to typing (complete proof)
- [ ] Compositionality (formalized in Coq)
- [ ] Determinism (formalized)

### 11.2 Model Construction

- [ ] Coherence space model for Ephapax
- [ ] Game semantics model
- [ ] Proof of full abstraction (if achievable)

### 11.3 Extensions

- [ ] Denotational semantics for polymorphism
- [ ] Semantics for effects/IO
- [ ] Semantics for concurrency (if added)

---

## 12. References

1. Scott, D.S. & Strachey, C. (1971). *Toward a mathematical semantics for computer languages*.

2. Plotkin, G.D. (1977). LCF considered as a programming language. *Theoretical Computer Science*, 5(3).

3. Girard, J.-Y. (1987). Linear logic. *Theoretical Computer Science*, 50(1).

4. Abramsky, S. & Jagadeesan, R. (1994). Games and full completeness for multiplicative linear logic. *Journal of Symbolic Logic*, 59(2).

5. Hyland, M. & Ong, L. (2000). On full abstraction for PCF. *Information and Computation*, 163(2).

---

*End of Denotational Semantics*
