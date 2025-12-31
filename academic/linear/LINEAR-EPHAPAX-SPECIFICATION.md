# Linear Ephapax: Complete Formal Specification

## A Linear Type System for Safe Memory Management

**Version**: 1.0.0
**Date**: 2025-12-31
**Discipline**: Linear (use exactly once)
**SPDX-License-Identifier**: EUPL-1.2

---

## Abstract

Linear Ephapax is a programming language with a *linear* type system where every resource must be used exactly once. This document provides the complete formal specification including syntax, type system, operational semantics, and metatheory. Linear types guarantee: no use-after-free, no double-free, no memory leaks, and no dangling pointers.

---

## Part I: Syntax

### 1.1 Variables and Names

```
x, y, z ∈ Var           (term variables)
r, s, t ∈ RegionName    (region identifiers)
```

### 1.2 Types

```
T, U ∈ Type ::=
    | Unit                      (unit type)
    | Bool                      (boolean)
    | I32 | I64 | F32 | F64     (numeric primitives)
    | String@r                  (linear string in region r)
    | T₁ × T₂                   (linear product)
    | T₁ + T₂                   (linear sum)
    | T₁ ⊸ T₂                   (linear function)
    | &T                        (second-class borrow)
    | Region[r](T)              (region-scoped type)
```

### 1.3 Linearity Classification

**Definition 1.1** (Linear Type):
```
linear : Type → Bool

linear(String@r)     = true
linear(T₁ × T₂)      = linear(T₁) ∨ linear(T₂)
linear(T₁ + T₂)      = linear(T₁) ∨ linear(T₂)
linear(Region[r](T)) = linear(T)
linear(_)            = false
```

### 1.4 Expressions

```
e ∈ Expr ::=
    (* Values *)
    | ()                        (unit)
    | true | false              (booleans)
    | n                         (integer literal)
    | x                         (variable)

    (* Strings *)
    | String.new@r(s)           (allocate in region r)
    | String.concat(e₁, e₂)     (concatenate, consuming both)
    | String.len(e)             (length via borrow)

    (* Binding *)
    | let x = e₁ in e₂          (let binding)
    | let! x = e₁ in e₂         (explicitly linear let)

    (* Functions *)
    | λ(x:T). e                 (abstraction)
    | e₁ e₂                     (application)

    (* Products *)
    | (e₁, e₂)                  (pair construction)
    | let (x, y) = e₁ in e₂     (pair elimination)
    | π₁(e) | π₂(e)             (projections - restricted)

    (* Sums *)
    | inl[T](e) | inr[T](e)     (injections)
    | case e of inl(x) → e₁; inr(y) → e₂  (case analysis)

    (* Control *)
    | if e₁ then e₂ else e₃     (conditional)

    (* Regions *)
    | region r { e }            (region scope)

    (* Borrowing *)
    | &e                        (borrow)

    (* Resource Management *)
    | drop(e)                   (explicit consumption)
    | copy(e)                   (copy - unrestricted only)
```

### 1.5 Values

```
v ∈ Value ::= () | true | false | n | λ(x:T).e | (v₁, v₂) | inl[T](v) | inr[T](v)
```

---

## Part II: Type System

### 2.1 Typing Contexts

**Definition 2.1** (Context):
A typing context Γ is a finite map from variables to (type, used-flag) pairs:
```
Γ ::= ∅ | Γ, x : T @ used
```
where `used ∈ {⊥, ⊤}` tracks whether the binding has been consumed.

**Definition 2.2** (Context Operations):

```
lookup(Γ, x) = (T, u)  if (x : T @ u) ∈ Γ

mark(Γ, x) = Γ[x ↦ (T, ⊤)]  where Γ(x) = (T, _)

extend(Γ, x, T) = Γ, x : T @ ⊥

fresh(Γ, x) ⟺ x ∉ dom(Γ)
```

### 2.2 Region Environment

```
R ⊆ RegionName    (set of active regions)
```

### 2.3 Linear Typing Judgment

The central judgment has the form:
```
R; Γ ⊢ e : T ⊣ Γ'
```

Read: "Under active regions R and input context Γ, expression e has type T, producing output context Γ'."

**Critical Invariant**: The output context Γ' tracks which linear resources have been consumed. All linear bindings must be marked used by the end of their scope.

### 2.4 Typing Rules

#### 2.4.1 Values

```
─────────────────────────────  (T-Unit)
R; Γ ⊢ () : Unit ⊣ Γ


─────────────────────────────  (T-True)
R; Γ ⊢ true : Bool ⊣ Γ


─────────────────────────────  (T-False)
R; Γ ⊢ false : Bool ⊣ Γ


─────────────────────────────  (T-Int)
R; Γ ⊢ n : I32 ⊣ Γ
```

#### 2.4.2 Variables

```
lookup(Γ, x) = (T, ⊥)
linear(T) = true
─────────────────────────────────────────  (T-Var-Lin)
R; Γ ⊢ x : T ⊣ mark(Γ, x)


lookup(Γ, x) = (T, _)
linear(T) = false
─────────────────────────────────────────  (T-Var-Unr)
R; Γ ⊢ x : T ⊣ Γ
```

**Key Point**: Linear variables are marked used upon access. Unrestricted variables leave context unchanged.

#### 2.4.3 Strings

```
r ∈ R
─────────────────────────────────────────────  (T-StringNew)
R; Γ ⊢ String.new@r(s) : String@r ⊣ Γ


R; Γ ⊢ e₁ : String@r ⊣ Γ'
R; Γ' ⊢ e₂ : String@r ⊣ Γ''
─────────────────────────────────────────────────────────  (T-StringConcat)
R; Γ ⊢ String.concat(e₁, e₂) : String@r ⊣ Γ''


R; Γ ⊢ &e : &(String@r) ⊣ Γ'
─────────────────────────────────────────────  (T-StringLen)
R; Γ ⊢ String.len(e) : I32 ⊣ Γ'
```

#### 2.4.4 Let Bindings

```
R; Γ ⊢ e₁ : T₁ ⊣ Γ'
fresh(Γ', x)
R; extend(Γ', x, T₁) ⊢ e₂ : T₂ ⊣ Γ'', x : T₁ @ u
linear(T₁) ⟹ u = ⊤                              ← MUST USE IF LINEAR
─────────────────────────────────────────────────────────────────────  (T-Let)
R; Γ ⊢ let x = e₁ in e₂ : T₂ ⊣ Γ''
```

**Critical**: If T₁ is linear, x MUST be marked used (u = ⊤) by the end of e₂.

#### 2.4.5 Functions

```
fresh(Γ, x)
R; extend(Γ, x, T₁) ⊢ e : T₂ ⊣ Γ', x : T₁ @ u
linear(T₁) ⟹ u = ⊤
─────────────────────────────────────────────────  (T-Lam)
R; Γ ⊢ λ(x:T₁). e : T₁ ⊸ T₂ ⊣ Γ'


R; Γ ⊢ e₁ : T₁ ⊸ T₂ ⊣ Γ'
R; Γ' ⊢ e₂ : T₁ ⊣ Γ''
───────────────────────────────────────  (T-App)
R; Γ ⊢ e₁ e₂ : T₂ ⊣ Γ''
```

#### 2.4.6 Products

```
R; Γ ⊢ e₁ : T₁ ⊣ Γ'
R; Γ' ⊢ e₂ : T₂ ⊣ Γ''
───────────────────────────────────────  (T-Pair)
R; Γ ⊢ (e₁, e₂) : T₁ × T₂ ⊣ Γ''


R; Γ ⊢ e₁ : T₁ × T₂ ⊣ Γ'
fresh(Γ', x)  fresh(Γ', y)
R; extend(extend(Γ', x, T₁), y, T₂) ⊢ e₂ : T ⊣ Γ'', x:T₁@u₁, y:T₂@u₂
linear(T₁) ⟹ u₁ = ⊤
linear(T₂) ⟹ u₂ = ⊤
─────────────────────────────────────────────────────────────────────  (T-LetPair)
R; Γ ⊢ let (x, y) = e₁ in e₂ : T ⊣ Γ''
```

**Projection (Restricted)**:
```
R; Γ ⊢ e : T₁ × T₂ ⊣ Γ'
linear(T₂) = false                          ← T₂ must be droppable!
───────────────────────────────────────────  (T-Fst)
R; Γ ⊢ π₁(e) : T₁ ⊣ Γ'
```

Projections are only allowed when the discarded component is non-linear.

#### 2.4.7 Sums

```
R; Γ ⊢ e : T₁ ⊣ Γ'
─────────────────────────────────────  (T-Inl)
R; Γ ⊢ inl[T₂](e) : T₁ + T₂ ⊣ Γ'


R; Γ ⊢ e : T₁ + T₂ ⊣ Γ'
R; extend(Γ', x, T₁) ⊢ e₁ : T ⊣ Γ₁, x:T₁@⊤
R; extend(Γ', y, T₂) ⊢ e₂ : T ⊣ Γ₂, y:T₂@⊤
Γ₁ = Γ₂                                     ← BRANCHES MUST AGREE
─────────────────────────────────────────────────────────────────  (T-Case)
R; Γ ⊢ case e of inl(x) → e₁; inr(y) → e₂ : T ⊣ Γ₁
```

**Critical**: Both branches must consume the same linear resources (Γ₁ = Γ₂).

#### 2.4.8 Conditionals

```
R; Γ ⊢ e₁ : Bool ⊣ Γ'
R; Γ' ⊢ e₂ : T ⊣ Γ''
R; Γ' ⊢ e₃ : T ⊣ Γ''                        ← SAME OUTPUT CONTEXT
───────────────────────────────────────────────────────────────  (T-If)
R; Γ ⊢ if e₁ then e₂ else e₃ : T ⊣ Γ''
```

#### 2.4.9 Regions

```
r ∉ R
R ∪ {r}; Γ ⊢ e : T ⊣ Γ'
¬mentions(T, r)                             ← NO ESCAPE
─────────────────────────────────────────────  (T-Region)
R; Γ ⊢ region r { e } : T ⊣ Γ'
```

**Definition 2.3** (Mentions):
```
mentions(r, String@s)     = (r = s)
mentions(r, T₁ × T₂)      = mentions(r, T₁) ∨ mentions(r, T₂)
mentions(r, T₁ + T₂)      = mentions(r, T₁) ∨ mentions(r, T₂)
mentions(r, T₁ ⊸ T₂)      = mentions(r, T₁) ∨ mentions(r, T₂)
mentions(r, Region[s](T)) = (r = s) ∨ mentions(r, T)
mentions(r, _)            = false
```

#### 2.4.10 Borrowing

```
lookup(Γ, x) = (T, ⊥)
─────────────────────────────────  (T-Borrow)
R; Γ ⊢ &x : &T ⊣ Γ
```

**Note**: Borrowing does NOT mark the variable as used. The original remains available.

#### 2.4.11 Resource Management

```
linear(T) = true
R; Γ ⊢ e : T ⊣ Γ'
───────────────────────────────────  (T-Drop)
R; Γ ⊢ drop(e) : Unit ⊣ Γ'


linear(T) = false
R; Γ ⊢ e : T ⊣ Γ'
───────────────────────────────────  (T-Copy)
R; Γ ⊢ copy(e) : T × T ⊣ Γ'
```

---

## Part III: Operational Semantics

### 3.1 Runtime Structures

**Definition 3.1** (Memory):
```
H : Loc → Cell
Cell ::= ⟨data : String, region : RegionName, status : {Alloc, Freed}⟩
```

**Definition 3.2** (Runtime Environment):
```
ρ : Var → Value
```

**Definition 3.3** (Configuration):
```
σ = ⟨H, R, ρ, e⟩
```

### 3.2 Small-Step Reduction

```
σ → σ'
```

#### 3.2.1 Variable Lookup

```
ρ(x) = v
───────────────────────────────────
⟨H, R, ρ, x⟩ → ⟨H, R, ρ, v⟩
```

#### 3.2.2 String Operations

```
ℓ = fresh(H)
H' = H[ℓ ↦ ⟨s, r, Alloc⟩]
r ∈ R
─────────────────────────────────────────────────────
⟨H, R, ρ, String.new@r(s)⟩ → ⟨H', R, ρ, ℓ⟩


H(ℓ₁) = ⟨s₁, r, Alloc⟩
H(ℓ₂) = ⟨s₂, r, Alloc⟩
ℓ₃ = fresh(H)
H' = H[ℓ₁ ↦ ⟨_, r, Freed⟩][ℓ₂ ↦ ⟨_, r, Freed⟩][ℓ₃ ↦ ⟨s₁++s₂, r, Alloc⟩]
──────────────────────────────────────────────────────────────────────
⟨H, R, ρ, String.concat(ℓ₁, ℓ₂)⟩ → ⟨H', R, ρ, ℓ₃⟩
```

#### 3.2.3 Let Binding

```
⟨H, R, ρ, e₁⟩ → ⟨H', R', ρ', e₁'⟩
───────────────────────────────────────────────────────
⟨H, R, ρ, let x = e₁ in e₂⟩ → ⟨H', R', ρ', let x = e₁' in e₂⟩


is_value(v)
─────────────────────────────────────────────────────────
⟨H, R, ρ, let x = v in e₂⟩ → ⟨H, R, ρ[x ↦ v], e₂⟩
```

#### 3.2.4 Application

```
is_value(v)
───────────────────────────────────────────────────────────
⟨H, R, ρ, (λ(x:T). e) v⟩ → ⟨H, R, ρ[x ↦ v], e⟩
```

#### 3.2.5 Regions

```
r ∉ R
───────────────────────────────────────────────────────────
⟨H, R, ρ, region r { e }⟩ → ⟨H, R ∪ {r}, ρ, region r { e }⟩


is_value(v)
r ∈ R
H' = free_region(H, r)
───────────────────────────────────────────────────────────
⟨H, R, ρ, region r { v }⟩ → ⟨H', R \ {r}, ρ, v⟩
```

**Definition 3.4** (Region Deallocation):
```
free_region(H, r) = λℓ.
  if H(ℓ).region = r ∧ H(ℓ).status = Alloc
  then ⟨H(ℓ).data, r, Freed⟩
  else H(ℓ)
```

#### 3.2.6 Drop

```
H' = H[ℓ ↦ ⟨_, _, Freed⟩]
───────────────────────────────────────
⟨H, R, ρ, drop(ℓ)⟩ → ⟨H', R, ρ, ()⟩
```

---

## Part IV: Metatheory

### 4.1 Type Safety

**Theorem 4.1** (Progress):
If `R; Γ ⊢ e : T ⊣ Γ'` and `e` is not a value, then there exists `e'` such that `⟨H, R, ρ, e⟩ → ⟨H', R', ρ', e'⟩` for appropriate H, ρ.

**Theorem 4.2** (Preservation):
If `R; Γ ⊢ e : T ⊣ Γ'` and `⟨H, R, ρ, e⟩ → ⟨H', R', ρ', e'⟩`, then there exists Γ'' such that `R'; Γ'' ⊢ e' : T ⊣ Γ'`.

### 4.2 Linearity Preservation

**Theorem 4.3** (Linearity):
If `R; Γ ⊢ e : T ⊣ Γ'`, then for every `(x : U @ ⊥) ∈ Γ` where `linear(U) = true`, we have `(x : U @ ⊤) ∈ Γ'`.

In words: every linear variable in the input context is consumed exactly once.

**Proof Sketch**:
By induction on the typing derivation. Key cases:
- T-Var-Lin: Marks the variable used
- T-Let: Requires linear binding to be used in body
- T-If/T-Case: Both branches must agree on usage

### 4.3 Memory Safety

**Theorem 4.4** (No Use-After-Free):
If `R; Γ ⊢ e : T ⊣ Γ'` and evaluation reaches a configuration `⟨H, R, ρ, e'⟩`, then for all locations ℓ reachable from ρ, `H(ℓ).status = Alloc`.

**Theorem 4.5** (No Double-Free):
A location ℓ cannot be freed twice during evaluation of a well-typed expression.

**Theorem 4.6** (No Leaks):
All linear resources are consumed by the end of evaluation (within their region).

**Theorem 4.7** (No Region Escapes):
If `R; Γ ⊢ region r { e } : T ⊣ Γ'`, then no value of type mentioning r can escape the region scope.

---

## Part V: Decidability and Complexity

**Theorem 5.1** (Type Checking Decidability):
Type checking for Linear Ephapax is decidable in O(n) time where n = |e|.

**Proof**:
1. Rules are syntax-directed (no overlap)
2. Each rule recurses on strict subexpressions
3. Context operations are O(1) with hash maps
4. Total: O(n) nodes × O(1) per node = O(n)

---

## Part VI: Linear Logic Correspondence

### 6.1 Curry-Howard

| Linear Ephapax | Linear Logic |
|----------------|--------------|
| T₁ × T₂ | A ⊗ B (tensor) |
| T₁ + T₂ | A ⊕ B (plus) |
| T₁ ⊸ T₂ | A ⊸ B (lollipop) |
| Unit | 1 |
| Unrestricted T | !A |

### 6.2 Proof Terms

Typing derivations correspond to proofs in intuitionistic linear logic. Evaluation corresponds to cut elimination.

---

## Part VII: Categorical Semantics

Linear Ephapax types and terms form a symmetric monoidal closed category (SMCC):

- Objects: Types
- Morphisms: Terms `x:A ⊢ e : B`
- Tensor (⊗): Product types
- Internal Hom (⊸): Function types
- Unit (I): Unit type

The SMCC axioms (associativity, unit, symmetry, closure) correspond to type isomorphisms provable in the system.

---

*End of Linear Ephapax Specification*
