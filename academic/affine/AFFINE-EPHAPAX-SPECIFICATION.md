# Affine Ephapax: Complete Formal Specification

## An Affine Type System for Safe Memory Management

**Version**: 1.0.0
**Date**: 2025-12-31
**Discipline**: Affine (use at most once)
**SPDX-License-Identifier**: EUPL-1.2

---

## Abstract

Affine Ephapax is a programming language with an *affine* type system where every resource may be used at most once. This is more permissive than linear types: resources can be implicitly dropped. This document provides the complete formal specification including syntax, type system, operational semantics, and metatheory. Affine types guarantee: no use-after-free, no double-free, and no dangling pointers. (Note: memory leaks are possible but controlled by regions.)

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
    | String@r                  (affine string in region r)
    | T₁ × T₂                   (affine product)
    | T₁ + T₂                   (affine sum)
    | T₁ → T₂                   (affine function)
    | &T                        (second-class borrow)
    | Region[r](T)              (region-scoped type)
```

### 1.3 Affinity Classification

**Definition 1.1** (Affine Type):
```
affine : Type → Bool

affine(String@r)     = true
affine(T₁ × T₂)      = affine(T₁) ∨ affine(T₂)
affine(T₁ + T₂)      = affine(T₁) ∨ affine(T₂)
affine(Region[r](T)) = affine(T)
affine(_)            = false
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
    | let x = e₁ in e₂          (let binding - may drop)

    (* Functions *)
    | λ(x:T). e                 (abstraction)
    | e₁ e₂                     (application)

    (* Products *)
    | (e₁, e₂)                  (pair construction)
    | let (x, y) = e₁ in e₂     (pair elimination)
    | π₁(e) | π₂(e)             (projections - allowed!)

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

**Definition 2.3** (Context Merge for Affine):
When branches may differ in usage:
```
merge(Γ₁, Γ₂) = λx.
  match (Γ₁(x), Γ₂(x)) with
  | ((T, ⊤), (T, _)) → (T, ⊤)    (* Used in one branch = used *)
  | ((T, _), (T, ⊤)) → (T, ⊤)
  | ((T, ⊥), (T, ⊥)) → (T, ⊥)    (* Unused in both = unused *)
```

### 2.2 Region Environment

```
R ⊆ RegionName    (set of active regions)
```

### 2.3 Affine Typing Judgment

The central judgment has the form:
```
R; Γ ⊢ e : T ⊣ Γ'
```

Read: "Under active regions R and input context Γ, expression e has type T, producing output context Γ'."

**Key Difference from Linear**: Affine bindings do NOT need to be used. Only double-use is forbidden.

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
affine(T) = true
─────────────────────────────────────────  (T-Var-Aff)
R; Γ ⊢ x : T ⊣ mark(Γ, x)


lookup(Γ, x) = (T, _)
affine(T) = false
─────────────────────────────────────────  (T-Var-Unr)
R; Γ ⊢ x : T ⊣ Γ
```

**Note**: Accessing an already-used affine variable (lookup returns ⊤) is forbidden. But NOT accessing it is fine.

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
R; extend(Γ', x, T₁) ⊢ e₂ : T₂ ⊣ Γ'', x : T₁ @ _
                                              ↑ NO REQUIREMENT!
──────────────────────────────────────────────────────────  (T-Let-Aff)
R; Γ ⊢ let x = e₁ in e₂ : T₂ ⊣ Γ''
```

**Key Difference**: The binding x does NOT need to be used. Implicit drop is allowed.

#### 2.4.5 Functions

```
fresh(Γ, x)
R; extend(Γ, x, T₁) ⊢ e : T₂ ⊣ Γ', x : T₁ @ _
                                          ↑ Parameter may be unused
─────────────────────────────────────────────────  (T-Lam-Aff)
R; Γ ⊢ λ(x:T₁). e : T₁ → T₂ ⊣ Γ'


R; Γ ⊢ e₁ : T₁ → T₂ ⊣ Γ'
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


R; Γ ⊢ e : T₁ × T₂ ⊣ Γ'
───────────────────────────────────  (T-Fst-Aff)
R; Γ ⊢ π₁(e) : T₁ ⊣ Γ'


R; Γ ⊢ e : T₁ × T₂ ⊣ Γ'
───────────────────────────────────  (T-Snd-Aff)
R; Γ ⊢ π₂(e) : T₂ ⊣ Γ'
```

**Key Difference**: Projections are ALWAYS allowed. The discarded component is implicitly dropped.

#### 2.4.7 Sums

```
R; Γ ⊢ e : T₁ ⊣ Γ'
─────────────────────────────────────  (T-Inl)
R; Γ ⊢ inl[T₂](e) : T₁ + T₂ ⊣ Γ'


R; Γ ⊢ e : T₁ + T₂ ⊣ Γ'
R; extend(Γ', x, T₁) ⊢ e₁ : T ⊣ Γ₁
R; extend(Γ', y, T₂) ⊢ e₂ : T ⊣ Γ₂
Γ_out = merge(Γ₁, Γ₂)                          ← BRANCHES MAY DIFFER
─────────────────────────────────────────────────────────────────  (T-Case-Aff)
R; Γ ⊢ case e of inl(x) → e₁; inr(y) → e₂ : T ⊣ Γ_out
```

**Key Difference**: Branches may consume different resources. We merge conservatively.

#### 2.4.8 Conditionals

```
R; Γ ⊢ e₁ : Bool ⊣ Γ'
R; Γ' ⊢ e₂ : T ⊣ Γ₂
R; Γ' ⊢ e₃ : T ⊣ Γ₃
Γ_out = merge(Γ₂, Γ₃)                          ← BRANCHES MAY DIFFER
───────────────────────────────────────────────────────────────  (T-If-Aff)
R; Γ ⊢ if e₁ then e₂ else e₃ : T ⊣ Γ_out
```

**Key Difference**: Branches may consume different affine resources.

#### 2.4.9 Regions

```
r ∉ R
R ∪ {r}; Γ ⊢ e : T ⊣ Γ'
¬mentions(T, r)
─────────────────────────────────────────────  (T-Region)
R; Γ ⊢ region r { e } : T ⊣ Γ'
```

Regions work the same as in linear - they provide bulk deallocation.

#### 2.4.10 Borrowing

```
lookup(Γ, x) = (T, ⊥)
─────────────────────────────────  (T-Borrow)
R; Γ ⊢ &x : &T ⊣ Γ
```

#### 2.4.11 Resource Management

```
affine(T) = true
R; Γ ⊢ e : T ⊣ Γ'
───────────────────────────────────  (T-Drop)
R; Γ ⊢ drop(e) : Unit ⊣ Γ'


affine(T) = false
R; Γ ⊢ e : T ⊣ Γ'
───────────────────────────────────  (T-Copy)
R; Γ ⊢ copy(e) : T × T ⊣ Γ'
```

---

## Part III: Implicit Drop Semantics

### 3.1 Scope-End Drop Insertion

In Affine Ephapax, unused affine bindings are implicitly dropped at scope exit.

**Definition 3.1** (Drop Insertion):
At the end of a let scope, for each `(x : T @ ⊥)` where `affine(T)`:
```
let x = e₁ in e₂  ≡  let x = e₁ in (let _ = e₂ in drop(x))
                     if x unused in e₂ and affine(T)
```

This is a compile-time transformation, not a runtime check.

### 3.2 Branch Reconciliation

When branches differ, the compiler inserts drops:

```
if cond then
  use(x)        (* x consumed *)
else
  ()            (* x NOT consumed → insert drop(x) *)
```

Transforms to:
```
if cond then
  use(x)
else
  drop(x); ()
```

---

## Part IV: Operational Semantics

### 4.1 Runtime Structures

Same as Linear Ephapax:
```
H : Loc → Cell
Cell ::= ⟨data : String, region : RegionName, status : {Alloc, Freed}⟩
ρ : Var → Value
σ = ⟨H, R, ρ, e⟩
```

### 4.2 Small-Step Reduction

Most rules are identical to Linear Ephapax. Key difference:

#### 4.2.1 Scope Exit with Implicit Drop

```
is_value(v)
x unused in current scope (determined at compile time)
H' = implicit_drop(H, ρ(x))
─────────────────────────────────────────────────────────
⟨H, R, ρ, scope_exit(x, v)⟩ → ⟨H', R, ρ, v⟩
```

In practice, the compiler inserts explicit drops, so at runtime this is just:
```
⟨H, R, ρ, drop(ℓ); v⟩ → ⟨H[ℓ ↦ Freed], R, ρ, v⟩
```

---

## Part V: Metatheory

### 5.1 Type Safety

**Theorem 5.1** (Progress):
If `R; Γ ⊢ e : T ⊣ Γ'` and `e` is not a value, then e can step.

**Theorem 5.2** (Preservation):
If `R; Γ ⊢ e : T ⊣ Γ'` and `e → e'`, then there exists Γ'' such that `R; Γ'' ⊢ e' : T ⊣ Γ'`.

### 5.2 Affinity Preservation

**Theorem 5.3** (At-Most-Once Use):
If `R; Γ ⊢ e : T ⊣ Γ'`, then for every `(x : U @ ⊥) ∈ Γ` where `affine(U)`, at most one use of x occurs in e.

**Non-Theorem** (Exactly-Once):
Unlike linear types, we do NOT have: every affine variable is used exactly once. Zero uses are permitted.

### 5.3 Memory Safety

**Theorem 5.4** (No Use-After-Free):
Well-typed Affine Ephapax programs cannot access freed memory.

**Proof**: Same as linear - once marked used, a binding cannot be accessed again.

**Theorem 5.5** (No Double-Free):
A location cannot be freed twice.

**Proof**: Same as linear - affine prevents multiple consumption.

**Non-Theorem** (No Leaks):
Affine Ephapax does NOT guarantee no leaks at the language level. However:
- Regions provide bulk deallocation
- Implicit drops handle most cases
- Only truly orphaned allocations can leak

**Theorem 5.6** (No Region Escapes):
Same as linear - region-scoped types cannot escape.

### 5.4 Relationship to Linear

**Theorem 5.7** (Linear ⊂ Affine):
Every Linear Ephapax program is a valid Affine Ephapax program:
```
R; Γ ⊢_Lin e : T ⊣ Γ'  ⟹  R; Γ ⊢_Aff e : T ⊣ Γ''
```

**Theorem 5.8** (Affine ⊄ Linear):
Some Affine programs are not Linear:
```
let x = String.new@r("unused") in 42    (* Affine: OK *)
                                         (* Linear: ERROR - x unused *)
```

---

## Part VI: Decidability and Complexity

**Theorem 6.1** (Type Checking Decidability):
Type checking for Affine Ephapax is decidable in O(n) time.

**Proof**:
Same as linear. The merge operation for branches adds only constant overhead per conditional.

---

## Part VII: Affine Logic Correspondence

### 7.1 Curry-Howard

| Affine Ephapax | Affine Logic |
|----------------|--------------|
| T₁ × T₂ | A ⊗ B (tensor) |
| T₁ + T₂ | A ⊕ B (plus) |
| T₁ → T₂ | A ⊸ B (lollipop) |
| Unit | 1 |
| Unrestricted T | !A |
| Implicit drop | Weakening |

### 7.2 Structural Rules

Affine logic = Linear logic + Weakening:

```
Γ ⊢ B
─────────  (Weakening)
Γ, A ⊢ B
```

This allows discarding unused hypotheses.

---

## Part VIII: Categorical Semantics

Affine types form a *symmetric monoidal closed category with discards*:

- Objects: Types
- Morphisms: Terms `x:A ⊢ e : B`
- Tensor (⊗): Product types
- Internal Hom (⊸): Function types
- Unit (I): Unit type
- Discard: Natural transformation `!_A : A → I`

The discard maps allow weakening in the categorical setting.

---

## Part IX: Comparison Table

| Property | Linear Ephapax | Affine Ephapax |
|----------|----------------|----------------|
| Use count | Exactly 1 | At most 1 |
| Implicit drop | ✗ | ✓ |
| Unused bindings | ERROR | OK (auto-dropped) |
| Asymmetric branches | ✗ | ✓ |
| Projections | Restricted | Unrestricted |
| Memory leaks | Prevented | Possible (rare) |
| Use-after-free | Prevented | Prevented |
| Double-free | Prevented | Prevented |
| Ease of use | Stricter | More permissive |

---

*End of Affine Ephapax Specification*
