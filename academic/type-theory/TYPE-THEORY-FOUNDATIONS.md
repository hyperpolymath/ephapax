# Ephapax Type Theory Foundations

## Formal Mathematical Treatment

**Version**: 1.0.0
**Date**: 2025-12-31
**SPDX-License-Identifier**: EUPL-1.2

---

## 1. Syntax

### 1.1 Variables and Names

```
x, y, z ∈ Var           (Variables)
r, s, t ∈ RegionName    (Region names)
```

### 1.2 Linearity Annotations

```
l ∈ Linearity ::= Lin | Unr
```

- `Lin`: Linear — must use exactly once
- `Unr`: Unrestricted — may use any number of times

### 1.3 Base Types

```
B ∈ BaseType ::= Unit | Bool | I32 | I64 | F32 | F64
```

### 1.4 Types

```
T, U ∈ Type ::= B                    (Base type)
              | String@r             (Region-scoped string)
              | Ref[l](T)            (Reference with linearity)
              | T → U                (Function type)
              | T × U                (Product type)
              | T + U                (Sum type)
              | Region[r](T)         (Region-scoped type)
              | &T                   (Borrow type)
```

### 1.5 Expressions

```
e ∈ Expr ::= ()                      (Unit value)
           | true | false            (Boolean literals)
           | n                       (Integer literal)
           | x                       (Variable)
           | String.new@r(s)         (String allocation)
           | String.concat(e₁, e₂)   (Concatenation)
           | String.len(e)           (Length)
           | let x = e₁ in e₂        (Let binding)
           | let! x = e₁ in e₂       (Linear let)
           | λ(x:T). e               (Abstraction)
           | e₁ e₂                   (Application)
           | (e₁, e₂)                (Pair)
           | π₁(e) | π₂(e)           (Projections)
           | inl[U](e) | inr[T](e)   (Injections)
           | case e of inl(x)→e₁; inr(y)→e₂  (Case)
           | if e₁ then e₂ else e₃   (Conditional)
           | region r { e }          (Region scope)
           | &e                      (Borrow)
           | drop(e)                 (Explicit drop)
           | copy(e)                 (Explicit copy)
```

### 1.6 Values

```
v ∈ Value ::= () | true | false | n | λ(x:T). e | (v₁, v₂) | inl[U](v) | inr[T](v)
```

---

## 2. Type System

### 2.1 Typing Contexts

A typing context Γ is a list of triples:

```
Γ ::= ∅ | Γ, (x : T, used)
```

where `used ∈ {true, false}` tracks whether the binding has been consumed.

**Definition 2.1** (Context operations):

1. **Lookup**:
   ```
   Γ(x) = T  iff  (x : T, _) ∈ Γ
   ```

2. **Mark used**:
   ```
   Γ[x ↦ used] = { (y : U, u') | (y : U, u) ∈ Γ, u' = used if y = x else u }
   ```

3. **Extension**:
   ```
   Γ, x : T = Γ ∪ {(x : T, false)}
   ```

### 2.2 Linearity Predicate

**Definition 2.2** (Linear type):

```
linear(String@r) = true
linear(Ref[Lin](T)) = true
linear(Region[r](T)) = linear(T)
linear(T × U) = linear(T) ∨ linear(U)
linear(T + U) = linear(T) ∨ linear(U)
linear(_) = false
```

### 2.3 Region Environment

```
R ⊆ RegionName    (Set of active regions)
```

**Definition 2.3** (Active region):
```
active(R, r) ⟺ r ∈ R
```

### 2.4 Typing Judgment

The typing judgment has the form:

```
R; Γ ⊢ e : T ⊣ Γ'
```

Read: "Under active regions R and input context Γ, expression e has type T, producing output context Γ'."

This is a *substructural* typing judgment where the context threading ensures linear resources are tracked.

---

## 3. Typing Rules

### 3.1 Value Rules

```
                    T-Unit
─────────────────────────────────────
   R; Γ ⊢ () : Unit ⊣ Γ


                    T-Bool
─────────────────────────────────────
   R; Γ ⊢ b : Bool ⊣ Γ       (b ∈ {true, false})


                    T-Int
─────────────────────────────────────
   R; Γ ⊢ n : I32 ⊣ Γ
```

### 3.2 Variable Rules

```
Γ(x) = (T, false)    linear(T)
──────────────────────────────────     T-Var-Lin
   R; Γ ⊢ x : T ⊣ Γ[x ↦ used]


Γ(x) = (T, _)    ¬linear(T)
──────────────────────────────────     T-Var-Unr
   R; Γ ⊢ x : T ⊣ Γ
```

### 3.3 String Rules

```
r ∈ R
──────────────────────────────────────     T-StringNew
   R; Γ ⊢ String.new@r(s) : String@r ⊣ Γ


R; Γ ⊢ e₁ : String@r ⊣ Γ'
R; Γ' ⊢ e₂ : String@r ⊣ Γ''
────────────────────────────────────────────     T-StringConcat
   R; Γ ⊢ String.concat(e₁, e₂) : String@r ⊣ Γ''


R; Γ ⊢ &e : &(String@r) ⊣ Γ'
──────────────────────────────────────     T-StringLen
   R; Γ ⊢ String.len(e) : I32 ⊣ Γ'
```

### 3.4 Let Binding Rules

```
R; Γ ⊢ e₁ : T₁ ⊣ Γ'
R; Γ', x : T₁ ⊢ e₂ : T₂ ⊣ (x : T₁, true) :: Γ''
────────────────────────────────────────────────     T-Let
   R; Γ ⊢ let x = e₁ in e₂ : T₂ ⊣ Γ''


linear(T₁)
R; Γ ⊢ e₁ : T₁ ⊣ Γ'
R; Γ', x : T₁ ⊢ e₂ : T₂ ⊣ (x : T₁, true) :: Γ''
────────────────────────────────────────────────     T-LetLin
   R; Γ ⊢ let! x = e₁ in e₂ : T₂ ⊣ Γ''
```

### 3.5 Function Rules

```
R; Γ, x : T₁ ⊢ e : T₂ ⊣ (x : T₁, true) :: Γ
─────────────────────────────────────────────     T-Lam
   R; Γ ⊢ λ(x:T₁). e : T₁ → T₂ ⊣ Γ


R; Γ ⊢ e₁ : T₁ → T₂ ⊣ Γ'
R; Γ' ⊢ e₂ : T₁ ⊣ Γ''
─────────────────────────────────────     T-App
   R; Γ ⊢ e₁ e₂ : T₂ ⊣ Γ''
```

### 3.6 Product Rules

```
R; Γ ⊢ e₁ : T₁ ⊣ Γ'
R; Γ' ⊢ e₂ : T₂ ⊣ Γ''
─────────────────────────────────────     T-Pair
   R; Γ ⊢ (e₁, e₂) : T₁ × T₂ ⊣ Γ''


R; Γ ⊢ e : T₁ × T₂ ⊣ Γ'    ¬linear(T₂)
────────────────────────────────────────     T-Fst
   R; Γ ⊢ π₁(e) : T₁ ⊣ Γ'


R; Γ ⊢ e : T₁ × T₂ ⊣ Γ'    ¬linear(T₁)
────────────────────────────────────────     T-Snd
   R; Γ ⊢ π₂(e) : T₂ ⊣ Γ'
```

### 3.7 Sum Rules

```
R; Γ ⊢ e : T₁ ⊣ Γ'
──────────────────────────────────────     T-Inl
   R; Γ ⊢ inl[T₂](e) : T₁ + T₂ ⊣ Γ'


R; Γ ⊢ e : T₂ ⊣ Γ'
──────────────────────────────────────     T-Inr
   R; Γ ⊢ inr[T₁](e) : T₁ + T₂ ⊣ Γ'


R; Γ ⊢ e : T₁ + T₂ ⊣ Γ'
R; Γ', x : T₁ ⊢ e₁ : U ⊣ (x : T₁, true) :: Γ_final
R; Γ', y : T₂ ⊢ e₂ : U ⊣ (y : T₂, true) :: Γ_final
─────────────────────────────────────────────────────     T-Case
   R; Γ ⊢ case e of inl(x)→e₁; inr(y)→e₂ : U ⊣ Γ_final
```

### 3.8 Conditional Rule

```
R; Γ ⊢ e₁ : Bool ⊣ Γ'
R; Γ' ⊢ e₂ : T ⊣ Γ''
R; Γ' ⊢ e₃ : T ⊣ Γ''
───────────────────────────────────────     T-If
   R; Γ ⊢ if e₁ then e₂ else e₃ : T ⊣ Γ''
```

Note: Both branches must consume the same linear resources (produce the same output context).

### 3.9 Region Rules

```
r ∉ R
R ∪ {r}; Γ ⊢ e : T ⊣ Γ'
T does not mention r
──────────────────────────────────     T-Region
   R; Γ ⊢ region r { e } : T ⊣ Γ'
```

### 3.10 Borrow Rules

```
Γ(x) = (T, false)
──────────────────────────────     T-Borrow
   R; Γ ⊢ &x : &T ⊣ Γ
```

Note: Borrowing does *not* mark the variable as used. The original remains available.

### 3.11 Resource Management Rules

```
linear(T)
R; Γ ⊢ e : T ⊣ Γ'
──────────────────────────────────     T-Drop
   R; Γ ⊢ drop(e) : Unit ⊣ Γ'


¬linear(T)
R; Γ ⊢ e : T ⊣ Γ'
──────────────────────────────────     T-Copy
   R; Γ ⊢ copy(e) : T × T ⊣ Γ'
```

---

## 4. Metatheory

### 4.1 Auxiliary Definitions

**Definition 4.1** (All linear used):
```
all_linear_used(∅) = true
all_linear_used((x : T, used) :: Γ) = (linear(T) ⇒ used) ∧ all_linear_used(Γ)
```

**Definition 4.2** (Context subsumption):
```
Γ' ⊑ Γ  iff  ∀x. Γ(x) = (T, u) ⇒ Γ'(x) = (T, u') ∧ (u ⇒ u')
```

### 4.2 Weakening and Exchange

**Lemma 4.3** (Weakening for unrestricted):
If `R; Γ ⊢ e : T ⊣ Γ'` and `¬linear(U)`, then `R; Γ, x : U ⊢ e : T ⊣ Γ', x : U`.

*Proof*: By induction on the typing derivation. Unrestricted variables do not affect context threading. □

**Lemma 4.4** (Exchange):
If `R; Γ₁, x : T₁, y : T₂, Γ₂ ⊢ e : T ⊣ Γ'`, then `R; Γ₁, y : T₂, x : T₁, Γ₂ ⊢ e : T ⊣ Γ'`.

*Proof*: Context operations are order-independent for distinct variables. □

### 4.3 Substitution

**Lemma 4.5** (Substitution):
If `R; Γ, x : U ⊢ e : T ⊣ Γ', (x : U, true)` and `R; Γ ⊢ v : U ⊣ Γ''` where `v` is a value, then `R; Γ ⊢ e[v/x] : T ⊣ Γ'`.

*Proof*: By induction on the typing derivation for `e`. Key cases:
- If `e = x`, then `T = U` and `e[v/x] = v`.
- If `e = y` for `y ≠ x`, substitution has no effect.
- Other cases follow by IH. □

---

## 5. Type Safety

### 5.1 Progress

**Theorem 5.1** (Progress):
If `R; Γ ⊢ e : T ⊣ Γ'` and `e` is not a value, then there exists `e'` such that `e → e'`.

*Proof sketch*: By induction on the typing derivation.

**Base cases**:
- T-Unit, T-Bool, T-Int: `e` is a value.
- T-Lam: `e` is a value.

**Inductive cases**:
- T-Var: Variables are not values but the semantics reduces them via environment lookup.
- T-App: By IH on `e₁` and `e₂`:
  - If `e₁` is not a value, it can step.
  - If `e₁` is a value and `e₂` is not, `e₂` can step.
  - If both are values, `e₁` must be a lambda (by canonical forms), so beta reduction applies.
- T-If: By IH, either `e₁` steps or `e₁` is a boolean (by canonical forms), enabling conditional reduction.
- Other cases similar. □

### 5.2 Preservation

**Theorem 5.2** (Preservation):
If `R; Γ ⊢ e : T ⊣ Γ'` and `e → e'`, then there exists `Γ''` such that `R; Γ'' ⊢ e' : T ⊣ Γ'`.

*Proof sketch*: By induction on the typing derivation, with case analysis on the reduction rule.

**Key case** (Beta reduction):
- Given: `R; Γ ⊢ (λ(x:U). e₁) v : T ⊣ Γ'`
- From T-App: `R; Γ ⊢ λ(x:U). e₁ : U → T ⊣ Γ₁` and `R; Γ₁ ⊢ v : U ⊣ Γ'`
- From T-Lam: `R; Γ, x : U ⊢ e₁ : T ⊣ (x : U, true) :: Γ`
- By substitution lemma: `R; Γ₁ ⊢ e₁[v/x] : T ⊣ Γ'`

**Key case** (Region exit):
- Given: `R; Γ ⊢ region r { v } : T ⊣ Γ'`
- From T-Region: `R ∪ {r}; Γ ⊢ v : T ⊣ Γ'` and `T` does not mention `r`
- The reduction `region r { v } → v` with memory freed
- Since `T` does not mention `r`, `R; Γ ⊢ v : T ⊣ Γ'` holds. □

### 5.3 Linearity Preservation

**Theorem 5.3** (Linearity):
If `R; Γ ⊢ e : T ⊣ Γ'`, then `all_linear_used(Γ')`.

*Proof*: By induction on the typing derivation.

**Key insight**: Every rule that consumes a linear variable marks it as used in the output context. The threading of contexts ensures this marking persists through evaluation.

**Key case** (T-Var-Lin):
- Premise: `Γ(x) = (T, false)` and `linear(T)`
- Output: `Γ[x ↦ used]`
- The linear variable `x` is now marked used.

**Key case** (T-Case):
- Both branches produce the same `Γ_final`
- This ensures linear resources are consumed consistently regardless of which branch executes. □

---

## 6. Decidability

### 6.1 Type Checking Algorithm

**Theorem 6.1** (Decidability):
Type checking for Ephapax is decidable in time O(n) where n is the size of the expression.

*Proof sketch*:
1. The typing rules are syntax-directed (no overlapping rules for the same expression form)
2. Each rule consumes the expression constructor and recurses on subexpressions
3. Context operations (lookup, mark used) are O(1) with appropriate representation
4. No fixpoint computation is required □

### 6.2 Type Inference

**Conjecture 6.2**: Principal types exist for Ephapax expressions (without explicit type annotations on lambdas).

*Status*: Not yet proven. Requires development of a constraint-based type inference algorithm.

---

## 7. Extensions

### 7.1 Polymorphism

Region polymorphism could be added:

```
∀r. String@r → I32
```

This requires extending the type syntax and adding universal/existential introduction rules.

### 7.2 Recursive Types

Recursive types require careful treatment with linearity:

```
μα. Unit + (T × α)     (List structure)
```

The `fold`/`unfold` operations must preserve linearity.

### 7.3 Multiplicity Polymorphism

Following Linear Haskell, we could add multiplicity variables:

```
∀(p : Mult). (T -[p]-> U) -> (List T -[p]-> List U)
```

---

## 8. TODO: Proof Obligations

The following theorems are stated but require full proofs:

### 8.1 In Coq (formal/Typing.v)

- [ ] `linearity_preservation` (line 197): Proof by induction on typing derivation

### 8.2 In Coq (formal/Semantics.v)

- [ ] `progress` (line 217): Case analysis on expression form
- [ ] `preservation` (line 227): Induction with substitution lemma
- [ ] `memory_safety` (line 254): Follows from linearity
- [ ] `no_leaks` (line 267): Region semantics ensures cleanup

### 8.3 Paper Proofs Needed

- [ ] Canonical forms lemma
- [ ] Substitution lemma (full proof)
- [ ] Context subsumption properties
- [ ] Type inference algorithm correctness (if developed)

---

## References

1. Walker, D. (2005). Substructural Type Systems. In *Advanced Topics in Types and Programming Languages*, Chapter 1.

2. Girard, J.-Y. (1987). Linear logic. *Theoretical Computer Science*, 50(1), 1-101.

3. Wadler, P. (1990). Linear types can change the world! In *Programming Concepts and Methods*.

4. Tofte, M. & Talpin, J.-P. (1997). Region-based memory management. *Information and Computation*, 132(2), 109-176.

5. Bernardy, J.-P. et al. (2018). Linear Haskell: practical linearity in a higher-order polymorphic language. *PACMPL*, 2(POPL).

---

*End of Type Theory Foundations*
