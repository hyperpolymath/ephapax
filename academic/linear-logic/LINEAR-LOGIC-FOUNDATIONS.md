# Linear Logic Foundations of Ephapax

## Curry-Howard Correspondence for Linear Types

**Version**: 1.0.0
**Date**: 2025-12-31
**SPDX-License-Identifier**: EUPL-1.2

---

## 1. Introduction

Ephapax's type system is grounded in *intuitionistic linear logic* (ILL), developed by Girard [1987]. This document establishes the precise correspondence between Ephapax types and linear logic propositions.

---

## 2. Linear Logic Primer

### 2.1 Classical vs. Linear Logic

In classical logic, propositions can be used arbitrarily:
- **Weakening**: If Γ ⊢ B, then Γ, A ⊢ B (unused hypotheses allowed)
- **Contraction**: If Γ, A, A ⊢ B, then Γ, A ⊢ B (hypotheses can be duplicated)

Linear logic rejects both principles for linear propositions:
- Resources must be used **exactly once**
- This models consumption of physical resources

### 2.2 Linear Connectives

| Connective | Name | Ephapax Type |
|------------|------|--------------|
| A ⊗ B | Multiplicative conjunction (tensor) | A × B (product) |
| A ⊕ B | Additive disjunction | A + B (sum) |
| A ⊸ B | Linear implication (lollipop) | A → B (function) |
| !A | Of course (exponential) | Unrestricted A |
| 1 | Multiplicative unit | Unit |

### 2.3 Intuitionistic Linear Logic

Ephapax uses the intuitionistic fragment (no ⅋, ⊥):

```
A, B ::= X | 1 | A ⊗ B | A ⊕ B | A ⊸ B | !A
```

The exponential `!A` marks propositions that can be used unrestrictedly (weakening and contraction allowed).

---

## 3. Curry-Howard Correspondence

### 3.1 Types as Propositions

| Ephapax Type | Linear Logic Proposition | Interpretation |
|--------------|-------------------------|----------------|
| Unit | 1 | Trivially available |
| Bool | !2 | Unrestricted choice |
| I32, I64, F32, F64 | !ℕ, !ℝ | Unrestricted values |
| String@r | X_r | Linear resource in region r |
| T₁ × T₂ | A ⊗ B | Both resources together |
| T₁ + T₂ | A ⊕ B | One resource or the other |
| T₁ → T₂ | A ⊸ B | Resource transformer |
| &T | A | Borrow (derived) |

### 3.2 Expressions as Proofs

Each typing derivation corresponds to a proof in linear logic:

| Typing Rule | Linear Logic Rule |
|-------------|-------------------|
| T-Unit | 1-introduction |
| T-Var-Lin | Axiom (linear hypothesis use) |
| T-Var-Unr | Dereliction (!-elimination) |
| T-Pair | ⊗-introduction |
| T-Fst, T-Snd | ⊗-elimination |
| T-Inl, T-Inr | ⊕-introduction |
| T-Case | ⊕-elimination |
| T-Lam | ⊸-introduction |
| T-App | ⊸-elimination (cut) |

### 3.3 Proof Terms

The Curry-Howard correspondence gives:

```
Types       ↔ Propositions
Expressions ↔ Proofs
Evaluation  ↔ Cut elimination
```

An Ephapax program is a constructive proof that its type is inhabited.

---

## 4. Linear Logic Sequent Calculus

### 4.1 Sequent Form

Linear logic sequents have the form:

```
Γ; Δ ⊢ A
```

Where:
- Γ = unrestricted context (can use contraction/weakening)
- Δ = linear context (must use exactly once)
- A = conclusion

### 4.2 Structural Rules

**Identity**:
```
────────────
A ⊢ A
```

**Cut**:
```
Γ; Δ ⊢ A    Γ; Δ', A ⊢ B
───────────────────────────
      Γ; Δ, Δ' ⊢ B
```

### 4.3 Multiplicative Rules

**Tensor Introduction (⊗R)**:
```
Γ; Δ₁ ⊢ A    Γ; Δ₂ ⊢ B
────────────────────────
   Γ; Δ₁, Δ₂ ⊢ A ⊗ B
```

Corresponds to: `T-Pair`

**Tensor Elimination (⊗L)**:
```
Γ; Δ, A, B ⊢ C
────────────────────
Γ; Δ, A ⊗ B ⊢ C
```

Corresponds to: destructuring let `let (x, y) = e₁ in e₂`

**Linear Implication Introduction (⊸R)**:
```
Γ; Δ, A ⊢ B
─────────────────
Γ; Δ ⊢ A ⊸ B
```

Corresponds to: `T-Lam`

**Linear Implication Elimination (⊸L)**:
```
Γ; Δ₁ ⊢ A    Γ; Δ₂, B ⊢ C
───────────────────────────
  Γ; Δ₁, Δ₂, A ⊸ B ⊢ C
```

Corresponds to: `T-App`

### 4.4 Additive Rules

**Additive Disjunction Introduction (⊕R₁, ⊕R₂)**:
```
Γ; Δ ⊢ A              Γ; Δ ⊢ B
─────────────         ─────────────
Γ; Δ ⊢ A ⊕ B         Γ; Δ ⊢ A ⊕ B
```

Corresponds to: `T-Inl`, `T-Inr`

**Additive Disjunction Elimination (⊕L)**:
```
Γ; Δ, A ⊢ C    Γ; Δ, B ⊢ C
───────────────────────────
    Γ; Δ, A ⊕ B ⊢ C
```

Corresponds to: `T-Case`

Note: Both branches use the **same** linear context Δ. This is the additive (rather than multiplicative) pattern.

### 4.5 Exponential Rules

**Promotion (!R)**:
```
Γ ⊢ A
──────────
Γ ⊢ !A
```

Can only promote when the context is entirely unrestricted.

**Dereliction (!L)**:
```
Γ; Δ, A ⊢ B
─────────────
Γ; Δ, !A ⊢ B
```

Allows using an unrestricted resource linearly.

**Weakening (!W)**:
```
Γ; Δ ⊢ B
─────────────
Γ; Δ, !A ⊢ B
```

**Contraction (!C)**:
```
Γ; Δ, !A, !A ⊢ B
──────────────────
  Γ; Δ, !A ⊢ B
```

---

## 5. Ephapax-Specific Constructs

### 5.1 Regions as Modalities

Region types `String@r` can be viewed as indexed linear propositions:

```
String@r : Prop(Region)
```

The region `r` is a *world* or *stage* in the modal interpretation.

### 5.2 Region Introduction and Elimination

**Region Introduction**:
```
R ∪ {r}; Γ ⊢ e : A    A does not mention r
─────────────────────────────────────────────
       R; Γ ⊢ region r { e } : A
```

This is analogous to necessity introduction (□R) in modal logic, but for regions.

**Region Elimination** (implicit):
When exiting a region, all resources scoped to that region are deallocated.

### 5.3 Borrowing as Controlled Weakening

Borrows `&T` provide a form of controlled use without consumption:

```
Γ(x) = T
─────────────
Γ ⊢ &x : &T
```

This is **not** standard linear logic—it's an extension that allows temporary, non-consuming access.

In terms of linear logic, borrowing can be modeled as:
- A comonad operation: `T → T ⊗ &T` (conceptually)
- But Ephapax restricts &T to be second-class

---

## 6. Cut Elimination and Evaluation

### 6.1 Cut Elimination Theorem

**Theorem** (Gentzen, 1935; Girard, 1987):
If `Γ; Δ ⊢ A` is provable in linear logic, it has a cut-free proof.

### 6.2 Computational Interpretation

Cut elimination corresponds to evaluation:

| Cut on | Reduction |
|--------|-----------|
| ⊗ | Let-binding elimination |
| ⊕ | Case reduction |
| ⊸ | Beta reduction |
| ! | Bang-let reduction |

**Example** (Beta reduction as cut elimination):

```
            ⊸R                    Ax
      ─────────────           ─────────
      Γ ⊢ λx.e : A⊸B         Δ ⊢ v : A
      ─────────────────────────────────  cut
              Γ, Δ ⊢ (λx.e) v : B

                ↓ cut elimination

                Γ, Δ ⊢ e[v/x] : B
```

### 6.3 Strong Normalization

**Theorem**: Cut elimination in intuitionistic linear logic terminates.

**Corollary**: Ephapax evaluation terminates for the pure fragment (no recursion).

---

## 7. Semantics

### 7.1 Coherence Spaces (Girard)

Linear logic has a denotational semantics in *coherence spaces*:
- Objects: coherence spaces (sets with coherence relation)
- Morphisms: linear functions (preserving coherence)
- ⊗: tensor product of coherence spaces
- ⊸: space of linear functions

### 7.2 Game Semantics

Linear logic also has game-semantic models:
- Types = Games
- Programs = Strategies
- Linear implication = Game composition
- Tensor = Parallel game play

### 7.3 Resource Semantics

For Ephapax specifically:
- `String@r` = Memory cell in region r
- `T₁ × T₂` = Both resources
- `T₁ + T₂` = One or the other
- `T₁ → T₂` = Resource transformation
- Region = Allocation arena

---

## 8. Extensions and Variations

### 8.1 Bounded Linear Logic

Ephapax could be extended with *bounded* exponentials:

```
!_n A    -- Can use A at most n times
```

This would allow fine-grained multiplicity control.

### 8.2 Graded Linear Logic

A further extension uses *semirings* for multiplicities:

```
A^r    -- Use A with multiplicity r ∈ R
```

Where R is a semiring (e.g., ℕ, {0, 1, ω}).

Linear Haskell uses this approach with multiplicities {1, Many}.

### 8.3 Differential Linear Logic

Girard's differential linear logic adds:
- Differentiation: ∂A
- Taylor expansion of proofs

This could model incremental computation.

---

## 9. Relationship to Other Systems

### 9.1 Affine Logic

Affine types allow weakening (use ≤ 1 times) but not contraction.
- Rust uses affine types (move semantics)
- Ephapax uses linear types (use = 1 time)

Ephapax is stricter: resources MUST be consumed.

### 9.2 Relevant Logic

Relevant logic allows contraction but not weakening:
- Resources can be duplicated
- But must be used at least once

### 9.3 Ordered Logic

Ordered (non-commutative) linear logic restricts exchange:
- Resources must be used in order
- Models stack-based computation

---

## 10. TODO: Future Work

### 10.1 Proof-Theoretic

- [ ] Formalize cut elimination for Ephapax in Coq
- [ ] Prove strong normalization
- [ ] Establish categorical semantics (linear categories)

### 10.2 Extensions

- [ ] Add polymorphism (System F with linear types)
- [ ] Add dependent types (Linear LF)
- [ ] Add effects (linear effect systems)

### 10.3 Verification

- [ ] Prove Curry-Howard correspondence formally
- [ ] Connect to separation logic (see separation-logic/)

---

## References

1. Girard, J.-Y. (1987). Linear logic. *Theoretical Computer Science*, 50(1), 1-101.

2. Wadler, P. (1990). Linear types can change the world! In *Programming Concepts and Methods*.

3. Abramsky, S. (1993). Computational interpretations of linear logic. *Theoretical Computer Science*, 111(1-2), 3-57.

4. Barber, A. (1996). *Dual Intuitionistic Linear Logic*. PhD thesis, University of Edinburgh.

5. Benton, P.N. (1995). A mixed linear and non-linear logic: Proofs, terms and models. In *CSL*.

6. Girard, J.-Y., Lafont, Y., & Taylor, P. (1989). *Proofs and Types*. Cambridge University Press.

---

*End of Linear Logic Foundations*
