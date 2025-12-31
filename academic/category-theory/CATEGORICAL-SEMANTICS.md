# Categorical Semantics of Ephapax

## A Linear Type Theory in Symmetric Monoidal Categories

**Version**: 1.0.0
**Date**: 2025-12-31
**SPDX-License-Identifier**: EUPL-1.2

---

## Abstract

We develop a categorical semantics for Ephapax's linear type system using symmetric monoidal closed categories (SMCCs). This provides a mathematical foundation for understanding the type system's structure and enables abstract reasoning about program equivalence.

---

## 1. Introduction

Categorical semantics interprets:
- Types as objects in a category
- Terms as morphisms
- Type constructors as functors
- Typing rules as natural transformations

For linear type systems, the appropriate setting is *symmetric monoidal closed categories* (SMCCs).

---

## 2. Categorical Preliminaries

### 2.1 Categories

**Definition 2.1** (Category):
A category C consists of:
- Objects: Ob(C)
- Morphisms: For each A, B ∈ Ob(C), a set Hom(A, B)
- Composition: ∘ : Hom(B, C) × Hom(A, B) → Hom(A, C)
- Identity: For each A, id_A ∈ Hom(A, A)

Subject to associativity and identity laws.

### 2.2 Monoidal Categories

**Definition 2.2** (Monoidal Category):
A monoidal category (C, ⊗, I, α, λ, ρ) is a category C with:
- Tensor product: ⊗ : C × C → C
- Unit object: I ∈ Ob(C)
- Associator: α_{A,B,C} : (A ⊗ B) ⊗ C → A ⊗ (B ⊗ C)
- Left unitor: λ_A : I ⊗ A → A
- Right unitor: ρ_A : A ⊗ I → A

These must satisfy coherence conditions (pentagon and triangle diagrams).

### 2.3 Symmetric Monoidal Categories

**Definition 2.3** (SMC):
A symmetric monoidal category adds:
- Symmetry: σ_{A,B} : A ⊗ B → B ⊗ A

With σ_{B,A} ∘ σ_{A,B} = id and coherence with associators.

### 2.4 Closed Categories

**Definition 2.4** (Monoidal Closed Category):
A monoidal category is closed if for each A, the functor (– ⊗ A) has a right adjoint (A ⊸ –):

```
Hom(C ⊗ A, B) ≅ Hom(C, A ⊸ B)
```

This adjunction gives the internal hom (linear function space).

---

## 3. Interpretation of Ephapax Types

### 3.1 Base Types

| Ephapax Type | Categorical Interpretation |
|--------------|---------------------------|
| Unit | Terminal object 1 (or I) |
| Bool | 1 + 1 |
| I32 | Fixed object Z₃₂ |

### 3.2 Type Constructors

| Constructor | Categorical Operation |
|-------------|----------------------|
| T₁ × T₂ | Tensor product ⊗ |
| T₁ + T₂ | Coproduct + |
| T₁ → T₂ | Internal hom ⊸ |

### 3.3 The Linear/Unrestricted Split

Ephapax has two kinds of types:
- Linear types: Interpreted in an SMCC L
- Unrestricted types: Interpreted in a CCC C

The connection uses a comonad ! : L → L (the "of course" modality):

```
!A = Free commutative comonoid on A
```

With natural transformations:
- ε : !A → A (dereliction)
- δ : !A → !!A (digging)

---

## 4. Interpretation of Typing Judgments

### 4.1 Contexts as Tensors

A context Γ = x₁:A₁, ..., xₙ:Aₙ is interpreted as:

```
⟦Γ⟧ = ⟦A₁⟧ ⊗ ... ⊗ ⟦Aₙ⟧
```

### 4.2 Typing Judgments as Morphisms

A judgment `Γ ⊢ e : A` is interpreted as a morphism:

```
⟦e⟧ : ⟦Γ⟧ → ⟦A⟧
```

### 4.3 Context Threading

Ephapax's context threading `R; Γ ⊢ e : T ⊣ Γ'` requires a refined interpretation:

```
⟦e⟧ : ⟦Γ⟧ → ⟦T⟧ ⊗ ⟦Γ'⟧
```

The output context Γ' represents "leftover" resources.

For linear variables that are consumed:
```
⟦Γ'⟧ = ⟦Γ \ consumed⟧
```

---

## 5. Interpretation of Typing Rules

### 5.1 Identity and Weakening

**Identity (Variables)**:
```
Γ, x:A, Γ' ⊢ x : A
```

Interpreted as projection:
```
⟦x⟧ = π₂ ∘ π₁ : ⟦Γ⟧ ⊗ A ⊗ ⟦Γ'⟧ → A
```

For linear variables, this "uses up" the A component.

### 5.2 Tensor (Products)

**Pair Introduction**:
```
Γ₁ ⊢ e₁ : A    Γ₂ ⊢ e₂ : B
───────────────────────────
   Γ₁, Γ₂ ⊢ (e₁, e₂) : A ⊗ B
```

Interpreted as:
```
⟦(e₁, e₂)⟧ = ⟦e₁⟧ ⊗ ⟦e₂⟧ : ⟦Γ₁⟧ ⊗ ⟦Γ₂⟧ → A ⊗ B
```

### 5.3 Internal Hom (Functions)

**Lambda Abstraction**:
```
Γ, x:A ⊢ e : B
─────────────────
Γ ⊢ λx.e : A ⊸ B
```

Using the adjunction:
```
Hom(⟦Γ⟧ ⊗ A, B) ≅ Hom(⟦Γ⟧, A ⊸ B)
```

We have:
```
⟦e⟧ : ⟦Γ⟧ ⊗ A → B
⟦λx.e⟧ = curry(⟦e⟧) : ⟦Γ⟧ → A ⊸ B
```

**Application**:
```
Γ₁ ⊢ e₁ : A ⊸ B    Γ₂ ⊢ e₂ : A
──────────────────────────────────
      Γ₁, Γ₂ ⊢ e₁ e₂ : B
```

Interpreted as:
```
⟦e₁ e₂⟧ = eval ∘ (⟦e₁⟧ ⊗ ⟦e₂⟧) : ⟦Γ₁⟧ ⊗ ⟦Γ₂⟧ → B
```

Where eval : (A ⊸ B) ⊗ A → B is the counit of the adjunction.

### 5.4 Coproduct (Sums)

**Injection**:
```
⟦inl(e)⟧ = inl ∘ ⟦e⟧ : ⟦Γ⟧ → A + B
⟦inr(e)⟧ = inr ∘ ⟦e⟧ : ⟦Γ⟧ → A + B
```

**Case Analysis**:
```
Γ ⊢ e : A + B
Γ', x:A ⊢ e₁ : C
Γ', y:B ⊢ e₂ : C
───────────────────────
Γ, Γ' ⊢ case e of ... : C
```

Using the universal property of coproducts:
```
⟦case⟧ = [⟦e₁⟧, ⟦e₂⟧] ∘ distrib ∘ (⟦e⟧ ⊗ id)
```

Where distrib : (A + B) ⊗ C → (A ⊗ C) + (B ⊗ C).

### 5.5 Exponential (Unrestricted)

For unrestricted types, we use the comonad !:

**Dereliction**: !A → A
```
der : !A → A
```

Allows using an unrestricted resource linearly.

**Promotion**: A → !A (in limited contexts)
```
prom : !Γ ⊢ A → !Γ ⊢ !A
```

---

## 6. Region Interpretation

### 6.1 Indexed Categories

Regions can be modeled using indexed/fibered categories:

```
R : Region → SMCC
```

For each region r, we have a category R(r) of types scoped to r.

### 6.2 Region Polymorphism

Region abstraction forms a right adjoint:

```
∀r. T ⟦...⟧  ↔  limit over R
```

### 6.3 Region as Graded Monad

Alternatively, regions form a graded monad indexed by region names:

```
T_r : SMCC → SMCC   (for each region r)

η_r : A → T_r(A)    (allocation)
μ : T_r(T_s(A)) → T_{r∪s}(A)   (nesting)
```

The region exit operation:

```
exit_r : T_r(A) → A   (when A doesn't mention r)
```

---

## 7. Soundness and Completeness

### 7.1 Soundness

**Theorem 7.1** (Soundness):
If `Γ ⊢ e : A` is derivable, then ⟦e⟧ : ⟦Γ⟧ → ⟦A⟧ is a well-defined morphism.

*Proof*: By induction on the derivation, showing each rule corresponds to a valid categorical construction. □

### 7.2 Completeness

**Theorem 7.2** (Completeness for Full Abstraction):
For the appropriate SMCC (e.g., coherence spaces):
```
e₁ ≈ e₂  ⟺  ⟦e₁⟧ = ⟦e₂⟧
```

Where ≈ is observational equivalence.

*Status*: Conjectured; requires proof.

### 7.3 Internal Language

**Theorem 7.3**:
The internal language of an SMCC is exactly intuitionistic linear logic / linear λ-calculus.

This establishes Ephapax as the term language for SMCCs (with extensions for regions).

---

## 8. Examples of Models

### 8.1 Coherence Spaces

**Definition**: A coherence space X = (|X|, ⌢_X) is:
- A set |X| of tokens
- A reflexive, symmetric relation ⌢ (coherence)

**Interpretation**:
- Objects: Coherence spaces
- Morphisms: Linear (stable, clique-preserving) maps
- ⊗: Tensor product of coherence spaces
- ⊸: Space of linear maps

### 8.2 Phase Spaces

**Definition**: A phase space is (M, ⊥) where:
- M is a commutative monoid
- ⊥ ⊆ M is a "pole" (set of "false" facts)

Linear propositions interpreted as subsets closed under double orthogonalization.

### 8.3 Quantitative Models

**Definition**: Rel! model:
- Objects: Sets
- Morphisms: Multirelations (bags of pairs)
- Tracks multiplicity of resource usage

This model validates graded linear logic.

---

## 9. Coherence Diagrams

### 9.1 Pentagon (Associativity)

```
        ((A⊗B)⊗C)⊗D
       /             \
      α               α⊗id
     /                 \
(A⊗(B⊗C))⊗D    (A⊗B)⊗(C⊗D)
    |                   |
    α                   α
    |                   |
A⊗((B⊗C)⊗D) ────→ A⊗(B⊗(C⊗D))
              id⊗α
```

This diagram must commute.

### 9.2 Triangle (Unit)

```
    (A⊗I)⊗B
    /      \
   α        ρ⊗id
  /          \
A⊗(I⊗B) ────→ A⊗B
         id⊗λ
```

This diagram must commute.

### 9.3 Naturality of Currying

For the closed structure:
```
Hom(A ⊗ B, C) ────curry──→ Hom(A, B ⊸ C)
     |                            |
   f∘(g⊗h)                     g⊸h∘f
     |                            |
     ↓                            ↓
Hom(A' ⊗ B', C') ──curry─→ Hom(A', B' ⊸ C')
```

---

## 10. Categorical Constructions for Ephapax Features

### 10.1 Second-Class Borrows

Borrows can be modeled as a comonad on types:

```
B : SMCC → SMCC

BA = A    (underlying type)

extract : BA → A    (unrestricted; second-class escape)
duplicate : BA → BBA  (re-borrowing)
```

The "second-class" restriction means borrows don't form morphisms in the usual sense—they're more like effects.

### 10.2 Drop as Counit

The drop operation:
```
drop : A → I
```

For linear types, this is a morphism to the unit object.

The linear type discipline ensures each object has exactly one morphism to I used.

### 10.3 Copy as Diagonal

For unrestricted types:
```
copy : !A → !A ⊗ !A
```

This is the diagonal morphism in the Kleisli category of !.

---

## 11. TODO: Proofs Required

### 11.1 Main Theorems

- [ ] Full proof of soundness theorem
- [ ] Internal language theorem
- [ ] Coherence for region grading

### 11.2 Model Construction

- [ ] Explicit coherence space model for Ephapax
- [ ] Proof of full abstraction (if achievable)
- [ ] Connection to game semantics

### 11.3 Extensions

- [ ] Categorical semantics for polymorphism
- [ ] Enriched categories for effects
- [ ] Double categories for regions

---

## 12. References

1. Barr, M. & Wells, C. (1990). *Category Theory for Computing Science*.

2. Benton, P.N., Bierman, G., de Paiva, V., & Hyland, M. (1993). A term calculus for intuitionistic linear logic. *TLCA*.

3. Seely, R.A.G. (1989). Linear logic, *-autonomous categories and cofree coalgebras. *Contemporary Mathematics*, 92.

4. Mellies, P.-A. (2009). Categorical semantics of linear logic. *Panoramas et Synthèses*, 27.

5. Hasegawa, M. (1999). *Logical predicates for intuitionistic linear type theories*. *TLCA*.

6. Girard, J.-Y. (1987). Linear logic. *Theoretical Computer Science*, 50(1).

---

*End of Categorical Semantics*
