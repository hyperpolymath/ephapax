# Separation Logic Connection

## Ephapax and Separation Logic: A Unified Perspective

**Version**: 1.0.0
**Date**: 2025-12-31
**SPDX-License-Identifier**: EUPL-1.2

---

## Abstract

We establish a formal connection between Ephapax's linear type system and separation logic. This connection provides: (1) an alternative semantic foundation for Ephapax, (2) techniques for reasoning about Ephapax programs using separation logic tools, and (3) insights for extending Ephapax with separation-style permissions.

---

## 1. Introduction

Separation logic [Reynolds, 2002; O'Hearn, 2019] is a Hoare logic extension for reasoning about programs with mutable state. Its key innovation is the *separating conjunction* (∗), which asserts that the heap can be split into disjoint parts.

Linear types and separation logic share a common foundation:
- Both manage resources (heap cells, permissions)
- Both prevent aliasing/sharing errors
- Both have roots in linear logic

We explore this connection in depth.

---

## 2. Separation Logic Primer

### 2.1 Assertions

Separation logic assertions describe heap states:

```
P, Q ::= emp                    (empty heap)
       | e ↦ v                  (cell at e contains v)
       | P ∗ Q                  (separating conjunction)
       | P ∧ Q                  (classical conjunction)
       | P —∗ Q                  (separating implication / magic wand)
       | ∀x. P | ∃x. P          (quantifiers)
```

### 2.2 Key Connective: Separating Conjunction

```
(P ∗ Q)(h) ≡ ∃h₁, h₂. h = h₁ ⊎ h₂ ∧ P(h₁) ∧ Q(h₂)
```

The heap h is partitioned into disjoint parts h₁ and h₂, with P holding on h₁ and Q on h₂.

### 2.3 Frame Rule

The frame rule enables local reasoning:

```
    {P} c {Q}
─────────────────    (Frame)
{P ∗ R} c {Q ∗ R}
```

If c transforms P to Q, and R describes disjoint heap, then c preserves R.

### 2.4 Separation Logic Rules

**Allocation**:
```
{emp} x := alloc(v) {x ↦ v}
```

**Deallocation**:
```
{x ↦ v} free(x) {emp}
```

**Load**:
```
{x ↦ v} y := [x] {x ↦ v ∧ y = v}
```

**Store**:
```
{x ↦ _} [x] := v {x ↦ v}
```

---

## 3. Linear Types as Separation

### 3.1 Types as Predicates

We interpret Ephapax types as separation logic assertions:

| Ephapax Type | Separation Logic Interpretation |
|--------------|--------------------------------|
| Unit | emp |
| Bool | pure(b) ≡ emp ∧ b ∈ {true, false} |
| I32 | pure(n) ≡ emp ∧ n ∈ Z₃₂ |
| String@r | ∃ℓ, s. ℓ ↦_r (s) |
| T₁ × T₂ | ⟦T₁⟧ ∗ ⟦T₂⟧ |
| T₁ + T₂ | ⟦T₁⟧ ∨ ⟦T₂⟧ (exclusive) |
| T₁ → T₂ | ⟦T₁⟧ —∗ ⟦T₂⟧ |
| &T | ∃ℓ. ℓ ↦ v ∧ ⟦T⟧(v) (shared, not exclusive) |

### 3.2 Products as Separating Conjunction

The key insight: linear products correspond to separating conjunction.

**Ephapax**:
```
T₁ × T₂  (must use both components)
```

**Separation Logic**:
```
⟦T₁⟧ ∗ ⟦T₂⟧  (heap split into T₁-part and T₂-part)
```

### 3.3 Functions as Separating Implication

**Ephapax**:
```
T₁ → T₂  (consumes T₁, produces T₂)
```

**Separation Logic**:
```
⟦T₁⟧ —∗ ⟦T₂⟧  (given heap satisfying T₁, produces heap satisfying T₂)
```

The magic wand —∗ captures the "resource transformer" nature of linear functions.

### 3.4 Context as Separating Conjunction

A typing context Γ = x₁:T₁, ..., xₙ:Tₙ corresponds to:

```
⟦Γ⟧ = ⟦T₁⟧ ∗ ⟦T₂⟧ ∗ ... ∗ ⟦Tₙ⟧
```

Each binding owns a disjoint portion of the heap.

---

## 4. Typing Rules as Proof Rules

### 4.1 Correspondence

Each Ephapax typing rule corresponds to a separation logic proof rule:

**T-Pair ↔ ∗-Introduction**:
```
Ephapax:                      Separation Logic:
Γ₁ ⊢ e₁ : T₁                 {P₁} e₁ {Q₁}
Γ₂ ⊢ e₂ : T₂                 {P₂} e₂ {Q₂}
──────────────────            ───────────────────
Γ₁, Γ₂ ⊢ (e₁, e₂) : T₁ × T₂   {P₁ ∗ P₂} (e₁, e₂) {Q₁ ∗ Q₂}
```

**T-Let ↔ Sequential Composition**:
```
Ephapax:                      Separation Logic:
Γ ⊢ e₁ : T₁                   {P} e₁ {Q}
Γ', x:T₁ ⊢ e₂ : T₂            {Q ∗ R} e₂ {S}
────────────────────          ─────────────────────
Γ, Γ' ⊢ let x = e₁ in e₂ : T₂   {P ∗ R} let x = e₁ in e₂ {S}
```

**T-App ↔ Modus Ponens with ∗**:
```
Ephapax:                      Separation Logic:
Γ₁ ⊢ f : T₁ → T₂              {⟦T₁⟧ —∗ ⟦T₂⟧} (function spec)
Γ₂ ⊢ e : T₁                   {⟦T₁⟧} (argument)
─────────────────              ────────────────────────
Γ₁, Γ₂ ⊢ f e : T₂              {⟦T₁⟧ ∗ (⟦T₁⟧ —∗ ⟦T₂⟧)} f e {⟦T₂⟧}
```

### 4.2 Frame Rule Correspondence

The separation logic frame rule corresponds to context extension:

**Ephapax** (implicit frame):
If Γ ⊢ e : T and Γ' contains only unrestricted types, then Γ, Γ' ⊢ e : T.

**Separation Logic**:
{P} c {Q} ⟹ {P ∗ R} c {Q ∗ R}

Linear types automatically enforce the frame property for linear resources.

---

## 5. Region Logic

### 5.1 Regions as Heap Partitions

Regions in Ephapax correspond to heap partitions in separation logic:

```
⟦region r { e }⟧ ≈ ∃h_r. (h = h_r ⊎ h_rest) ∧ ⟦e⟧(h_r) ∧ (at end, h_r = emp)
```

### 5.2 Region Entry

```
{P} region r { ... } {Q}
```

Entering a region creates a fresh heap partition for region r.

### 5.3 Region Exit

```
{P ∗ (r-allocations)} region r { v } {P}
```

Exiting a region deallocates all r-tagged memory, leaving the original P.

### 5.4 No-Escape as Framing

The region no-escape property corresponds to:

```
{P} e {Q ∗ R}  where R mentions only region r
──────────────────────────────────────────────
{P} region r { e } {Q}   (R deallocated, cannot escape)
```

---

## 6. Formal Translation

### 6.1 Translation Function

Define ⟦−⟧ : Type → SepLogicAssertion:

```
⟦Unit⟧(v) = v = () ∧ emp
⟦Bool⟧(v) = v ∈ {true, false} ∧ emp
⟦I32⟧(v) = v ∈ Z₃₂ ∧ emp
⟦String@r⟧(v) = ∃ℓ, s. v = ℓ ∧ ℓ ↦_r s
⟦T₁ × T₂⟧(v) = ∃v₁, v₂. v = (v₁, v₂) ∧ ⟦T₁⟧(v₁) ∗ ⟦T₂⟧(v₂)
⟦T₁ + T₂⟧(v) = (∃v'. v = inl(v') ∧ ⟦T₁⟧(v')) ∨ (∃v'. v = inr(v') ∧ ⟦T₂⟧(v'))
⟦T₁ → T₂⟧(v) = ∀v'. ⟦T₁⟧(v') —∗ ⟦T₂⟧(v v')
⟦&T⟧(v) = ∃v'. ⟦T⟧(v') ∧ v = borrow(v')  (weak assertion, doesn't own)
```

### 6.2 Context Translation

```
⟦x₁:T₁, ..., xₙ:Tₙ⟧ = ⟦T₁⟧(x₁) ∗ ... ∗ ⟦Tₙ⟧(xₙ)
```

### 6.3 Judgment Translation

**Theorem 6.1** (Soundness of Translation):
If `R; Γ ⊢ e : T ⊣ Γ'` in Ephapax, then:
```
{⟦Γ⟧} e {∃v. v = result ∧ ⟦T⟧(v) ∗ ⟦Γ'⟧}
```

In separation logic, where ⟦Γ'⟧ reflects consumed resources.

---

## 7. Borrowing and Permissions

### 7.1 Fractional Permissions

Separation logic can express fractional permissions:

```
ℓ ↦_{π} v    where π ∈ (0, 1]
```

- π = 1: Full permission (read/write)
- π < 1: Partial permission (read only)
- π₁ + π₂ ≤ 1: Permissions must not exceed 1

### 7.2 Ephapax Borrows as Fractions

A borrow in Ephapax can be modeled as:

```
⟦&T⟧ ≈ ∃v, ℓ, π. ℓ ↦_{π} v ∧ π < 1
```

The original owner retains 1 - π permission.

### 7.3 Future Extension: Fractional Borrows

Ephapax could be extended with fractional permissions:

```
&(1/2) T    -- Half permission (can split again)
&(1/4) T    -- Quarter permission
```

Separation logic provides the semantic foundation.

---

## 8. Concurrent Separation Logic

### 8.1 CSL Extension

Concurrent separation logic (CSL) adds rules for parallel composition:

```
{P₁} c₁ {Q₁}    {P₂} c₂ {Q₂}
────────────────────────────  (Parallel)
  {P₁ ∗ P₂} c₁ || c₂ {Q₁ ∗ Q₂}
```

### 8.2 Linear Channels

If Ephapax adds linear channels:

```
Chan[T]  -- Linear channel carrying T
send : Chan[T] → T → Unit
recv : Chan[T] → T
```

The CSL correspondence:

```
⟦Chan[T]⟧ = ∃endpoint. channel_resource(endpoint)
```

Linear ownership of the channel endpoint ensures race-freedom.

### 8.3 Ownership Transfer

Sending on a linear channel transfers ownership:

```
{⟦Chan[T]⟧(c) ∗ ⟦T⟧(v)} send(c, v) {⟦Chan[T]⟧(c)}
```

The resource ⟦T⟧(v) moves from sender to receiver.

---

## 9. Iris and Higher-Order Separation Logic

### 9.1 Iris Framework

Iris [Jung et al., 2018] is a state-of-the-art higher-order concurrent separation logic framework. Key features:

- Impredicative invariants
- Ghost state
- Logical atomicity
- Mechanized in Coq

### 9.2 Ephapax in Iris

Ephapax could be verified using Iris:

```coq
(* Iris-style specification *)
Definition ephapax_string_concat_spec : iProp :=
  ∀ ℓ₁ ℓ₂ s₁ s₂ r,
    {{{ ℓ₁ ↦[r] s₁ ∗ ℓ₂ ↦[r] s₂ }}}
      string_concat ℓ₁ ℓ₂
    {{{ ℓ₃, RET ℓ₃; ℓ₃ ↦[r] (s₁ ++ s₂) }}}.
```

### 9.3 Benefits of Iris Formalization

1. **Machine-checked proofs**: Higher confidence than paper proofs
2. **Compositional reasoning**: Modular verification
3. **Concurrency support**: If Ephapax adds parallelism
4. **Existing libraries**: Reuse Iris proof infrastructure

---

## 10. Relationship to Bunched Implications (BI)

### 10.1 BI Logic

Separation logic is based on bunched implications (BI) [O'Hearn & Pym, 1999]:

- Combines additive (∧, →) and multiplicative (∗, —∗) connectives
- Linear logic is a fragment of BI
- Separation logic adds the heap semantics

### 10.2 BI Semantics

A BI model consists of:
- A set W of worlds (heap states)
- A monoidal structure (W, ⊗, ε) for separating conjunction
- Interpretations of ∗, —∗, emp

Ephapax's type system can be understood as the term language for a specific BI model.

---

## 11. Proof Strategies

### 11.1 Symbolic Execution

Use separation logic for symbolic execution of Ephapax programs:

```
Initial: {⟦Γ⟧}
After let x = String.new@r("hi"):
  {⟦Γ⟧ ∗ ∃ℓ. x = ℓ ∧ ℓ ↦_r "hi"}
After String.len(&x):
  {⟦Γ⟧ ∗ ∃ℓ. x = ℓ ∧ ℓ ↦_r "hi" ∧ result = 2}
```

### 11.2 Verification Conditions

Generate verification conditions from Ephapax code:

```
vc(let x = e₁ in e₂, P, Q) =
  ∃R. vc(e₁, P, R) ∧ vc(e₂, R ∗ x:⟦T₁⟧, Q)
```

### 11.3 Automation

Existing separation logic tools could be adapted:
- Viper: Permission-based verification
- VeriFast: C verification with separation logic
- Gillian: Multi-language symbolic execution

---

## 12. TODO: Future Work

### 12.1 Formalization

- [ ] Complete translation ⟦−⟧ for all Ephapax constructs
- [ ] Prove soundness theorem formally
- [ ] Mechanize in Coq/Iris

### 12.2 Extensions

- [ ] Add fractional permissions to Ephapax
- [ ] Develop concurrent Ephapax with CSL semantics
- [ ] Integrate with Iris for program verification

### 12.3 Tooling

- [ ] Build separation logic-based analyzer for Ephapax
- [ ] Generate verification conditions automatically
- [ ] Connect to SMT solvers for automation

---

## 13. References

1. Reynolds, J.C. (2002). Separation logic: A logic for shared mutable data structures. *LICS*.

2. O'Hearn, P.W. (2019). Separation logic. *Communications of the ACM*, 62(2).

3. O'Hearn, P.W. & Pym, D.J. (1999). The logic of bunched implications. *Bulletin of Symbolic Logic*, 5(2).

4. Jung, R., Krebbers, R., Jourdan, J.-H., Bizjak, A., Birkedal, L., & Dreyer, D. (2018). Iris from the ground up. *JFP*, 28.

5. Calcagno, C., Distefano, D., O'Hearn, P.W., & Yang, H. (2011). Compositional shape analysis by means of bi-abduction. *JACM*, 58(6).

6. Bornat, R., Calcagno, C., O'Hearn, P.W., & Parkinson, M. (2005). Permission accounting in separation logic. *POPL*.

---

*End of Separation Logic Connection*
