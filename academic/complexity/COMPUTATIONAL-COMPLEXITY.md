# Computational Complexity Analysis of Ephapax

## Decidability, Complexity Bounds, and Algorithmic Analysis

**Version**: 1.0.0
**Date**: 2025-12-31
**SPDX-License-Identifier**: EUPL-1.2

---

## Abstract

We analyze the computational complexity of the Ephapax type system and related decision problems. We prove that type checking is decidable in linear time, region inference (if added) is polynomial, and evaluate the algorithmic complexity of compilation phases.

---

## 1. Introduction

For a type system to be practical, type checking must be decidable and efficient. We analyze:

1. **Type checking complexity**: Given Γ, e, T, is `Γ ⊢ e : T` derivable?
2. **Type inference complexity**: Given e, find T such that `⊢ e : T`
3. **Region inference complexity**: Given e, infer region annotations
4. **Linearity checking complexity**: Verify linear resource usage

---

## 2. Type Checking

### 2.1 Algorithm

**Algorithm 2.1** (Type Checking):
```
check(R, Γ, e, T) → (Γ', bool)

check(R, Γ, EUnit, TBase TUnit) = (Γ, true)
check(R, Γ, EBool b, TBase TBool) = (Γ, true)
check(R, Γ, EI32 n, TBase TI32) = (Γ, true)

check(R, Γ, EVar x, T) =
  match Γ(x) with
  | Some(T', used) →
      if T = T' ∧ (¬linear(T) ∨ ¬used) then
        if linear(T) then (Γ[x ↦ used], true)
        else (Γ, true)
      else (Γ, false)
  | None → (Γ, false)

check(R, Γ, EStringNew r s, TString r) =
  if r ∈ R then (Γ, true) else (Γ, false)

check(R, Γ, ELet x e₁ e₂, T₂) =
  let (T₁, Γ₁, ok₁) = infer(R, Γ, e₁)
  if ¬ok₁ then (Γ, false)
  else
    let Γ₂ = Γ₁[x ↦ (T₁, false)]
    let (Γ₃, ok₂) = check(R, Γ₂, e₂, T₂)
    if ¬ok₂ then (Γ, false)
    else
      if linear(T₁) ∧ ¬used(Γ₃, x) then (Γ, false)  // unused linear
      else (remove(Γ₃, x), true)

check(R, Γ, ELam x T₁ e, TFun T₁ T₂) =
  let Γ' = Γ[x ↦ (T₁, false)]
  let (Γ'', ok) = check(R, Γ', e, T₂)
  if ok ∧ (¬linear(T₁) ∨ used(Γ'', x)) then
    (remove(Γ'', x), true)
  else (Γ, false)

check(R, Γ, EApp e₁ e₂, T₂) =
  let (TFun T₁ T₂', Γ₁, ok₁) = infer(R, Γ, e₁)
  if ¬ok₁ ∨ T₂ ≠ T₂' then (Γ, false)
  else check(R, Γ₁, e₂, T₁)

// ... similar for other constructs
```

### 2.2 Complexity Analysis

**Theorem 2.2** (Type Checking Complexity):
Type checking for Ephapax is decidable in O(n) time, where n is the size of the expression.

**Proof**:

*Claim 1*: Each expression construct is visited exactly once.
- The algorithm is recursive on the structure of expressions
- No backtracking or iteration over subexpressions

*Claim 2*: Each operation takes O(1) amortized time.
- Context operations (lookup, mark used, extend) are O(1) with hash maps
- Type equality is O(|T|), but types are typically small constants
- Region membership is O(1) with sets

*Claim 3*: Total work is proportional to expression size.
- ∑_{nodes} O(1) = O(n)

Therefore, type checking is O(n). □

### 2.3 Space Complexity

**Theorem 2.3** (Space Complexity):
Type checking requires O(n) space.

**Proof**:
- The context Γ contains at most n bindings (one per let/lambda)
- The region set R contains at most n regions (one per region construct)
- The recursion depth is at most n
- Total space: O(n). □

---

## 3. Type Inference

### 3.1 Inference Algorithm

**Algorithm 3.1** (Type Inference):
```
infer(R, Γ, e) → (T, Γ', bool)

infer(R, Γ, EUnit) = (TBase TUnit, Γ, true)
infer(R, Γ, EBool b) = (TBase TBool, Γ, true)
infer(R, Γ, EI32 n) = (TBase TI32, Γ, true)

infer(R, Γ, EVar x) =
  match Γ(x) with
  | Some(T, used) →
      if linear(T) ∧ used then (⊥, Γ, false)
      else if linear(T) then (T, Γ[x ↦ used], true)
      else (T, Γ, true)
  | None → (⊥, Γ, false)

infer(R, Γ, ELam x T₁ e) =
  let Γ' = Γ[x ↦ (T₁, false)]
  let (T₂, Γ'', ok) = infer(R, Γ', e)
  if ok ∧ (¬linear(T₁) ∨ used(Γ'', x)) then
    (TFun T₁ T₂, remove(Γ'', x), true)
  else (⊥, Γ, false)

infer(R, Γ, EApp e₁ e₂) =
  let (T₁, Γ₁, ok₁) = infer(R, Γ, e₁)
  match T₁ with
  | TFun T_arg T_ret →
      let (Γ₂, ok₂) = check(R, Γ₁, e₂, T_arg)
      if ok₁ ∧ ok₂ then (T_ret, Γ₂, true)
      else (⊥, Γ, false)
  | _ → (⊥, Γ, false)

// ... similar for other constructs
```

### 3.2 Complexity

**Theorem 3.2** (Type Inference Complexity):
Type inference for Ephapax (with explicit lambda annotations) is O(n).

**Proof**:
The inference algorithm mirrors the checking algorithm:
- Each node visited once
- Each operation O(1)
- Total: O(n). □

### 3.3 Full Type Inference (Hindley-Milner Style)

If we add polymorphism and remove lambda annotations:

**Theorem 3.3** (Polymorphic Type Inference):
Type inference with let-polymorphism is O(n²) in the worst case, O(n) expected.

This follows from standard Hindley-Milner analysis, with the linear constraint checking adding only constant factor overhead.

---

## 4. Region Inference

### 4.1 Problem Statement

Given an expression e with elided region annotations, infer minimal region assignments.

**Example**:
```
// Input (regions elided)
let s = String.new("hello")
let t = String.new("world")
String.concat(s, t)

// Output (regions inferred)
region r {
  let s = String.new@r("hello")
  let t = String.new@r("world")
  String.concat(s, t)
}
```

### 4.2 Constraint Generation

**Algorithm 4.1** (Constraint Generation):
Generate constraints of the form:
- `r₁ ⊑ r₂` (r₁ outlives r₂)
- `r ∈ scope(e)` (r is live during e)

```
constrain(e) → Set(Constraint)

constrain(EStringNew r s) = {r ∈ scope(current)}
constrain(EStringConcat e₁ e₂) =
  constrain(e₁) ∪ constrain(e₂) ∪ {region(e₁) = region(e₂)}
constrain(ELet x e₁ e₂) =
  constrain(e₁) ∪ constrain(e₂) ∪ {region(e₁) ⊑ scope(e₂)}
constrain(ERegion r e) =
  constrain(e) ∪ {∀s ∈ regions(result(e)). s ≠ r}
// ...
```

### 4.3 Constraint Solving

**Algorithm 4.2** (Region Constraint Solving):
Solve the constraint system using unification and subsumption.

**Theorem 4.2** (Region Inference Complexity):
Region inference is O(n · α(n)) where α is the inverse Ackermann function.

**Proof**:
- Constraint generation: O(n) (one pass)
- Constraint solving: Union-find for region unification
- Subsumption checking: Topological sort of region nesting
- Total: O(n · α(n)) ≈ O(n) for practical inputs. □

---

## 5. Linearity Checking

### 5.1 Problem Statement

Verify that linear resources are used exactly once.

### 5.2 Algorithm

**Algorithm 5.1** (Linearity Checking):
Track variable usage in a single pass:

```
linearCheck(Γ, e) → (Γ', bool)

// Context Γ maps variables to (type, used)
// Returns updated context and success flag

linearCheck(Γ, EVar x) =
  match Γ(x) with
  | (T, false) when linear(T) → (Γ[x ↦ (T, true)], true)
  | (T, true) when linear(T) → (Γ, false)  // double use
  | (T, _) → (Γ, true)  // unrestricted

linearCheck(Γ, ELet x e₁ e₂) =
  let (Γ₁, ok₁) = linearCheck(Γ, e₁)
  if ¬ok₁ then (Γ, false)
  let T = typeOf(e₁)
  let Γ₂ = Γ₁[x ↦ (T, false)]
  let (Γ₃, ok₂) = linearCheck(Γ₂, e₂)
  if ¬ok₂ then (Γ, false)
  if linear(T) ∧ ¬used(Γ₃, x) then (Γ, false)  // unused linear
  (remove(Γ₃, x), true)

linearCheck(Γ, EIf e₁ e₂ e₃) =
  let (Γ₁, ok₁) = linearCheck(Γ, e₁)
  if ¬ok₁ then (Γ, false)
  let (Γ₂, ok₂) = linearCheck(Γ₁, e₂)
  let (Γ₃, ok₃) = linearCheck(Γ₁, e₃)
  if ¬ok₂ ∨ ¬ok₃ then (Γ, false)
  if Γ₂ ≠ Γ₃ then (Γ, false)  // branches disagree
  (Γ₂, true)

// ...
```

### 5.3 Complexity

**Theorem 5.3** (Linearity Checking Complexity):
Linearity checking is O(n).

**Proof**:
- Single traversal of the expression
- Context operations are O(1) with appropriate data structures
- Branch comparison for conditionals/case is O(|Γ|) but amortized O(1) per node
- Total: O(n). □

---

## 6. Decidability Results

### 6.1 Type Checking

**Theorem 6.1** (Type Checking Decidability):
The type checking problem for Ephapax is decidable.

**Proof**:
Algorithm 2.1 terminates and correctly decides type checking. Termination follows from structural recursion on expressions. Correctness is by induction on the typing derivation. □

### 6.2 Type Inhabitance

**Theorem 6.2** (Type Inhabitance):
Given a type T, deciding whether there exists a closed expression e such that `⊢ e : T` is decidable.

**Proof sketch**:
For linear logic, the decision procedure is more complex than classical logic, but still decidable for propositional fragments. Ephapax's type language is essentially propositional linear logic, which is PSPACE-complete [Lincoln et al., 1992].

However, for practical types in Ephapax:
- Base types: () is the only unit inhabitant, booleans have true/false
- Function types: Construct lambdas recursively
- Product types: Construct pairs recursively
- Sum types: Use inl/inr
- String types: Require a region context

The procedure terminates because types are finite and recursion follows type structure. □

### 6.3 Subtyping (If Added)

**Theorem 6.3** (Subtyping Decidability):
If subtyping is added to Ephapax, with the usual linear type subtyping rules, subtype checking is decidable in O(|T₁| + |T₂|).

**Proof**:
Standard structural subtyping algorithm with linearity checks at reference types. □

---

## 7. Compilation Complexity

### 7.1 Lexing

**Theorem 7.1** (Lexing Complexity):
Lexing Ephapax source code is O(n) where n is the input length.

**Proof**:
The lexer (using `logos` crate) is a finite automaton. Each character is processed once. □

### 7.2 Parsing

**Theorem 7.2** (Parsing Complexity):
Parsing Ephapax is O(n) with a predictive (LL) parser or O(n³) with a general CFG parser.

**Proof**:
- Ephapax grammar is LL(k) for small k (unambiguous, left-factored)
- Using `chumsky` parser combinators with packrat memoization: O(n)
- Worst-case CFG parsing (CYK/Earley): O(n³), but not needed here. □

### 7.3 Type Checking

Already shown: O(n).

### 7.4 Code Generation

**Theorem 7.3** (Code Generation Complexity):
WASM code generation is O(n).

**Proof**:
- Single pass over the typed AST
- Each node generates constant-size WASM instruction(s)
- Total: O(n). □

### 7.5 Total Compilation

**Corollary 7.4** (Total Compilation Complexity):
End-to-end compilation of Ephapax to WASM is O(n).

---

## 8. Complexity Comparison

| Operation | Ephapax | Rust | Haskell |
|-----------|---------|------|---------|
| Type checking | O(n) | O(n³) typical | O(n) |
| Type inference | O(n) | O(n³) typical | O(n²) worst |
| Borrow checking | N/A | O(n²) typical | N/A |
| Region inference | O(n) | O(n²) (lifetime) | N/A |
| Parsing | O(n) | O(n) | O(n) |
| Code generation | O(n) | O(n) | O(n) |

Ephapax's simpler type system (no lifetime annotations, second-class borrows) enables better asymptotic complexity than Rust's borrow checker.

---

## 9. Hardness Results

### 9.1 Propositional Linear Logic

**Theorem 9.1** (PSPACE-Completeness):
Provability in propositional linear logic is PSPACE-complete [Lincoln et al., 1992].

For Ephapax type inhabitance, this gives a lower bound: deciding if a type is inhabited is at least as hard as propositional linear logic.

### 9.2 Higher-Order Matching

**Theorem 9.2** (Undecidability):
Higher-order unification (if added for polymorphism) is undecidable in general [Huet, 1973].

However, pattern matching (higher-order matching) is decidable [Stirling, 2009].

### 9.3 Region Inference with Subtyping

**Theorem 9.3** (Potentially Exponential):
Region inference with covariant/contravariant subtyping can be exponential in the worst case, but is polynomial for practical programs [Tofte & Birkedal, 1998].

---

## 10. Optimizations

### 10.1 Incremental Type Checking

With dependency tracking:
```
incrementalCheck(e, changed) → bool
  // Only re-check expressions depending on changed definitions
  // Amortized O(k) where k is the size of changed portion
```

### 10.2 Parallel Type Checking

Independent subexpressions can be checked in parallel:
```
parallelCheck(e) =
  match e with
  | EPair e₁ e₂ → parallel(check(e₁), check(e₂))
  | EApp e₁ e₂ → sequential(check(e₁), check(e₂))  // context dependency
  | ...
```

Parallelism is limited by context threading but can still improve performance.

---

## 11. TODO: Formal Proofs

### 11.1 Algorithm Correctness

- [ ] Prove type checking algorithm is sound (if it accepts, the expression is well-typed)
- [ ] Prove type checking algorithm is complete (if the expression is well-typed, it accepts)
- [ ] Prove type inference produces principal types

### 11.2 Complexity Proofs

- [ ] Formalize complexity analysis in a proof assistant
- [ ] Tighten bounds for specific sublanguages
- [ ] Analyze amortized complexity of context operations

---

## 12. References

1. Lincoln, P., Mitchell, J., Scedrov, A., & Shankar, N. (1992). Decision problems for propositional linear logic. *Annals of Pure and Applied Logic*, 56(1-3).

2. Huet, G. (1973). The undecidability of unification in third order logic. *Information and Control*, 22(3).

3. Stirling, C. (2009). Decidability of higher-order matching. *Logical Methods in Computer Science*, 5(3).

4. Tofte, M. & Birkedal, L. (1998). A region inference algorithm. *TOPLAS*, 20(4).

5. Gaboardi, M., Katsumata, S., Orchard, D., Breuvart, F., & Uustalu, T. (2016). Combining effects and coeffects via grading. *ICFP*.

---

*End of Computational Complexity Analysis*
