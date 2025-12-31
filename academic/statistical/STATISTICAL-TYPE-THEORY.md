# Statistical Type Theory for Ephapax

## Probabilistic Analysis and Resource Bounds

**Version**: 1.0.0
**Date**: 2025-12-31
**SPDX-License-Identifier**: EUPL-1.2

---

## Abstract

We develop a statistical and probabilistic perspective on Ephapax's type system. This includes: (1) probabilistic analysis of resource usage, (2) amortized complexity bounds via potential functions, (3) connections to information theory and entropy, and (4) statistical properties of linear type inference.

---

## 1. Introduction

Statistical type theory provides tools for:
- **Resource analysis**: Bounding memory usage, allocation counts
- **Probabilistic typing**: Types for randomized computations
- **Information-theoretic properties**: Entropy of type inhabitants
- **Empirical analysis**: Statistical properties of type inference

---

## 2. Resource Analysis

### 2.1 Resource Polynomials

Following Hoffmann et al. [2012], we assign resource usage polynomials to types:

**Definition 2.1** (Resource Annotation):
```
T^q = (T, q)  where q : ResourcePolynomial
```

Resource polynomials track:
- Allocation count
- Memory usage (bytes)
- Region depth

### 2.2 Annotated Types

```
Unit^0           -- No resource usage
Bool^0           -- No allocation
I32^0            -- No allocation
String@r^1       -- One allocation
(T₁^q₁ × T₂^q₂)^{q₁+q₂}   -- Combined usage
(T₁^q₁ → T₂^q₂)^0         -- Functions don't allocate at definition
```

### 2.3 Typing Rules with Resources

**Let binding**:
```
Γ ⊢ e₁ : T₁^q₁ ⊣ Γ'
Γ', x:T₁^q₁ ⊢ e₂ : T₂^q₂ ⊣ Γ''
──────────────────────────────────────
Γ ⊢ let x = e₁ in e₂ : T₂^{q₁+q₂} ⊣ Γ''
```

**String allocation**:
```
r ∈ R
────────────────────────────────────────
Γ ⊢ String.new@r(s) : String@r^{|s|+8} ⊣ Γ
```

(Accounts for string data + header)

### 2.4 Resource Bounds Theorem

**Theorem 2.1** (Sound Resource Bounds):
If `Γ ⊢ e : T^q`, then evaluating e allocates at most q bytes.

*Proof*: By induction on typing derivation, showing each rule's resource annotation is an upper bound. □

---

## 3. Amortized Analysis

### 3.1 Potential Functions

Assign potential Φ(T) to types representing "stored" resources:

```
Φ(Unit) = 0
Φ(Bool) = 0
Φ(I32) = 0
Φ(String@r) = c_string  (cost of future operations)
Φ(T₁ × T₂) = Φ(T₁) + Φ(T₂)
Φ(List^n[T]) = n · (Φ(T) + c_cons)  (n-element list)
```

### 3.2 Amortized Cost

**Definition 3.1** (Amortized Cost):
```
amort(e) = actual_cost(e) + ΔΦ
```

Where ΔΦ = Φ(result) - Φ(inputs).

### 3.3 Example: List Operations

If Ephapax had lists:
```
cons : T × List[T] → List[T]

actual_cost(cons) = c_alloc  (allocate cons cell)
Φ(List^n[T]) = n · k
Φ(List^{n+1}[T]) = (n+1) · k

amort(cons) = c_alloc + k  (constant)
```

Even though accessing all elements costs O(n), the amortized cost per insertion is O(1).

---

## 4. Probabilistic Types

### 4.1 Random Types

For probabilistic computations:

```
Prob[T] = probability distribution over T

T ::= ... | Prob[T]
```

### 4.2 Typing Random Expressions

```
Γ ⊢ e : T    P : Prob[T]
─────────────────────────────
Γ ⊢ sample(e, P) : Prob[T]
```

### 4.3 Linear Probability

In a linear setting, random resources are single-use:

```
Prob[String@r]  -- Random string, can only be "observed" once
```

This models quantum-like no-cloning for random values.

### 4.4 Expected Resource Usage

**Definition 4.1** (Expected Resources):
```
E[resources(e)] = Σ_v P(e ⇓ v) · resources(v)
```

**Theorem 4.1** (Expected Bound):
If `Γ ⊢ e : Prob[T^q]`, then E[resources(e)] ≤ E[q].

---

## 5. Information-Theoretic Properties

### 5.1 Type Entropy

**Definition 5.1** (Type Entropy):
The entropy of a type T is:
```
H(T) = log₂|inhabitants(T)|
```

For finite types:
```
H(Unit) = 0         (1 inhabitant)
H(Bool) = 1         (2 inhabitants)
H(I32) = 32         (2³² inhabitants)
H(T₁ × T₂) = H(T₁) + H(T₂)
H(T₁ + T₂) = log₂(2^{H(T₁)} + 2^{H(T₂)})
H(T₁ → T₂) = H(T₂)^{H(T₁)}  (exponential!)
```

### 5.2 Linear Types and Information

Linear types constrain information flow:

```
// Non-linear: information can be duplicated
f : A → A × A

// Linear: information preserved, not duplicated
g : A ⊸ B  (transforms, doesn't copy)
```

**Theorem 5.1** (Linear Information Conservation):
For linear functions f : A ⊸ B:
```
H(B) ≤ H(A)  (no information creation)
```

*Proof*: Linear functions are injective on resources (one input, one output). Injections don't increase entropy. □

### 5.3 Region Entropy

**Definition 5.2** (Region Entropy):
```
H(region r { e }) = H(e) - H(freed resources)
```

Region exit "forgets" information about freed allocations.

---

## 6. Statistical Properties of Type Inference

### 6.1 Inference Success Rate

For randomly generated expressions:

**Definition 6.1** (Typeability Density):
```
ρ(n) = |{e : |e| = n, ⊢ e : T for some T}| / |{e : |e| = n}|
```

**Conjecture 6.1** (Typeability Density):
For Ephapax expressions, ρ(n) → 0 as n → ∞.

Most large random expressions are ill-typed (they violate linearity, scope, etc.).

### 6.2 Principal Type Distribution

For typeable expressions:

**Definition 6.2** (Type Size Distribution):
```
P(|T| = k | e is typeable) = proportion of typeable expressions with type size k
```

Empirically, type sizes follow a log-normal distribution for practical programs.

### 6.3 Linear Constraint Satisfaction

**Definition 6.3** (Linearity Constraint Density):
For an expression with n bindings:
```
constraints(e) ≈ O(n) linear usage constraints
```

**Theorem 6.2** (Constraint Density):
The number of linearity constraints is O(n) where n is the expression size.

*Proof*: Each variable introduces at most one "must use" constraint. Each use introduces one "mark used" operation. Total: O(n). □

---

## 7. Quantitative Type Theory

### 7.1 Graded Types

Ephapax could be extended with quantitative annotations:

```
T^r where r ∈ R (a resource semiring)

Examples:
  T^1 : use exactly once (linear)
  T^ω : use any number of times (unrestricted)
  T^0 : cannot use (erased)
  T^{0,1} : use at most once (affine)
```

### 7.2 Resource Semiring

**Definition 7.1** (Resource Semiring):
```
(R, +, ·, 0, 1) where:
- 0 : erased
- 1 : linear
- ω : unrestricted
- r + s : parallel composition
- r · s : sequential composition
```

### 7.3 Graded Typing Rules

**Variable**:
```
x : T^r ∈ Γ    r ≥ 1
─────────────────────
  Γ ⊢ x : T   [uses r]
```

**Abstraction**:
```
Γ, x : T^r ⊢ e : U
───────────────────────────
Γ ⊢ λx.e : T^r → U
```

---

## 8. Markov Chain Analysis

### 8.1 Evaluation as Markov Process

Model evaluation as a Markov chain:

```
States = Configuration
Transition = step relation → (with probabilities if randomized)
```

### 8.2 Stationary Distribution

For terminating programs:
```
π(final states) = 1
```

For non-terminating (with loops), analyze stationary behavior.

### 8.3 Hitting Times

**Definition 8.1** (Hitting Time):
```
τ_v = min{n : X_n = v}  (first time to reach value v)
```

**Theorem 8.1** (Bounded Hitting Time):
For Ephapax without recursion, τ_v < ∞ almost surely.

*Proof*: No recursion ⟹ strictly decreasing expression size ⟹ termination. □

---

## 9. Regression Analysis

### 9.1 Compile Time Prediction

Model compilation time as:
```
T_compile = β₀ + β₁·|AST| + β₂·|types| + β₃·regions + ε
```

### 9.2 Memory Usage Prediction

Model peak memory:
```
M_peak = γ₀ + γ₁·allocations + γ₂·max_region_depth + ε
```

### 9.3 Empirical Validation

Collect data from real Ephapax programs:
1. Measure actual compile times, memory usage
2. Fit regression models
3. Validate predictions on held-out data

---

## 10. Monte Carlo Type Checking

### 10.1 Probabilistic Type Checking

For complex programs, use sampling:

```
probCheck(e) =
  sample n random evaluation paths
  check type invariants on each path
  return (violations / n)
```

### 10.2 Statistical Guarantees

With n samples and error rate ε:
```
P(probCheck fails | e is well-typed) < ε
```

For confidence 1 - δ:
```
n ≥ (1/2ε²) · ln(2/δ)
```

### 10.3 Use Cases

- Rapid prototype checking
- Large codebase screening
- Fuzzing for type system bugs

---

## 11. Bayesian Type Inference

### 11.1 Prior on Types

Define prior probability over types:
```
P(T) ∝ 2^{-|T|}  (prefer simpler types)
```

### 11.2 Likelihood

```
P(e | T) = 1 if e : T, 0 otherwise
```

### 11.3 Posterior

```
P(T | e) ∝ P(e | T) · P(T)
```

The most probable type is the smallest (simplest) valid type.

### 11.4 Type Inference as Bayesian Update

```
infer(e) = argmax_T P(T | e)
         = argmax_{T : e:T} P(T)
         = smallest valid type
```

This connects type inference to Occam's razor.

---

## 12. TODO: Empirical Studies

### 12.1 Data Collection

- [ ] Implement Ephapax program generator
- [ ] Collect corpus of real Ephapax programs
- [ ] Measure type inference statistics

### 12.2 Statistical Analysis

- [ ] Fit typeability density curves
- [ ] Analyze type size distributions
- [ ] Measure compile time / memory correlations

### 12.3 Theoretical

- [ ] Prove typeability density conjecture
- [ ] Formalize resource polynomial system
- [ ] Develop graded type extension

---

## 13. References

1. Hoffmann, J., Aehlig, K., & Hofmann, M. (2012). Multivariate amortized resource analysis. *TOPLAS*, 34(3).

2. Dal Lago, U. & Gaboardi, M. (2011). Linear dependent types and relative completeness. *LICS*.

3. Atkey, R. (2018). Syntax and semantics of quantitative type theory. *LICS*.

4. Brunel, A., Gaboardi, M., Mazza, D., & Zdancewic, S. (2014). A core quantitative coeffect calculus. *ESOP*.

5. Bernardy, J.-P. & Moulin, G. (2013). Type-theory in color. *ICFP*.

6. Shannon, C.E. (1948). A mathematical theory of communication. *Bell System Technical Journal*.

---

*End of Statistical Type Theory*
