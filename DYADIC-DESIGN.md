# The Dyadic Design: A Paradigm Breakthrough

## Executive Summary

Ephapax introduces **dyadic design** — the first programming language to treat affine and linear type systems as **co-equal, first-class modes** rather than competing alternatives. This breakthrough enables developers to prototype rapidly in permissive affine mode, then switch to strict linear mode for production deployment, achieving both **developer productivity** and **guaranteed safety** without compromise.

## The Problem: The Strictness Dilemma

Linear type systems face a fundamental tension:

### Traditional Approach: Choose One

```
┌─────────────────────────────────────┐
│  Linear Types (Strict)              │
│  ✓ Perfect safety                   │
│  ✗ Slow prototyping                 │
│  ✗ High learning curve              │
└─────────────────────────────────────┘
                  OR
┌─────────────────────────────────────┐
│  Affine Types (Permissive)          │
│  ✓ Easy development                 │
│  ✗ Potential resource leaks         │
│  ✗ Weaker guarantees                │
└─────────────────────────────────────┘
```

**Result:** Developers either:
- Abandon linear types for productivity (losing safety)
- Struggle with strict enforcement (losing velocity)
- Use "unsafe escape hatches" (defeating the purpose)

### Why This Matters

Real-world development requires **both**:

| Phase | Need | Traditional Solution | Problem |
|-------|------|---------------------|---------|
| **Prototyping** | Speed, flexibility | Use GC/reference counting | Lose linear guarantees |
| **Production** | Safety, no leaks | Add manual checks | Brittle, error-prone |
| **Exploration** | Try ideas fast | Disable strict checking | Safety bugs in prototypes |
| **Deployment** | Zero defects | Rewrite in strict mode | Duplicate effort |

**The industry consensus:** "You can't have both."

## The Solution: Dyadic Design

Ephapax rejects this false dichotomy with **mode duality**.

### Core Insight

Affine and linear types are **not competing systems** — they're **different views of the same resource semantics**:

- **Affine (≤1):** "Use at most once" — permissive lower bound
- **Linear (=1):** "Use exactly once" — strict upper bound

**Dyadic design:** Implement **both** as switchable modes over the **same AST**.

### How It Works

```ephapax
// Write your code once
fn process(_unit: ()): I32 =
    region r {
        let s = String.new@r("data") in
        compute(&s)
        // No explicit drop here
    }
```

**Check in affine mode (prototyping):**
```bash
$ ephapax check --mode affine process.eph
✓ Type checks passed
```
The unused `s` is **implicitly dropped** — affine mode allows this.

**Check in linear mode (production):**
```bash
$ ephapax check --mode linear process.eph
✗ Type error: unused linear value 's' at line 4
```
Linear mode **demands explicit consumption**.

**Fix for production:**
```ephapax
fn process(_unit: ()): I32 =
    region r {
        let s = String.new@r("data") in
        let result = compute(&s) in
        let _ = drop(s) in  // Explicit drop
        result
    }
```

**Both modes now pass:**
```bash
$ ephapax check --mode affine process.eph   ✓
$ ephapax check --mode linear process.eph  ✓
```

## The Breakthrough: Co-Equal Modes

### What Makes This Different

**Traditional languages:**
```
Strict Mode (default) + Escape Hatches (workarounds)
```
Examples:
- Rust: `unsafe` blocks to bypass borrow checker
- Linear Haskell: Multiplicity polymorphism with `%1` annotations
- ATS: `praxi` for proof circumvention

**Problem:** Escape hatches are **admissions of defeat** — they say "the type system failed, so we opt out."

**Ephapax's approach:**
```
Affine Mode (exploration) ⇄ Linear Mode (production)
```
**No escape hatches.** Both modes are **fully type-safe** — they just enforce different guarantees.

### Key Difference

| Aspect | Traditional | Ephapax Dyadic |
|--------|-------------|----------------|
| **Philosophy** | One "right" mode + compromises | Two valid modes for different contexts |
| **Safety** | Escape hatches break guarantees | Both modes type-safe, no unsafe |
| **Workflow** | Choose strictness upfront | Adapt strictness to lifecycle |
| **Migration** | Rewrite or insert pragmas | Add explicit drops, that's it |
| **Semantics** | Loose XOR Strict | Loose AND Strict (switchable) |

## Formal Foundations

The dyadic design is **formally verified** in Coq.

### Type System Rules (Simplified)

**Affine mode** typing judgment:
```
Γ ⊢ₐ e : τ
```
Rules allow **weakening** (unused variables discarded).

**Linear mode** typing judgment:
```
Γ ⊢ₗ e : τ
```
Rules **prohibit weakening** (all variables must be used).

### Key Theorems (Proven)

**Theorem 1 (Soundness):** Both modes are sound
```coq
Theorem affine_soundness :
  ∀ e τ, ⊢ₐ e : τ → (e ⇓ v ∨ e diverges).

Theorem linear_soundness :
  ∀ e τ, ⊢ₗ e : τ → (e ⇓ v ∨ e diverges).
```

**Theorem 2 (Linear subsumes Affine):** Linear mode is strictly stronger
```coq
Theorem linear_implies_affine :
  ∀ Γ e τ, Γ ⊢ₗ e : τ → Γ ⊢ₐ e : τ.
```

**Corollary:** Code that type-checks in linear mode **always** type-checks in affine mode.

**Theorem 3 (Resource Safety):** Linear mode prevents leaks
```coq
Theorem linear_no_leaks :
  ∀ e, (⊢ₗ e : τ) → (∀ r ∈ regions(e), used(r) = allocated(r)).
```

### Dyadic Semantics

The operational semantics is **mode-independent**:
```
e ⇓ v  (same reduction rules for both modes)
```

**The modes differ only in static checking**, not runtime behavior. This means:
- No runtime overhead for mode switching
- WASM output identical regardless of mode
- Migration is purely compile-time transformation

## Real-World Workflow

### Development Lifecycle

```
┌─────────────────────────────────────────────────────────┐
│ Phase 1: EXPLORATION (Affine Mode)                      │
├─────────────────────────────────────────────────────────┤
│ • Prototype features rapidly                            │
│ • Implicit drops = fewer errors                         │
│ • Focus on logic, not resource management               │
│ • iterate fast on APIs                                  │
│                                                         │
│ $ ephapax check --mode affine prototype.eph            │
│ ✓ Type checks passed (warnings about unused resources) │
└─────────────────────────────────────────────────────────┘
                         ↓
┌─────────────────────────────────────────────────────────┐
│ Phase 2: HARDENING (Linear Mode)                        │
├─────────────────────────────────────────────────────────┤
│ • Switch to linear mode                                 │
│ • Fix diagnostics (add explicit drops)                  │
│ • Verify resource cleanup                               │
│ • Guarantee zero leaks                                  │
│                                                         │
│ $ ephapax check --mode linear prototype.eph            │
│ ✗ 5 errors: unused linear values                       │
│ → Add 5 explicit drops                                  │
│ ✓ All checks passed                                     │
└─────────────────────────────────────────────────────────┘
                         ↓
┌─────────────────────────────────────────────────────────┐
│ Phase 3: PRODUCTION (Linear Mode)                       │
├─────────────────────────────────────────────────────────┤
│ • Deploy with linear mode guarantees                    │
│ • Zero resource leaks                                   │
│ • No use-after-free                                     │
│ • Verified safety                                       │
│                                                         │
│ $ ephapax compile --mode linear production.eph         │
│ ✓ Compiled to production.wasm (547 bytes)              │
└─────────────────────────────────────────────────────────┘
```

### Example: API Exploration to Production

**Phase 1: Exploring a new API (affine mode)**
```ephapax
fn experiment(_unit: ()): I32 =
    region r {
        let s1 = String.new@r("test") in
        let s2 = String.new@r("data") in
        let s3 = String.new@r("example") in

        // Just trying things out
        let len1 = String.len(&s1) in
        let len2 = String.len(&s2) in

        // Oops, forgot s3, but affine mode allows this
        len1 + len2
    }
```

**Affine mode:** ✓ Passes (s3 implicitly dropped, warning issued)

**Phase 2: Production hardening (linear mode)**
```bash
$ ephapax check --mode linear experiment.eph
✗ Error: unused linear value 's3' at line 6
```

**Fix:**
```ephapax
fn experiment(_unit: ()): I32 =
    region r {
        let s1 = String.new@r("test") in
        let s2 = String.new@r("data") in
        let s3 = String.new@r("example") in

        let len1 = String.len(&s1) in
        let len2 = String.len(&s2) in

        // Explicitly handle all resources
        let _ = drop(s1) in
        let _ = drop(s2) in
        let _ = drop(s3) in

        len1 + len2
    }
```

**Linear mode:** ✓ Passes (production-ready)

## Comparison with Other Approaches

### Rust

**Approach:** Strict ownership + `unsafe` escape hatches

```rust
fn process(data: String) -> usize {
    let len = data.len();
    // Rust automatically drops 'data' here
    len
}

// Escape hatch when strictness blocks you
fn manual_memory() {
    unsafe {
        // Bypass borrow checker
        let ptr = std::alloc::alloc(layout);
        // Manual memory management
    }
}
```

**Pros:**
- Strong safety guarantees (when not using `unsafe`)
- Automatic cleanup

**Cons:**
- No "exploration mode"
- `unsafe` blocks break guarantees
- Fighting the borrow checker during prototyping

**Ephapax difference:** No `unsafe` needed — use affine mode instead.

### Linear Haskell

**Approach:** Multiplicity polymorphism

```haskell
f :: a %1 -> b    -- Linear: use 'a' exactly once
g :: a %Many -> b -- Unrestricted: use 'a' many times
```

**Pros:**
- Fine-grained control
- Polymorphic over linearity

**Cons:**
- Complex type signatures
- Linearity permeates the type system
- No simple "mode switch" for whole programs

**Ephapax difference:** Mode is a compile flag, not a type-level concern.

### ATS (Applied Type System)

**Approach:** Dependent types with proof terms

```ats
fun process {l:addr} (pf: !mytype @ l | ptr: ptr l): void
```

**Pros:**
- Extremely powerful verification
- Proof-carrying code

**Cons:**
- Very steep learning curve
- Proof obligations everywhere
- `praxi` (proof axioms) as escape hatch

**Ephapax difference:** Simpler — just switch modes, no proofs needed.

## Why Dyadic Design Is a Breakthrough

### 1. **Philosophical Shift**

**Old thinking:** "Linear types are too strict for real development, so we add escape hatches."

**Dyadic thinking:** "Affine and linear are both valid — use each where appropriate."

This reframes the entire debate:
- Not "strict vs. permissive"
- But "exploration vs. production"

### 2. **Eliminates Escape Hatches**

Every "escape hatch" is an **admission that the type system failed**. Dyadic design says: "We don't need escape hatches — we have two **valid** modes."

Compare:
```rust
// Rust: escape hatch breaks guarantees
unsafe { /* do unsafe thing */ }

// Ephapax: switch modes, both type-safe
--mode affine  // Exploration
--mode linear  // Production
```

### 3. **Migration Path**

Most languages force an upfront choice:
- Start strict → slow prototyping
- Start loose → hard to add guarantees later

Ephapax provides a **smooth gradient**:
```
Affine (fast) → Add drops → Linear (safe)
```

Same code structure. Incremental hardening.

### 4. **Compositional**

You can mix modes in a codebase:
```bash
# Test suite in affine mode (fast iteration)
ephapax test --mode affine tests/

# Production code in linear mode (zero leaks)
ephapax build --mode linear src/
```

## The Name: "Dyadic"

**Dyadic** (from Greek δυάς "pair, duality") emphasizes that:

1. **Two modes, not one primary + fallback**
2. **Co-equal status** (neither is a "compromise")
3. **Duality** (mathematical relationship: linear ⊆ affine)
4. **Mode switching** (binary choice, not a spectrum)

This is **not**:
- Gradual typing (unsound mixing of typed/untyped)
- Multiplicity polymorphism (per-binding annotations)
- Escape hatches (unsafe workarounds)

This **is**:
- Two sound type systems
- Global mode selection
- Migration workflow built-in

## Future Research Directions

The dyadic design opens new questions:

1. **Automatic mode inference:** Can we infer the minimal mode needed?
2. **Mixed-mode compilation:** Can functions have different modes in the same program?
3. **Mode polymorphism:** Can a function be polymorphic over mode?
4. **Gradual strengthening:** Can we interpolate between affine and linear?

These are open research problems enabled by dyadic design.

## Conclusion

Ephapax's dyadic design is a **paradigm breakthrough** because it:

✅ **Rejects false dichotomies** (strict XOR permissive)
✅ **Provides both modes as first-class** (not primary + escape hatch)
✅ **Enables smooth migration** (prototype → production)
✅ **Maintains full type safety** (no `unsafe`, no `praxi`)
✅ **Grounds in formal semantics** (Coq-verified soundness)

**The result:** Developers can finally have their cake and eat it too — **rapid prototyping** in affine mode, **guaranteed safety** in linear mode, all in the **same language** with the **same code structure**.

This is what the next generation of type systems looks like.

---

## Further Reading

- **Formal Semantics:** [formal/](formal/) — Coq proofs of soundness
- **Implementation:** [src/ephapax-typing/](src/ephapax-typing/) — Dyadic type checker
- **Language Guide:** [LANGUAGE-GUIDE.md](LANGUAGE-GUIDE.md) — Using both modes
- **Examples:** [examples/](examples/) — Affine and linear code

## Citation

If you use Ephapax's dyadic design in research or production, please cite:

```bibtex
@software{ephapax2026,
  title = {Ephapax: A Dyadic Affine/Linear Type System for WebAssembly},
  author = {Jewell, Jonathan D.A.},
  year = {2026},
  url = {https://github.com/hyperpolymath/ephapax},
  note = {First language with co-equal affine and linear modes}
}
```

---

**Ephapax: Dyadic by design. Safe by proof. Practical by choice.** 🎭✨
