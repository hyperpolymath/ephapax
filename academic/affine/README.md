# Affine Ephapax

## Complete Academic Documentation

**Discipline**: Affine (use at most once)

---

## Overview

Affine Ephapax enforces that every resource may be used **at most once**. This is more permissive than linear:

| Property | Guarantee |
|----------|-----------|
| No use-after-free | ✓ |
| No double-free | ✓ |
| No memory leaks | ✗ (implicit drop) |
| No dangling pointers | ✓ |

---

## Documents

| File | Description |
|------|-------------|
| `AFFINE-EPHAPAX-SPECIFICATION.md` | Complete formal specification |
| `proofs/AffineEphapax.v` | Coq mechanization |

---

## Key Typing Rules

### Variable Access (Affine)
```
lookup(Γ, x) = (T, false)    affine(T) = true
─────────────────────────────────────────────
R; Γ ⊢ x : T ⊣ mark(Γ, x)
```
(Same as linear - prevents double use)

### Let Binding (May Be Unused)
```
R; Γ ⊢ e₁ : T₁ ⊣ Γ'
R; Γ', x:T₁ ⊢ e₂ : T₂ ⊣ Γ'', (x:T₁, _)
                              ↑ NO REQUIREMENT
───────────────────────────────────────────────
R; Γ ⊢ let x = e₁ in e₂ : T₂ ⊣ Γ''
```

### Conditionals (May Differ)
```
R; Γ' ⊢ e₂ : T ⊣ Γ₁
R; Γ' ⊢ e₃ : T ⊣ Γ₂
Γ_out = merge(Γ₁, Γ₂)    ← MERGED, not equal
─────────────────────────────────────
R; Γ ⊢ if e₁ then e₂ else e₃ : T ⊣ Γ_out
```

### Projections (Always Allowed)
```
R; Γ ⊢ e : T₁ × T₂ ⊣ Γ'
───────────────────────────  (T₂ implicitly dropped)
R; Γ ⊢ π₁(e) : T₁ ⊣ Γ'
```

---

## When to Use Affine

- Ergonomic development experience
- Early return / error handling patterns
- When leak prevention is handled by regions
- Compatibility with Rust-like ownership

---

## Implicit Drop

Affine types automatically insert drops at scope boundaries:

```
// This is valid in Affine Ephapax:
let s = String.new@r("unused")
42  // s implicitly dropped here
```

Compiler transforms to:
```
let s = String.new@r("unused")
drop(s);
42
```

---

## Comparison with Linear

| Aspect | Linear | Affine |
|--------|--------|--------|
| Use count | = 1 | ≤ 1 |
| Implicit drop | ✗ | ✓ |
| Unused bindings | ERROR | OK |
| Branch agreement | Required | Merged |
| Leak prevention | ✓ | ✗ |
| Ease of use | Stricter | More permissive |
