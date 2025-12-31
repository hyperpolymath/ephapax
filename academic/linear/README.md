# Linear Ephapax

## Complete Academic Documentation

**Discipline**: Linear (use exactly once)

---

## Overview

Linear Ephapax enforces that every resource must be used **exactly once**. This provides the strongest guarantees:

| Property | Guarantee |
|----------|-----------|
| No use-after-free | ✓ |
| No double-free | ✓ |
| No memory leaks | ✓ |
| No dangling pointers | ✓ |

---

## Documents

| File | Description |
|------|-------------|
| `LINEAR-EPHAPAX-SPECIFICATION.md` | Complete formal specification |
| `proofs/LinearEphapax.v` | Coq mechanization |

---

## Key Typing Rules

### Variable Access (Linear)
```
lookup(Γ, x) = (T, false)    linear(T) = true
─────────────────────────────────────────────
R; Γ ⊢ x : T ⊣ mark(Γ, x)
```

### Let Binding (Must Use)
```
R; Γ ⊢ e₁ : T₁ ⊣ Γ'
R; Γ', x:T₁ ⊢ e₂ : T₂ ⊣ Γ'', (x:T₁, used)
linear(T₁) ⟹ used = true              ← REQUIRED
───────────────────────────────────────────────
R; Γ ⊢ let x = e₁ in e₂ : T₂ ⊣ Γ''
```

### Conditionals (Must Agree)
```
R; Γ' ⊢ e₂ : T ⊣ Γ''
R; Γ' ⊢ e₃ : T ⊣ Γ''    ← SAME OUTPUT
─────────────────────────────────────
R; Γ ⊢ if e₁ then e₂ else e₃ : T ⊣ Γ''
```

---

## When to Use Linear

- Maximum safety guarantees required
- Preventing all memory leaks is critical
- Resource protocols must be enforced
- Formal verification of resource usage

---

## Comparison with Affine

| Aspect | Linear | Affine |
|--------|--------|--------|
| Use count | = 1 | ≤ 1 |
| Implicit drop | ✗ | ✓ |
| Unused bindings | ERROR | OK |
| Branch agreement | Required | Merged |
| Leak prevention | ✓ | ✗ |
