# ephapax-linear

Standalone linear/affine discipline checker for the Ephapax language.

## Dual Grammars

This crate implements two **focused substructural grammars** — two views of the same ephapax syntax, each enforcing a different structural discipline:

| Property | Linear Grammar | Affine Grammar |
|----------|---------------|----------------|
| Exchange | Yes | Yes |
| Weakening | **No** (must consume) | **Yes** (implicit drop) |
| Contraction | **No** (single use) | **No** (single use) |
| `let!` | Exactly-once | Exactly-once (linear island) |
| `let` | Unrestricted types only | Any type |
| `drop(e)` | **Forbidden** | Permitted |
| Branch agreement | **Required** | Not required |
| Region exit | Must consume | Implicit drop (warns) |

## Dyadic Design

Ephapax is **dyadic** — both disciplines coexist per-program. `let!` always means linear, `let` always means affine. There is no global mode.

## Usage

```rust
use ephapax_linear::{check_expr, Discipline};

// Check under linear discipline
check_expr(&expr, Discipline::Linear)?;

// Check under affine discipline
check_expr(&expr, Discipline::Affine)?;
```

## Grammar Specifications

- `grammar/linear.ebnf` — Linear focused grammar (EBNF)
- `grammar/affine.ebnf` — Affine focused grammar (EBNF)

## License

SPDX-License-Identifier: PMPL-1.0-or-later
