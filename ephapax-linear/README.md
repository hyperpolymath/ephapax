# ephapax-linear

> ## 🛑 First-read disambiguation
>
> This crate is part of **`hyperpolymath/ephapax`** — a research language for
> compile-time WebAssembly memory safety, formally verified in Coq + Idris2.
>
> **`ephapax-linear` is *not* `hyperpolymath/affinescript`.** AffineScript is
> a separate, unrelated language (JS/TS/ReScript successor, OCaml + ReScript
> runtime). The two share only the compile target (`hyperpolymath/typed-wasm`).
>
> **Internal naming trap (important):** This crate implements *both*
> sublanguages of Ephapax — `ephapax-linear` (strict core) AND `ephapax-affine`
> (versatile prototyping companion). The name of the crate is `ephapax-linear`
> for historical reasons, but **the affine grammar in this crate is NOT
> `AffineScript`.** The lexical overlap of the word `affine` is a coincidence
> of substructural-logic family terminology, not a project relationship. Do
> not apply tactics, lessons, or framings from `hyperpolymath/affinescript`
> here, and vice versa.
>
> Canonical disambiguation:
> [`hyperpolymath/nextgen-languages/docs/disambiguation/ephapax-vs-affinescript.md`](https://github.com/hyperpolymath/nextgen-languages/blob/main/docs/disambiguation/ephapax-vs-affinescript.md).

Standalone linear/affine discipline checker for the Ephapax language.

> **Naming note.** This crate is called `ephapax-linear` for historical
> reasons; it implements **both** L2 modalities (Linear and Affine). The
> two are not different languages — they are two admissible-derivation
> regimes over the same syntax and semantics. See
> [`docs/vision/EPHAPAX-VISION.adoc`](../docs/vision/EPHAPAX-VISION.adoc)
> for the dyad framing, and
> [`formal/PRESERVATION-DESIGN.md §5`](../formal/PRESERVATION-DESIGN.md)
> for the L2 layer in the four-layer architecture.

## Two L2 Modalities

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

SPDX-License-Identifier: CC-BY-SA-4.0
<!-- Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk> -->
