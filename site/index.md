---
title: Ephapax
date: 2026-03-31
---

# Ephapax

> Four-layer dyadic type system for WebAssembly memory safety.

Four orthogonal disciplines compose to guarantee compile-time memory safety without a garbage collector:

- **Regions** (L1) — capabilities threaded through every expression.
- **Linear ↔ Affine** (L2) — the dyad, mother and child.
- **Echo** (L3, planned) — irreversibility leaves typed residue.
- **Dyadic mode** (L4) — declare which side you speak from.

Mechanically formalised in Coq and Idris2. See
[design](formal/PRESERVATION-DESIGN.md) ·
[vision](docs/vision/EPHAPAX-VISION.adoc) ·
[spec](spec/SPEC.md) ·
[roadmap](ROADMAP.adoc).

## Project Links

- Website: [ephapax.org](https://ephapax.org)
- Source: [https://github.com/hyperpolymath/ephapax](https://github.com/hyperpolymath/ephapax)
- README: [project overview](https://github.com/hyperpolymath/ephapax/blob/main/README.adoc)
- Docs: [documentation directory](https://github.com/hyperpolymath/ephapax/tree/main/docs)

This page is a lightweight landing point for the repository and will grow with the project.
