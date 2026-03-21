# tree-sitter-ephapax

<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

Tree-sitter grammar for [Ephapax](https://github.com/hyperpolymath/ephapax) — a dyadic language with affine and linear types.

## Usage

```bash
npm install
npx tree-sitter generate
npx tree-sitter test
```

## Features

- Full syntax support: `let`, `let!`, `region`, `@r` annotations
- Highlights distinguish linear (`let!`) from affine (`let`) bindings
- Region annotations (`@r`) highlighted as labels
- Local variable tracking for scope-aware navigation

## File Extension

`.eph`
