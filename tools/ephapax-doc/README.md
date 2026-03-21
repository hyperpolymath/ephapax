# ephapax-doc

<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->

Documentation generator for Ephapax.

Extracts doc comments (`///`) from `.eph` files and generates
HTML/Markdown documentation, including:

- Function signatures with qualifier annotations (● linear, ○ affine)
- Region parameters
- Type parameters
- Module hierarchy

## Usage

```bash
ephapax doc src/ --output docs/api/
```

## Status

Planned — depends on ephapax-syntax crate for AST parsing.
