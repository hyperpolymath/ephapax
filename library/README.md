# Ephapax Library

This directory contains the Ephapax standard library specifications.

## Structure

```
library/
├── common/           # Common Library (from aggregate-library)
│   ├── arithmetic/   # add, subtract, multiply, divide, modulo
│   ├── comparison/   # less_than, greater_than, equal, etc.
│   ├── logical/      # and, or, not
│   ├── string/       # concat, length, substring
│   ├── collection/   # map, filter, fold, contains
│   └── conditional/  # if_then_else
│
└── specific/         # Ephapax-Specific Library
    ├── linear/       # Linear type operations (move, drop, copy)
    ├── region/       # Region-based memory (new_region, alloc_in)
    ├── memory/       # Memory operations (borrow)
    └── wasm/         # WebAssembly compilation
```

## Common Library

The Common Library contains 20 operations shared across all languages in the aggregate-library ecosystem. These represent the intersection of functionality available in radically different programming paradigms.

See: https://github.com/hyperpolymath/aggregate-library

## Ephapax-Specific Library

Operations unique to Ephapax's linear type system:

### Linear Types (`linear/`)
- `move` - Transfer ownership of linear values
- `drop` - Explicitly consume linear values
- `copy` - Duplicate unrestricted values

### Regions (`region/`)
- `new_region` - Create scoped memory regions
- `alloc_in` - Allocate in specific regions

### Memory (`memory/`)
- `borrow` - Create temporary references

### WebAssembly (`wasm/`)
- `compile_to_wasm` - Compile to WebAssembly binary

## Usage

Library specifications are in Markdown format with:
1. Interface signatures
2. Behavioral semantics
3. Executable test cases
4. Ephapax implementation examples
