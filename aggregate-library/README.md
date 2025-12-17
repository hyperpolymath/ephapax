# Ephapax Aggregate Library

The complete standard library for Ephapax = Common Library + Ephapax-Specific Library.

## Structure

```
aggregate-library/
├── common/              # Common Library (22 operations)
│   ├── arithmetic/      # add, subtract, multiply, divide, modulo
│   ├── comparison/      # equal, not_equal, less_than, greater_than, less_equal, greater_equal
│   ├── logical/         # and, or, not
│   ├── string/          # concat, length, substring
│   ├── collection/      # map, filter, fold, contains
│   └── conditional/     # if_then_else
│
└── ephapax/             # Ephapax-Specific Library (17 operations)
    ├── linear/          # move, drop, copy, borrow
    ├── region/          # new_region, alloc_in
    ├── io/              # print, println, read_line
    ├── conversion/      # i32_to_string, string_to_i32
    ├── product/         # pair, fst, snd
    └── sum/             # inl, inr, case
```

## Common Library

Universal operations shared across all languages in the aggregate-library ecosystem. These 22 operations represent the intersection of functionality across radically different programming paradigms.

Source: https://github.com/hyperpolymath/aggregate-library

## Ephapax-Specific Library

Operations unique to Ephapax's linear type system and region-based memory management:

### Linear Types (4 operations)
- `move` - Transfer ownership of linear values
- `drop` - Explicitly consume linear values
- `copy` - Duplicate unrestricted values
- `borrow` - Create temporary references

### Regions (2 operations)
- `new_region` - Create scoped memory regions
- `alloc_in` - Allocate in specific regions

### I/O (3 operations)
- `print` - Output string without newline
- `println` - Output string with newline
- `read_line` - Read line from stdin

### Conversion (2 operations)
- `i32_to_string` - Integer to string
- `string_to_i32` - Parse string as integer

### Product Types (3 operations)
- `pair` - Construct pairs
- `fst` - Extract first element
- `snd` - Extract second element

### Sum Types (3 operations)
- `inl` - Inject left
- `inr` - Inject right
- `case` - Pattern match on sum

## Total: 39 Operations

Combined, the Ephapax standard library provides 39 fully-specified operations.
