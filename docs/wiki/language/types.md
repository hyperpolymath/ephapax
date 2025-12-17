# Types

Complete reference for Ephapax types.

## Base Types

### Unit

The type with exactly one value:

```ephapax
let u: () = ()
```

Properties:
- Zero-sized
- Unrestricted
- Used for side-effect functions

### Boolean

```ephapax
let t: Bool = true
let f: Bool = false
```

Properties:
- Represented as `i32` in WASM (0 or 1)
- Unrestricted

### Integers

```ephapax
let a: I32 = 42
let b: I64 = 9223372036854775807
```

Properties:
- `I32`: 32-bit signed integer
- `I64`: 64-bit signed integer
- Unrestricted

### Floating Point

```ephapax
let x: F32 = 3.14
let y: F64 = 2.718281828459045
```

Properties:
- `F32`: 32-bit IEEE 754
- `F64`: 64-bit IEEE 754
- Unrestricted

## String Type

Strings are linear and region-scoped:

```ephapax
let s: String@r = String.new@r("hello")
```

Properties:
- **Linear**: Must be used exactly once
- **Region-scoped**: Tied to a specific region
- Represented as (ptr, len) pair

### String Operations

```ephapax
-- Allocation (consumes nothing, produces linear string)
let s = String.new@r("hello")

-- Length (borrows, does not consume)
let len = String.len(&s)

-- Concatenation (consumes both, produces new)
let combined = String.concat(s1, s2)

-- Comparison (borrows both)
let eq = String.eq(&s1, &s2)
```

## Function Types

```ephapax
T1 -> T2
```

A function from `T1` to `T2`.

```ephapax
-- Function type
let f: I32 -> I32 = fn(x: I32) -> x + 1

-- Multi-argument (curried)
let add: I32 -> I32 -> I32 = fn(x: I32) -> fn(y: I32) -> x + y

-- With linear types
let consume: String@r -> () = fn(s: String@r) -> drop(s)
```

### Linearity in Functions

If a function parameter is linear, the function must consume it:

```ephapax
fn process(s: String@r): I32 =
  let len = String.len(&s)
  drop(s)  -- Must consume
  len
```

## Product Types (Pairs)

```ephapax
(T1, T2)
```

A pair of values:

```ephapax
let pair: (I32, Bool) = (42, true)
let first: I32 = pair.0
let second: Bool = pair.1
```

### Linear Products

If either component is linear, the pair is linear:

```ephapax
region r {
  let s = String.new@r("hello")
  let pair: (String@r, I32) = (s, 42)

  -- Cannot project! Would leak s
  -- let n = pair.1  -- ERROR

  -- Must destructure
  let (str, n) = pair
  print(str)  -- Consume the linear part
}
```

### Destructuring

```ephapax
let pair = (1, 2)
let (a, b) = pair  -- a = 1, b = 2
```

## Sum Types (Variants)

```ephapax
T1 + T2
```

A discriminated union:

```ephapax
-- Left variant
let left: I32 + Bool = inl[Bool](42)

-- Right variant
let right: I32 + Bool = inr[I32](true)
```

### Case Analysis

```ephapax
fn describe(x: I32 + Bool): String@r =
  case x of
    inl(n) -> String.new@r("number")
    inr(b) -> String.new@r("boolean")
  end
```

### Linear Sums

Both branches must handle linear values consistently:

```ephapax
region r {
  let choice: I32 + String@r = get_choice()

  case choice of
    inl(n) -> print_i32(n)
    inr(s) -> print(s)  -- Must consume s
  end
}
```

## Borrow Types

```ephapax
&T
```

A second-class borrow:

```ephapax
region r {
  let s = String.new@r("hello")
  let len = String.len(&s)  -- &s is a borrow
  print(s)                   -- s still available
}
```

### Borrow Restrictions

1. Cannot be stored in data structures
2. Cannot be returned from functions
3. Cannot escape the scope where created

```ephapax
-- ERROR: Cannot return borrow
fn bad(s: String@r): &String@r =
  &s  -- Would escape!

-- OK: Return a value derived from borrow
fn ok(s: &String@r): I32 =
  String.len(s)
```

## Region Types

```ephapax
region r { T }
```

A value of type `T` scoped to region `r`:

```ephapax
region r {
  let s: String@r = String.new@r("in region r")
}
```

### Region Constraints

Types mentioning a region cannot escape that region:

```ephapax
-- ERROR
fn bad(): String@r =
  region r {
    String.new@r("escapes!")
  }

-- OK
fn ok(): I32 =
  region r {
    let s = String.new@r("local")
    String.len(&s)
  }
```

## Type Aliases (Future)

```ephapax
type Point = (F64, F64)
type Result[T, E] = T + E
```

## Linearity Summary

| Type | Linearity |
|------|-----------|
| `()` | Unrestricted |
| `Bool` | Unrestricted |
| `I32`, `I64` | Unrestricted |
| `F32`, `F64` | Unrestricted |
| `String@r` | Linear |
| `T1 -> T2` | Depends on return |
| `(T1, T2)` | Linear if either is |
| `T1 + T2` | Linear if either is |
| `&T` | Second-class |

## Type Checking

The type checker enforces:

1. **Linearity**: Linear values used exactly once
2. **Region safety**: No escaping region-scoped types
3. **Borrow validity**: Borrows don't escape
4. **Branch consistency**: Same linear consumption in all branches

## Further Reading

- [Linearity](linearity.md) - Linear type details
- [Regions](regions.md) - Region-based memory
- [Borrowing](borrowing.md) - Borrow semantics
- [Specification](../../spec/SPEC.md) - Formal type rules
