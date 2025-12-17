# Tutorial

A step-by-step introduction to Ephapax.

## Part 1: Basic Types

### Unrestricted Types

These types can be used any number of times:

```ephapax
let x: I32 = 42
let y: I32 = x + x + x  -- OK: I32 is unrestricted

let b: Bool = true
if b then
  if b then  -- OK: Bool is unrestricted
    print_i32(y)
  else
    print_i32(0)
else
  print_i32(1)
```

### Linear Types

Strings are linear - must be used exactly once:

```ephapax
region r {
  let s: String@r = String.new@r("hello")

  -- Choose ONE of these:
  print(s)           -- Consumes s
  -- OR
  drop(s)            -- Explicitly discards s
  -- OR
  let t = use_string(s)  -- Pass to function
}
```

## Part 2: Functions

### Defining Functions

```ephapax
fn add(x: I32, y: I32): I32 = x + y

fn greet(name: String@r): String@r =
  let hello = String.new@r("Hello, ")
  String.concat(hello, name)  -- Consumes both, returns result
```

### Linear Function Arguments

When a function takes a linear argument, it **must** consume it:

```ephapax
-- This function consumes the string
fn consume_string(s: String@r): () =
  drop(s)

-- This function transforms the string
fn shout(s: String@r): String@r =
  String.concat(s, String.new@r("!"))
```

## Part 3: Borrowing

### The Problem

What if you want to inspect a value without consuming it?

```ephapax
-- BAD: This consumes s!
fn bad_length(s: String@r): I32 =
  String.len(s)  -- s is consumed... but we might want it back!
```

### The Solution: Borrows

Use `&` to create a temporary borrow:

```ephapax
region r {
  let s = String.new@r("hello")

  -- Borrow s to get its length
  let len = String.len(&s)  -- &s is a borrow, s is NOT consumed

  -- s is still available!
  print(s)  -- Consumes s here
}
```

### Borrow Rules

1. Borrows cannot escape their scope
2. Borrows cannot be stored in data structures
3. Borrows cannot be returned from functions

```ephapax
-- ERROR: Cannot return a borrow
fn bad_borrow(s: String@r): &String@r =
  &s  -- Error: borrow would escape
```

## Part 4: Products (Pairs)

### Creating Pairs

```ephapax
let pair: (I32, Bool) = (42, true)
let first = pair.0   -- 42
let second = pair.1  -- true
```

### Linear Pairs

If a pair contains a linear value, the pair is linear:

```ephapax
region r {
  let s1 = String.new@r("hello")
  let s2 = String.new@r("world")

  let pair: (String@r, String@r) = (s1, s2)

  -- Destructure to use both
  let (a, b) = pair
  print(a)
  print(b)
}
```

### Projection Restrictions

```ephapax
region r {
  let s = String.new@r("hello")
  let pair = (s, 42)

  -- ERROR: Cannot project pair.1 because pair.0 is linear
  -- let n = pair.1  -- Would leak s!

  -- Instead, destructure:
  let (str, n) = pair
  print(str)  -- Consume the string
  -- n is now available
}
```

## Part 5: Sums (Variants)

### Creating Sums

```ephapax
-- Left injection
let left: I32 + Bool = inl[Bool](42)

-- Right injection
let right: I32 + Bool = inr[I32](true)
```

### Pattern Matching

```ephapax
fn describe(x: I32 + Bool): String@r =
  case x of
    inl(n) -> String.new@r("It's a number")
    inr(b) -> String.new@r("It's a boolean")
  end
```

### Linear Sums

Both branches must handle linear values the same way:

```ephapax
region r {
  let s = String.new@r("hello")
  let choice: I32 + String@r = inr[I32](s)

  case choice of
    inl(n) ->
      -- No string to consume here
      print_i32(n)
    inr(str) ->
      -- Must consume str
      print(str)
  end
}
```

## Part 6: Regions

### Nested Regions

```ephapax
region outer {
  let s1 = String.new@outer("outer string")

  region inner {
    let s2 = String.new@inner("inner string")

    -- Can use both here
    let len1 = String.len(&s1)
    let len2 = String.len(&s2)

    print(s2)  -- Consumed before inner exits
  }
  -- inner memory freed here

  print(s1)  -- s1 still available
}
-- outer memory freed here
```

### Region Escape Prevention

```ephapax
region r {
  let s = String.new@r("hello")

  -- ERROR: Cannot return s, it would escape region r
  s  -- Type error: String@r cannot escape region r
}
```

## Part 7: Conditionals

### Both Branches Must Match

```ephapax
region r {
  let s = String.new@r("hello")
  let b = true

  if b then
    print(s)     -- Consumes s
  else
    drop(s)      -- Must also consume s!
}
```

### Returning Values

```ephapax
fn max(x: I32, y: I32): I32 =
  if x > y then x else y
```

## Part 8: Explicit Resource Management

### Drop

Explicitly consume a linear value without using it:

```ephapax
region r {
  let s = String.new@r("not needed")
  drop(s)  -- Explicitly consumed, returns ()
}
```

### Copy

Duplicate an unrestricted value:

```ephapax
let x: I32 = 42
let pair: (I32, I32) = copy(x)  -- (42, 42)
```

Note: `copy` only works on unrestricted types!

```ephapax
region r {
  let s = String.new@r("hello")
  -- ERROR: Cannot copy linear types
  let pair = copy(s)  -- Type error!
}
```

## Summary

| Concept | Key Point |
|---------|-----------|
| Linear types | Must be used exactly once |
| Unrestricted types | Can be used any number of times |
| Regions | Scoped memory allocation |
| Borrows | Temporary non-consuming access |
| Products | Pairs of values |
| Sums | Tagged unions |
| Drop | Explicit consumption |
| Copy | Duplication (unrestricted only) |

## Next Steps

- [Types Reference](../language/types.md)
- [Standard Library](../reference/stdlib/index.md)
- [Tooling Guide](../tooling/cli.md)
