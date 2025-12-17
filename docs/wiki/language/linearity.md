# Linear Types

The core concept of Ephapax: every linear value must be used exactly once.

## What is Linearity?

In traditional programming:

```python
# Python - values can be used arbitrarily
s = "hello"
print(s)
print(s)  # Same value used again
print(s)  # And again
# s might leak if never garbage collected
```

In Ephapax:

```ephapax
region r {
  let s = String.new@r("hello")
  print(s)   -- s consumed here
  -- print(s)  -- ERROR: s already consumed
}
```

## Linear vs Unrestricted

### Unrestricted Types

Can be used zero, one, or many times:

| Type | Example |
|------|---------|
| `()` | Unit |
| `Bool` | `true`, `false` |
| `I32` | `42` |
| `I64` | `1000000000000` |
| `F32` | `3.14` |
| `F64` | `2.718281828` |

### Linear Types

Must be used exactly once:

| Type | Example |
|------|---------|
| `String@r` | Strings in region `r` |
| `File@r` | File handles (future) |
| `Chan@r` | Channels (future) |

## Why Linearity?

### 1. No Use-After-Free

```ephapax
region r {
  let s = String.new@r("hello")
  let t = transform(s)  -- s consumed
  -- s no longer accessible, cannot use freed memory
  print(t)
}
```

### 2. No Double-Free

```ephapax
region r {
  let s = String.new@r("hello")
  free(s)
  -- free(s)  -- ERROR: s already consumed
}
```

### 3. No Memory Leaks

```ephapax
region r {
  let s = String.new@r("hello")
  -- Must consume s before region exits
}
-- ERROR: s not consumed
```

### 4. Deterministic Resource Management

Resources are released at predictable points, not "sometime later" by a GC.

## Linearity Rules

### Rule 1: Use Once

Every linear value must be used exactly once.

```ephapax
region r {
  let s = String.new@r("hello")

  -- GOOD: Used exactly once
  print(s)

  -- BAD: Used twice
  -- print(s)

  -- BAD: Not used at all
  -- (would error at region exit)
}
```

### Rule 2: Consumption is Transitive

If you pass a linear value to a function, that function "owns" it:

```ephapax
fn consume(s: String@r): () =
  print(s)

region r {
  let s = String.new@r("hello")
  consume(s)  -- s ownership transferred
  -- s no longer usable here
}
```

### Rule 3: Compound Types

A compound type is linear if any component is linear:

```ephapax
region r {
  let s = String.new@r("hello")
  let pair = (s, 42)  -- pair is linear because s is linear

  -- Must destructure to access
  let (str, n) = pair
  print(str)  -- Consume the linear part
}
```

### Rule 4: Branches Must Agree

All control flow branches must consume the same linear variables:

```ephapax
region r {
  let s = String.new@r("hello")
  let b = random_bool()

  if b then
    print(s)     -- Consumes s
  else
    drop(s)      -- Must also consume s
}
```

## Working with Linear Types

### Borrowing for Inspection

Use borrows to inspect without consuming:

```ephapax
region r {
  let s = String.new@r("hello")
  let len = String.len(&s)  -- Borrow, don't consume
  print(s)                   -- Now consume
}
```

### Transformation Chains

Chain transformations that consume and produce:

```ephapax
region r {
  let s1 = String.new@r("hello")
  let s2 = String.new@r(" world")
  let s3 = String.concat(s1, s2)  -- Consumes s1, s2; produces s3
  print(s3)                        -- Consumes s3
}
```

### Explicit Drop

When you don't need a value:

```ephapax
region r {
  let s = String.new@r("ignored")
  drop(s)  -- Explicitly consume without using
}
```

## Linearity and Functions

### Consuming Parameters

Functions that take linear parameters must consume them:

```ephapax
fn process(s: String@r): I32 =
  let len = String.len(&s)  -- Borrow to get length
  drop(s)                    -- Consume the string
  len                        -- Return the length
```

### Returning Linear Values

Functions can return linear values:

```ephapax
fn create(): String@r =
  region r {
    String.new@r("created")  -- Ownership transfers to caller
  }
```

### Higher-Order Functions (Future)

```ephapax
fn map(f: String@r -> String@r, s: String@r): String@r =
  f(s)  -- f consumes s, returns new string
```

## Error Messages

### Use After Consumption

```
error[E0001]: linear variable `s` used more than once
 --> example.epx:4:9
  |
3 |   print(s)
  |         - first use here
4 |   print(s)
  |         ^ second use (after consumption)
```

### Value Not Consumed

```
error[E0002]: linear variable `s` not consumed
 --> example.epx:2:7
  |
2 |   let s = String.new@r("hello")
  |       ^ must be consumed before scope exits
3 | }
  | - scope ends here
```

### Branch Mismatch

```
error[E0003]: branches consume different linear variables
 --> example.epx:4:3
  |
4 |   if b then
  |   ^^ branches must consume same variables
5 |     print(s)
  |           - `s` consumed in then-branch
6 |   else
7 |     ()  -- `s` not consumed in else-branch
```

## Best Practices

1. **Design for consumption**: Functions should either consume or borrow, make it clear which.

2. **Use borrows for queries**: When you only need to read, use `&`.

3. **Chain transformations**: `let result = transform(transform(initial))`

4. **Explicit drops**: When ignoring a value, use `drop()` to document intent.

5. **Keep linear scopes small**: The shorter the lifetime of linear values, the easier to reason about.

## Further Reading

- [Types](types.md) - All type definitions
- [Regions](regions.md) - Memory management
- [Borrowing](borrowing.md) - Non-consuming access
