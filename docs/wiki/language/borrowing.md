# Borrowing

Borrows provide temporary, non-consuming access to linear values.

## The Problem

Without borrowing, inspecting a value would consume it:

```ephapax
-- Without borrowing:
fn get_length_bad(s: String@r): I32 =
  String.len(s)  -- Consumes s, but we might want to keep it!

region r {
  let s = String.new@r("hello")
  let len = get_length_bad(s)  -- s consumed!
  -- print(s)  -- ERROR: s already consumed
}
```

## The Solution: Borrows

Use `&` to create a borrow:

```ephapax
region r {
  let s = String.new@r("hello")
  let len = String.len(&s)  -- Borrow s, don't consume
  print(s)                   -- s still available!
}
```

## Borrow Syntax

### Creating a Borrow

```ephapax
&expr
```

The expression `&s` borrows `s` without consuming it.

### Functions Taking Borrows

```ephapax
fn get_length(s: &String@r): I32 =
  -- s is borrowed, not owned
  String.len(s)  -- Passes the borrow
```

## Second-Class Borrows

Borrows in Ephapax are "second-class":

| Restriction | Explanation |
|-------------|-------------|
| Cannot return | Borrows can't escape functions |
| Cannot store | Cannot put in data structures |
| Cannot escape scope | Must stay in creating scope |

### Why Second-Class?

First-class borrows (like Rust) require:
- Lifetime parameters
- Complex borrow checking
- Significant mental overhead

Second-class borrows are simpler:
- Borrows are temporary
- Cannot outlive original
- Easier to reason about

## Valid Borrow Patterns

### Inspection

```ephapax
region r {
  let s = String.new@r("hello")

  -- Borrow for length
  let len = String.len(&s)

  -- Borrow for comparison
  let starts_with_h = String.starts_with(&s, "h")

  -- Original still available
  print(s)
}
```

### Passing to Functions

```ephapax
fn analyze(s: &String@r): Analysis =
  let len = String.len(s)
  let hash = String.hash(s)
  Analysis { len, hash }

region r {
  let s = String.new@r("data")
  let analysis = analyze(&s)  -- Borrow passed
  print(s)                     -- Still have s
}
```

### Multiple Borrows

```ephapax
region r {
  let s = String.new@r("hello")

  -- Multiple borrows OK
  let len1 = String.len(&s)
  let len2 = String.len(&s)
  let eq = String.eq(&s, &s)

  print(s)  -- Consume at end
}
```

## Invalid Borrow Patterns

### Returning a Borrow

```ephapax
-- ERROR: Borrow would escape
fn bad_return(s: String@r): &String@r =
  &s

-- Error message:
-- error[E0005]: borrow `&s` would escape function
--  --> example.epx:2:3
--   |
-- 1 | fn bad_return(s: String@r): &String@r =
--   |                             --------- return type is a borrow
-- 2 |   &s
--   |   ^^ borrow created here, would escape
```

### Storing a Borrow

```ephapax
-- ERROR: Cannot store borrows
region r {
  let s = String.new@r("hello")
  let pair = (&s, 42)  -- ERROR: Cannot put borrow in pair
}
```

### Escaping Scope

```ephapax
-- ERROR: Borrow escapes its scope
fn bad_scope(): &String@r =
  region r {
    let s = String.new@r("hello")
    &s  -- ERROR: Would escape region
  }
```

## Borrow vs Own

| Aspect | Borrow (`&T`) | Owned (`T`) |
|--------|---------------|-------------|
| Consumes | No | Yes (if linear) |
| Can return | No | Yes |
| Can store | No | Yes |
| Lifetime | Current scope | Until consumed |
| Mutability | Read-only | Full |

## Mutable Borrows (Future)

For mutation, Ephapax will support mutable borrows:

```ephapax
-- Future syntax
fn append_exclaim(s: &mut String@r): () =
  String.push(s, '!')

region r {
  let s = String.new@r("hello")
  append_exclaim(&mut s)  -- Mutates in place
  print(s)  -- "hello!"
}
```

Mutable borrow rules:
- Only one mutable borrow at a time
- No shared borrows while mutably borrowed

## Borrow Coercion

Values can be implicitly coerced to borrows:

```ephapax
fn takes_borrow(s: &String@r): I32 =
  String.len(s)

region r {
  let s = String.new@r("hello")

  -- Explicit borrow
  let len1 = takes_borrow(&s)

  -- Auto-borrow in some contexts (TBD)
  -- let len2 = takes_borrow(s)  -- Might auto-borrow
}
```

## Best Practices

### 1. Use Borrows for Queries

```ephapax
-- GOOD: Query functions take borrows
fn get_length(s: &String@r): I32 = String.len(s)
fn is_empty(s: &String@r): Bool = String.len(s) == 0
fn starts_with(s: &String@r, prefix: &String@r): Bool = ...
```

### 2. Own When Transforming

```ephapax
-- GOOD: Transformation consumes input
fn uppercase(s: String@r): String@r =
  -- Returns new string, original consumed
  String.map(s, char_to_upper)
```

### 3. Document Ownership

```ephapax
-- Clear from type: consumes s
fn consume_and_process(s: String@r): Result

-- Clear from type: only borrows
fn inspect(s: &String@r): Info
```

### 4. Minimize Borrow Scope

```ephapax
region r {
  let s = String.new@r("hello")

  -- GOOD: Borrow exists only where needed
  let info = {
    let len = String.len(&s)
    let hash = String.hash(&s)
    Info { len, hash }
  }

  -- Continue with s
  print(s)
}
```

## Further Reading

- [Linearity](linearity.md) - Linear type fundamentals
- [Regions](regions.md) - How borrows interact with regions
- [Types](types.md) - Complete type reference
