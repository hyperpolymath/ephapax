# Regions

Ephapax uses region-based memory management for efficient, deterministic deallocation.

## What is a Region?

A region is a scope-based memory arena:

```ephapax
region r {
  -- All allocations here use region r
  let s1 = String.new@r("hello")
  let s2 = String.new@r("world")

  -- Use the strings...
  print(s1)
  print(s2)
}
-- Region r exits: ALL memory freed in O(1)
```

## Benefits

| Benefit | Explanation |
|---------|-------------|
| **Bulk deallocation** | Free all region memory at once |
| **No GC pauses** | Deterministic, predictable timing |
| **Cache locality** | Allocations are contiguous |
| **Zero overhead** | No reference counting or tracing |

## Region Syntax

### Basic Region

```ephapax
region r {
  -- r is active here
  let s = String.new@r("data")
  use(s)
}
-- r freed here
```

### Region Annotation

The `@r` annotation specifies which region owns an allocation:

```ephapax
String.new@r("hello")  -- Allocate in region r
Vec.new@heap()         -- Allocate in heap region (future)
```

## Nested Regions

Regions can be nested:

```ephapax
region outer {
  let s1 = String.new@outer("outer")

  region inner {
    let s2 = String.new@inner("inner")

    -- Both s1 and s2 available here
    let combined = String.concat(
      String.copy(&s1),  -- Borrow s1, copy it
      s2                  -- Consume s2
    )
    print(combined)
  }
  -- inner freed here, s2's memory reclaimed

  print(s1)  -- s1 still available
}
-- outer freed here
```

## Region Escape Prevention

Strings cannot escape their region:

```ephapax
-- ERROR: This would allow escaping
fn bad(): String@r =
  region r {
    String.new@r("would escape")  -- Error!
  }
  -- r freed, but string would still exist?
```

The type system prevents this:

```
error[E0004]: type `String@r` cannot escape region `r`
 --> example.epx:3:5
  |
2 | fn bad(): String@r =
  |           -------- return type mentions region `r`
3 |   region r {
  |   ^^^^^^^^ region starts here
4 |     String.new@r("would escape")
  |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ value would escape
5 |   }
  |   - region ends here, but value would still be referenced
```

## Valid Return Patterns

### Return Before Region

```ephapax
fn good1(): I32 =
  region r {
    let s = String.new@r("hello")
    let len = String.len(&s)
    drop(s)
    len  -- I32 is not region-scoped, can return
  }
```

### Transform and Return

```ephapax
fn good2(input: String@outer): String@outer =
  region r {
    let temp = String.new@r("prefix: ")
    let result = String.concat_to@outer(temp, input)
    -- temp consumed, result in outer region
    result
  }
```

### Process and Discard

```ephapax
fn good3(s: String@r): () =
  region local {
    let temp = transform@local(s)
    analyze(temp)
    drop(temp)
  }
  -- Returns (), no values escape
```

## Region Parameters (Future)

Functions can be parameterized over regions:

```ephapax
fn duplicate<r>(s: &String@r): String@r =
  String.copy@r(s)
```

## Memory Layout

Regions use bump allocation:

```
Region r:
┌─────────────────────────────────────┐
│ String "hello" │ String "world" │...│
└─────────────────────────────────────┘
    ↑ bump_ptr moves forward
```

On region exit:
- Bump pointer reset to region start
- All memory instantly "freed"
- O(1) deallocation regardless of allocation count

## Region vs Garbage Collection

| Aspect | Regions | GC |
|--------|---------|-----|
| Deallocation | Deterministic | Non-deterministic |
| Pause times | None | Stop-the-world possible |
| Memory overhead | Minimal | Needs extra space |
| Complexity | Compile-time | Runtime |
| Fragmentation | Per-region | Requires compaction |

## Region Best Practices

### 1. Minimize Region Scope

```ephapax
-- GOOD: Small region scope
fn process(data: &[u8]): I32 =
  region r {
    let parsed = parse@r(data)
    let result = compute(parsed)
    drop(parsed)
    result
  }
```

### 2. Match Region to Lifetime

```ephapax
-- Processing request data
fn handle_request(req: Request): Response =
  region request_lifetime {
    let body = parse_body@request_lifetime(req)
    let response = process(body)
    -- body freed when request handling done
    response
  }
```

### 3. Use Nested Regions for Temporary Work

```ephapax
fn complex_operation(): Result =
  region main {
    let input = prepare@main()

    region scratch {
      -- Temporary allocations freed early
      let temp1 = compute_step1@scratch(input)
      let temp2 = compute_step2@scratch(temp1)
      let result = finalize@main(temp2)
      result
    }
    -- scratch freed, but result persists

    format@main(result)
  }
```

## Common Patterns

### Arena Pattern

```ephapax
fn process_batch(items: &[Item]): Summary =
  region arena {
    let results = Vec.new@arena()
    for item in items {
      let processed = process@arena(item)
      results.push(processed)
    }
    summarize(&results)  -- Returns Summary (not region-bound)
  }
  -- All intermediate results freed at once
```

### Request-Response Pattern

```ephapax
fn handle(request: Request@r): Response@r =
  region temp {
    let parsed = parse@temp(request)
    let validated = validate@temp(parsed)
    build_response@r(validated)
  }
```

## Further Reading

- [Memory Layout](../internals/codegen.md#memory-layout)
- [Linearity](linearity.md) - How regions interact with linear types
- [Borrowing](borrowing.md) - Accessing data across regions
