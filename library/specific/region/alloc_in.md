# Operation: alloc_in

## Interface Signature

```
alloc_in: Region r, a -> a @ r
```

## Behavioral Semantics

**Purpose**: Allocates a value in a specific memory region, returning a region-tagged reference.

**Parameters**:
- `region`: The region handle to allocate in
- `value`: The value to allocate

**Return Value**: A reference to the allocated value, tagged with the region lifetime.

**Properties**:
- Value is allocated in the specified region's memory
- Reference lifetime is bounded by region lifetime
- Supports nested region allocation

**Edge Cases**:
- Using an expired region handle is a compile-time error
- Allocated value inherits linearity from source type

## Executable Test Cases

```yaml
test_cases:
  - input: [r, "hello"]
    output: "hello @ r"
    description: "Allocate string in region"

  - input: [r, (1, 2)]
    output: "(1, 2) @ r"
    description: "Allocate pair in region"
```

## Ephapax Implementation

```ephapax
region |r| {
    let s = alloc_in(r, "hello world")
    // s has type String @ r
    let len = string_len(&s)
    len  // Return computed value, s freed with region
}
```
