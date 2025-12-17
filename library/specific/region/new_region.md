# Operation: new_region

## Interface Signature

```
new_region: (Region r -> a) -> a
```

## Behavioral Semantics

**Purpose**: Creates a new memory region and executes a computation within it. All allocations in the region are automatically freed when the region ends.

**Parameters**:
- `body`: A function that receives the region handle and produces a result

**Return Value**: The result of the body computation (must not contain region-local references).

**Properties**:
- Region-based memory management (Tofte-Talpin style)
- All region-local allocations are freed at region end
- Region handles cannot escape their scope
- Nested regions are supported

**Edge Cases**:
- Returning a region-local reference is a compile-time error
- Region lifetime is lexically scoped

## Executable Test Cases

```yaml
test_cases:
  - input: ["|r| 42"]
    output: 42
    description: "Region returns non-allocated value"

  - input: ["|r| alloc_in(r, 'hello').len()"]
    output: 5
    description: "Compute with region-allocated value"

  - input: ["|r| alloc_in(r, 'hello')"]
    error: "Region-local reference escapes"
    description: "Cannot return region-local references"
```

## Ephapax Implementation

```ephapax
let result = region |r| {
    let s = alloc_in(r, "temporary string")
    string_len(&s)  // Use the string, return computed value
}
// s is automatically freed, result = 16
```
