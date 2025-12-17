# Operation: new_region

## Interface Signature

```
new_region: (Region r -> a) -> a
```

## Behavioral Semantics

**Purpose**: Creates a lexically-scoped memory region. All allocations within are freed when the region ends.

**Parameters**:
- `body`: A function receiving the region handle, returning a value

**Return Value**: The result of `body`, which must not contain region-local references.

**Properties**:
- Tofte-Talpin style region-based memory management
- All region allocations freed at once (bump pointer reset)
- Region handles cannot escape their lexical scope
- Nested regions supported

**Edge Cases**:
- Returning region-local reference is compile-time error
- Region lifetime is strictly lexical

## Executable Test Cases

```yaml
test_cases:
  - input: ["|r| 42"]
    output: 42
    description: "Return non-allocated value"

  - input: ["|r| length(alloc_in(r, 'hello'))"]
    output: 5
    description: "Use region-allocated value"

  - input: ["|r| alloc_in(r, 'hello')"]
    error: "Region-local reference escapes"
    description: "Cannot return region reference"
```
