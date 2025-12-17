# Operation: alloc_in

## Interface Signature

```
alloc_in: Region r, a -> a @ r
```

## Behavioral Semantics

**Purpose**: Allocates a value within a specific memory region.

**Parameters**:
- `region`: The region handle to allocate in
- `value`: The value to allocate

**Return Value**: A region-tagged reference to the allocated value.

**Properties**:
- Reference lifetime bounded by region lifetime
- Allocation uses bump pointer (fast)
- No individual deallocation; freed with region

**Edge Cases**:
- Using expired region handle is compile-time error

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
