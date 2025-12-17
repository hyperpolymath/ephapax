# Operation: fst

## Interface Signature

```
fst: (a, b) -> a
```

## Behavioral Semantics

**Purpose**: Extracts the first element of a pair, consuming the pair.

**Parameters**:
- `p`: A pair to destructure

**Return Value**: The first element of the pair.

**Properties**:
- Consumes the pair
- Second element must be handled (dropped if linear)
- For non-consuming access, use borrow

**Edge Cases**:
- If second element is linear, it is implicitly dropped

## Executable Test Cases

```yaml
test_cases:
  - input: [(1, 2)]
    output: 1
    description: "Extract first"

  - input: [("hello", "world")]
    output: "hello"
    postcondition: "world is dropped"
    description: "First of string pair"
```
