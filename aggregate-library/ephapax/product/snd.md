# Operation: snd

## Interface Signature

```
snd: (a, b) -> b
```

## Behavioral Semantics

**Purpose**: Extracts the second element of a pair, consuming the pair.

**Parameters**:
- `p`: A pair to destructure

**Return Value**: The second element of the pair.

**Properties**:
- Consumes the pair
- First element must be handled (dropped if linear)
- For non-consuming access, use borrow

**Edge Cases**:
- If first element is linear, it is implicitly dropped

## Executable Test Cases

```yaml
test_cases:
  - input: [(1, 2)]
    output: 2
    description: "Extract second"

  - input: [("hello", "world")]
    output: "world"
    postcondition: "hello is dropped"
    description: "Second of string pair"
```
