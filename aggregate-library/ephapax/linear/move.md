# Operation: move

## Interface Signature

```
move: Linear a -> Linear a
```

## Behavioral Semantics

**Purpose**: Transfers ownership of a linear value, consuming the source binding.

**Parameters**:
- `value`: A linear value to transfer

**Return Value**: The same value, now owned by the destination binding.

**Properties**:
- Source binding becomes unusable after move
- Zero-cost at runtime (semantic operation only)
- Preserves value identity: `move(x) ≡ x`

**Edge Cases**:
- Moving an already-moved value is a compile-time error
- Moving through a borrow is not permitted

## Executable Test Cases

```yaml
test_cases:
  - input: [x]
    output: x
    postcondition: "x is no longer accessible"
    description: "Move transfers ownership"

  - input: [pair(a, b)]
    output: pair(a, b)
    description: "Move works on compound linear values"
```
