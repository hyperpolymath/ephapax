# Operation: move

## Interface Signature

```
move: Linear a -> Linear a
```

## Behavioral Semantics

**Purpose**: Transfers ownership of a linear value, consuming the source binding.

**Parameters**:
- `value`: A linear value to be moved

**Return Value**: The same value with ownership transferred to new binding.

**Properties**:
- Consumes the source binding (cannot be used after move)
- Zero-copy operation (semantic, not physical)
- Identity: `move(x) = x` (semantically)

**Edge Cases**:
- Moving an already-moved value is a compile-time error
- Moving a borrowed value is not allowed

## Executable Test Cases

```yaml
test_cases:
  - input: [x]
    output: x
    description: "Move transfers ownership"
    postcondition: "x is no longer accessible"

  - input: [pair(a, b)]
    output: pair(a, b)
    description: "Move transfers compound values"
```

## Ephapax Implementation

```ephapax
// Move is implicit in Ephapax - values are moved by default
let x = "hello"
let y = x  // x is moved to y, x is now inaccessible
```
