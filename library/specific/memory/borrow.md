# Operation: borrow

## Interface Signature

```
borrow: Linear a -> (&a, Linear a)
```

## Behavioral Semantics

**Purpose**: Creates a temporary immutable reference to a linear value without consuming it.

**Parameters**:
- `value`: A linear value to borrow from

**Return Value**: A pair of (borrowed reference, original value continuation).

**Properties**:
- Original value remains owned by caller
- Borrow cannot outlive the original value
- Multiple borrows allowed (shared borrowing)
- Cannot modify through borrow

**Edge Cases**:
- Using value while borrow is active is a compile-time error
- Borrow lifetime must be shorter than value lifetime

## Executable Test Cases

```yaml
test_cases:
  - input: [s]
    output: (&s, s)
    description: "Borrow creates reference and continuation"

  - input: [string]
    output: "(&string, string)"
    description: "Borrow string without consuming"
```

## Ephapax Implementation

```ephapax
let s = "hello"
let len = string_len(&s)  // Implicit borrow
// s is still usable after borrow ends
drop(s)
```
