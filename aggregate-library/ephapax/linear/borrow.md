# Operation: borrow

## Interface Signature

```
borrow: Linear a -> &a
```

## Behavioral Semantics

**Purpose**: Creates a temporary immutable reference to a linear value without consuming it.

**Parameters**:
- `value`: A linear value to borrow

**Return Value**: An immutable reference to the value.

**Properties**:
- Original value remains owned by caller
- Borrow lifetime must not exceed value lifetime
- Multiple concurrent borrows allowed (shared borrowing)
- Cannot mutate through borrow

**Edge Cases**:
- Using the owned value while borrow is active is a compile-time error
- Borrow cannot escape its scope

## Executable Test Cases

```yaml
test_cases:
  - input: [s]
    output: "&s"
    description: "Borrow creates reference"

  - input: [string]
    postcondition: "string still usable after borrow ends"
    description: "Non-destructive access"
```
