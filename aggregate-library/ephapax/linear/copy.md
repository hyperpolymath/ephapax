# Operation: copy

## Interface Signature

```
copy: Unrestricted a -> (a, a)
```

## Behavioral Semantics

**Purpose**: Duplicates an unrestricted (non-linear) value.

**Parameters**:
- `value`: An unrestricted value (I32, I64, F32, F64, Bool, Unit)

**Return Value**: A pair containing two copies of the value.

**Properties**:
- Only valid for unrestricted types
- Both copies are independent
- Linear types cannot be copied (compile-time error)

**Edge Cases**:
- Attempting to copy a linear type fails at compile time

## Executable Test Cases

```yaml
test_cases:
  - input: [42]
    output: (42, 42)
    description: "Copy integer"

  - input: [true]
    output: (true, true)
    description: "Copy boolean"

  - input: ["hello"]
    error: "Linear type cannot be copied"
    description: "Strings are linear"
```
