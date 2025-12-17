# Operation: inr

## Interface Signature

```
inr: b -> (a + b)
```

## Behavioral Semantics

**Purpose**: Injects a value into the right side of a sum type.

**Parameters**:
- `value`: The value to inject

**Return Value**: A sum type with the value in the right position.

**Properties**:
- Consumes the value (if linear)
- Left type is inferred from context
- Sum is linear if component is linear

**Edge Cases**:
- Type annotation may be required for inference

## Executable Test Cases

```yaml
test_cases:
  - input: [true]
    output: inr(true)
    description: "Inject boolean right"

  - input: ["error"]
    output: inr("error")
    description: "Inject string right"
```
