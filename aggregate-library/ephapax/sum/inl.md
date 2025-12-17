# Operation: inl

## Interface Signature

```
inl: a -> (a + b)
```

## Behavioral Semantics

**Purpose**: Injects a value into the left side of a sum type.

**Parameters**:
- `value`: The value to inject

**Return Value**: A sum type with the value in the left position.

**Properties**:
- Consumes the value (if linear)
- Right type is inferred from context
- Sum is linear if component is linear

**Edge Cases**:
- Type annotation may be required for inference

## Executable Test Cases

```yaml
test_cases:
  - input: [42]
    output: inl(42)
    description: "Inject integer left"

  - input: ["hello"]
    output: inl("hello")
    description: "Inject string left"
```
