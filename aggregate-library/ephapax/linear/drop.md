# Operation: drop

## Interface Signature

```
drop: Linear a -> Unit
```

## Behavioral Semantics

**Purpose**: Explicitly consumes a linear value, releasing any associated resources.

**Parameters**:
- `value`: A linear value to consume

**Return Value**: Unit

**Properties**:
- Value is consumed and cannot be used afterward
- Required for linear values not otherwise consumed
- Triggers destructor/cleanup logic

**Edge Cases**:
- Dropping an already-consumed value is a compile-time error
- Cannot drop borrowed references

## Executable Test Cases

```yaml
test_cases:
  - input: [x]
    output: ()
    postcondition: "x resources released"
    description: "Drop consumes linear value"
```
