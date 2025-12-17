# Operation: i32_to_string

## Interface Signature

```
i32_to_string: I32 -> String
```

## Behavioral Semantics

**Purpose**: Converts a 32-bit integer to its string representation.

**Parameters**:
- `n`: The integer to convert

**Return Value**: A new linear String containing the decimal representation.

**Properties**:
- Negative numbers include minus sign
- No leading zeros (except for 0 itself)
- Returns linear String

**Edge Cases**:
- MIN_I32 (-2147483648) correctly represented

## Executable Test Cases

```yaml
test_cases:
  - input: [42]
    output: "42"
    description: "Positive integer"

  - input: [-17]
    output: "-17"
    description: "Negative integer"

  - input: [0]
    output: "0"
    description: "Zero"
```
