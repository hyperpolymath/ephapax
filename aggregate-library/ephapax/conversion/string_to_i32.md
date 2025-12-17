# Operation: string_to_i32

## Interface Signature

```
string_to_i32: &String -> Option I32
```

## Behavioral Semantics

**Purpose**: Parses a string as a 32-bit integer.

**Parameters**:
- `s`: A borrowed reference to the string to parse

**Return Value**: Some(n) if valid integer, None if parse fails.

**Properties**:
- Accepts optional leading minus sign
- Rejects leading/trailing whitespace
- Takes borrow (non-consuming)

**Edge Cases**:
- Overflow returns None
- Empty string returns None
- Non-numeric characters return None

## Executable Test Cases

```yaml
test_cases:
  - input: ["42"]
    output: Some(42)
    description: "Parse positive"

  - input: ["-17"]
    output: Some(-17)
    description: "Parse negative"

  - input: ["hello"]
    output: None
    description: "Invalid input"

  - input: [""]
    output: None
    description: "Empty string"
```
