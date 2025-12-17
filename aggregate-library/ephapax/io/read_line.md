# Operation: read_line

## Interface Signature

```
read_line: Unit -> String
```

## Behavioral Semantics

**Purpose**: Reads a line of text from standard input.

**Parameters**:
- None (Unit input)

**Return Value**: A new linear String containing the input (without trailing newline).

**Properties**:
- Blocks until newline received
- Returns linear String (must be consumed)
- Strips trailing newline

**Edge Cases**:
- EOF returns empty string
- Very long lines may be truncated (implementation-defined)

## Executable Test Cases

```yaml
test_cases:
  - input: [()]
    stdin: "hello\\n"
    output: "hello"
    description: "Read line strips newline"

  - input: [()]
    stdin: "\\n"
    output: ""
    description: "Empty line returns empty string"
```
