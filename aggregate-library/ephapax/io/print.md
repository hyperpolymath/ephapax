# Operation: print

## Interface Signature

```
print: &String -> Unit
```

## Behavioral Semantics

**Purpose**: Outputs a string to standard output without a trailing newline.

**Parameters**:
- `s`: A borrowed reference to the string to print

**Return Value**: Unit

**Properties**:
- Takes a borrow (non-consuming)
- No trailing newline added
- Immediate output (not buffered)

**Edge Cases**:
- Empty string prints nothing

## Executable Test Cases

```yaml
test_cases:
  - input: ["hello"]
    output: ()
    side_effect: "hello printed to stdout"
    description: "Print string"

  - input: [""]
    output: ()
    side_effect: "nothing printed"
    description: "Print empty string"
```
