# Operation: println

## Interface Signature

```
println: &String -> Unit
```

## Behavioral Semantics

**Purpose**: Outputs a string to standard output with a trailing newline.

**Parameters**:
- `s`: A borrowed reference to the string to print

**Return Value**: Unit

**Properties**:
- Takes a borrow (non-consuming)
- Appends newline after string
- Flushes output buffer

**Edge Cases**:
- Empty string prints just a newline

## Executable Test Cases

```yaml
test_cases:
  - input: ["hello"]
    output: ()
    side_effect: "hello\\n printed to stdout"
    description: "Print string with newline"

  - input: [""]
    output: ()
    side_effect: "\\n printed"
    description: "Print just newline"
```
