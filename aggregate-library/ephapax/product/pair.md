# Operation: pair

## Interface Signature

```
pair: a, b -> (a, b)
```

## Behavioral Semantics

**Purpose**: Constructs a product type (pair) from two values.

**Parameters**:
- `first`: The first element
- `second`: The second element

**Return Value**: A pair containing both values.

**Properties**:
- Consumes both arguments (if linear)
- Pair is linear if either component is linear
- Order preserved

**Edge Cases**:
- Nested pairs supported: `pair(pair(a, b), c)`

## Executable Test Cases

```yaml
test_cases:
  - input: [1, 2]
    output: (1, 2)
    description: "Pair of integers"

  - input: ["hello", 42]
    output: ("hello", 42)
    description: "Mixed types"

  - input: [(), ()]
    output: ((), ())
    description: "Pair of units"
```
