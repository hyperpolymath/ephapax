# Operation: case

## Interface Signature

```
case: (a + b), (a -> c), (b -> c) -> c
```

## Behavioral Semantics

**Purpose**: Pattern matches on a sum type, applying the appropriate function.

**Parameters**:
- `sum`: The sum value to match on
- `left_fn`: Function to apply if left variant
- `right_fn`: Function to apply if right variant

**Return Value**: Result of applying the matching function.

**Properties**:
- Exactly one branch executes
- Sum is consumed
- Both branches must return same type
- Linear values in non-taken branch are not evaluated

**Edge Cases**:
- Both branches must handle linearity correctly

## Executable Test Cases

```yaml
test_cases:
  - input: [inl(42), "x => add(x, 1)", "y => 0"]
    output: 43
    description: "Match left variant"

  - input: [inr(true), "x => 0", "y => 1"]
    output: 1
    description: "Match right variant"
```
