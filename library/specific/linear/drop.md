# Operation: drop

## Interface Signature

```
drop: Linear a -> Unit
```

## Behavioral Semantics

**Purpose**: Explicitly consumes a linear value, releasing its resources.

**Parameters**:
- `value`: A linear value to be dropped

**Return Value**: Unit (the value is consumed)

**Properties**:
- Must be called exactly once for each linear value
- Cannot be called on borrowed values
- Triggers region cleanup if value is region-allocated

**Edge Cases**:
- Dropping an already-dropped value is a compile-time error
- Values in active regions are dropped when region ends

## Executable Test Cases

```yaml
test_cases:
  - input: [x]
    output: ()
    description: "Drop consumes the value"
    postcondition: "x resources are released"

  - input: [region_allocated_value]
    output: ()
    description: "Drop triggers region cleanup"
```

## Ephapax Implementation

```ephapax
let x = alloc_string("hello")
drop(x)  // Explicitly consume x
// x is no longer accessible
```
