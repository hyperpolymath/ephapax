# Operation: copy

## Interface Signature

```
copy: Unrestricted a -> (a, a)
```

## Behavioral Semantics

**Purpose**: Creates a duplicate of an unrestricted (copyable) value.

**Parameters**:
- `value`: An unrestricted value that can be copied

**Return Value**: A pair containing two copies of the value.

**Properties**:
- Only works on unrestricted types (I32, I64, F32, F64, Bool, Unit)
- Linear types cannot be copied
- Both copies are independent values

**Edge Cases**:
- Attempting to copy a linear value is a compile-time error
- Copying a borrowed reference creates two borrows

## Executable Test Cases

```yaml
test_cases:
  - input: [42]
    output: (42, 42)
    description: "Copy duplicates integers"

  - input: [true]
    output: (true, true)
    description: "Copy duplicates booleans"

  - input: ["hello"]
    error: "Cannot copy linear type String"
    description: "Strings are linear and cannot be copied"
```

## Ephapax Implementation

```ephapax
let x: I32 = 42
let (a, b) = copy(x)  // Both a and b are 42
// x, a, and b are all usable
```
