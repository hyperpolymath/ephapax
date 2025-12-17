# Standard Library

Overview of the Ephapax standard library.

## Status

The standard library is under development. Currently available:

| Module | Status | Description |
|--------|--------|-------------|
| `String` | Partial | String operations |
| `core` | Planned | Core types and traits |
| `collections` | Planned | Data structures |
| `io` | Planned | Input/output |
| `mem` | Planned | Memory utilities |

## String Module

### Types

```ephapax
String@r  -- String allocated in region r
```

### Functions

#### `String.new`

Allocate a new string:

```ephapax
String.new@r(literal: &str) -> String@r
```

Example:

```ephapax
region r {
  let s = String.new@r("hello")
  -- s is a linear String@r
}
```

#### `String.len`

Get string length (borrows):

```ephapax
String.len(s: &String@r) -> I32
```

Example:

```ephapax
region r {
  let s = String.new@r("hello")
  let len = String.len(&s)  -- 5
  print(s)
}
```

#### `String.concat`

Concatenate two strings (consumes both):

```ephapax
String.concat(s1: String@r, s2: String@r) -> String@r
```

Example:

```ephapax
region r {
  let a = String.new@r("hello, ")
  let b = String.new@r("world")
  let c = String.concat(a, b)  -- "hello, world"
  print(c)
}
```

#### `String.eq` (Planned)

Compare strings for equality:

```ephapax
String.eq(s1: &String@r, s2: &String@r) -> Bool
```

#### `String.slice` (Planned)

Extract a substring:

```ephapax
String.slice(s: &String@r, start: I32, end: I32) -> String@r
```

## Core Module (Planned)

### Types

```ephapax
Option[T] = T + ()           -- Optional value
Result[T, E] = T + E         -- Success or error
```

### Functions

```ephapax
-- Option operations
Option.some[T](value: T) -> Option[T]
Option.none[T]() -> Option[T]
Option.map[T, U](opt: Option[T], f: T -> U) -> Option[U]

-- Result operations
Result.ok[T, E](value: T) -> Result[T, E]
Result.err[T, E](error: E) -> Result[T, E]
Result.map[T, U, E](res: Result[T, E], f: T -> U) -> Result[U, E]
```

## Collections Module (Planned)

### Vec

Dynamic array:

```ephapax
Vec.new@r[T]() -> Vec[T]@r
Vec.push(v: &mut Vec[T]@r, item: T) -> ()
Vec.pop(v: &mut Vec[T]@r) -> Option[T]
Vec.len(v: &Vec[T]@r) -> I32
Vec.get(v: &Vec[T]@r, index: I32) -> Option[&T]
```

### HashMap (Planned)

Hash table:

```ephapax
HashMap.new@r[K, V]() -> HashMap[K, V]@r
HashMap.insert(m: &mut HashMap[K, V]@r, key: K, value: V) -> Option[V]
HashMap.get(m: &HashMap[K, V]@r, key: &K) -> Option[&V]
HashMap.remove(m: &mut HashMap[K, V]@r, key: &K) -> Option[V]
```

## I/O Module (Planned)

### Console

```ephapax
print(s: String@r) -> ()
print_i32(n: I32) -> ()
print_line(s: String@r) -> ()
read_line@r() -> String@r
```

### File (WASI)

```ephapax
File.open@r(path: &String@r) -> Result[File@r, IoError]
File.read(f: &mut File@r, buf: &mut [u8]) -> Result[I32, IoError]
File.write(f: &mut File@r, data: &[u8]) -> Result[I32, IoError]
File.close(f: File@r) -> Result[(), IoError]
```

## Memory Module (Planned)

### Region Utilities

```ephapax
-- Get current region allocation size
region_size(r: Region) -> I32

-- Check if in a region
in_region() -> Bool
```

### Allocation

```ephapax
-- Low-level allocation
alloc@r(size: I32) -> Ptr@r
dealloc(ptr: Ptr@r) -> ()
```

## Using the Standard Library

### Import (Future)

```ephapax
import std.string.{String, concat}
import std.collections.Vec
```

### Prelude

Automatically available:

- Base types: `()`, `Bool`, `I32`, `I64`, `F32`, `F64`
- `String` module
- `print` function
- `drop`, `copy` functions
