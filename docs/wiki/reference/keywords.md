# Keywords Reference

Complete list of Ephapax keywords and their usage.

## Current Keywords

| Keyword | Usage | Example |
|---------|-------|---------|
| `let` | Variable binding | `let x = 42 in x + 1` |
| `let!` | Linear binding (explicit) | `let! s = String.new@r("x") in ...` |
| `fn` | Function definition/lambda | `fn(x: I32) -> x + 1` |
| `if` | Conditional | `if b then e1 else e2` |
| `then` | Conditional branch | `if b then ...` |
| `else` | Conditional branch | `... else e2` |
| `region` | Region scope | `region r { ... }` |
| `drop` | Explicit consumption | `drop(s)` |
| `copy` | Explicit duplication | `copy(x)` |
| `true` | Boolean literal | `let b = true` |
| `false` | Boolean literal | `let b = false` |
| `inl` | Left sum injection | `inl[Bool](42)` |
| `inr` | Right sum injection | `inr[I32](true)` |
| `case` | Sum pattern match | `case x of ...` |
| `of` | Case branches start | `case x of inl(n) -> ...` |
| `end` | Case branches end | `... end` |
| `in` | Let body | `let x = 1 in x + 1` |
| `type` | Type alias (future) | `type Point = (F64, F64)` |

## Keyword Details

### `let`

Binds a value to a name:

```ephapax
let x = 42 in
let y = x + 1 in
y * 2
```

With type annotation:

```ephapax
let x: I32 = 42 in x
```

### `let!`

Explicitly marks a binding as linear:

```ephapax
let! s = String.new@r("hello") in
print(s)  -- Must consume s
```

### `fn`

Lambda expression:

```ephapax
fn(x: I32) -> x + 1

-- Multi-argument
fn(x: I32) -> fn(y: I32) -> x + y
```

Top-level function:

```ephapax
fn add(x: I32, y: I32): I32 = x + y
```

### `if` / `then` / `else`

Conditional expression:

```ephapax
if condition then
  true_branch
else
  false_branch
```

Both branches must:
- Have the same type
- Consume the same linear variables

### `region`

Creates a scoped memory region:

```ephapax
region r {
  let s = String.new@r("hello")
  print(s)
}
-- All @r allocations freed
```

### `drop`

Explicitly consumes a linear value:

```ephapax
region r {
  let s = String.new@r("not needed")
  drop(s)  -- Returns ()
}
```

### `copy`

Duplicates an unrestricted value:

```ephapax
let x: I32 = 42
let (a, b) = copy(x)  -- (42, 42)
```

Error on linear types:

```ephapax
let s = String.new@r("hello")
copy(s)  -- ERROR: Cannot copy linear type
```

### `inl` / `inr`

Sum type constructors:

```ephapax
-- Type: I32 + Bool
let left: I32 + Bool = inl[Bool](42)
let right: I32 + Bool = inr[I32](true)
```

### `case` / `of` / `end`

Pattern matching on sums:

```ephapax
case value of
  inl(n) -> handle_left(n)
  inr(b) -> handle_right(b)
end
```

## Reserved Keywords

These are reserved for future use:

| Keyword | Planned Usage |
|---------|---------------|
| `match` | Enhanced pattern matching |
| `with` | Pattern guards |
| `where` | Local definitions |
| `forall` | Universal quantification |
| `exists` | Existential types |
| `mut` | Mutable borrows |
| `async` | Async functions |
| `await` | Async await |
| `import` | Module imports |
| `export` | Module exports |
| `module` | Module definition |
| `trait` | Type classes |
| `impl` | Trait implementation |
| `self` | Self reference |
| `Self` | Self type |
| `pub` | Public visibility |
| `priv` | Private visibility |
| `struct` | Record types |
| `enum` | Algebraic data types |
| `interface` | Interface definition |
| `class` | Type class |
| `new` | Constructor |
| `ref` | Reference creation |
