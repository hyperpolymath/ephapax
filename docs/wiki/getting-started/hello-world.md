# Hello World

Your first Ephapax program.

## The Code

Create a file `hello.epx`:

```ephapax
-- hello.epx
-- Our first Ephapax program

fn main(): () =
  region r {
    let greeting = String.new@r("Hello, ")
    let name = String.new@r("World!")
    let message = String.concat(greeting, name)
    print(message)
  }
```

## Understanding the Code

### 1. Region Declaration

```ephapax
region r {
  ...
}
```

Creates a memory region `r`. All allocations inside are freed when the region exits.

### 2. String Allocation

```ephapax
let greeting = String.new@r("Hello, ")
```

- `String.new@r` allocates a string in region `r`
- The `@r` annotation specifies which region owns the string
- `greeting` is a **linear** value - must be used exactly once

### 3. String Concatenation

```ephapax
let message = String.concat(greeting, name)
```

- `String.concat` **consumes** both `greeting` and `name`
- After this line, `greeting` and `name` cannot be used
- Returns a new string `message` (also linear)

### 4. Output

```ephapax
print(message)
```

- Consumes `message` by printing it
- All linear values are now consumed

### 5. Region Exit

When the `region r` block ends:
- All memory allocated in `r` is freed
- No garbage collection needed

## Running the Program

```bash
# Compile to WASM
ephapax build hello.epx -o hello.wasm

# Run
ephapax run hello.wasm
```

Output:
```
Hello, World!
```

## What Would Fail?

### Using a String Twice

```ephapax
fn bad_example(): () =
  region r {
    let s = String.new@r("hello")
    print(s)
    print(s)  -- ERROR: s already consumed
  }
```

Error:
```
error[E0001]: linear variable `s` used more than once
 --> bad.epx:5:11
  |
4 |     print(s)
  |           - first use here
5 |     print(s)
  |           ^ second use here (not allowed)
```

### Not Using a String

```ephapax
fn also_bad(): () =
  region r {
    let s = String.new@r("hello")
    -- ERROR: s is never consumed
  }
```

Error:
```
error[E0002]: linear variable `s` not consumed
 --> also_bad.epx:3:9
  |
3 |     let s = String.new@r("hello")
  |         ^ must be used before region exits
```

## Next Steps

- [Tutorial](tutorial.md) - A complete walkthrough
- [Linearity](../language/linearity.md) - Understanding linear types
- [Regions](../language/regions.md) - Memory management with regions
