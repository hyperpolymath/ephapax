# Linear vs Affine: Deep Dive

This lesson explains the **key difference** between linear and affine types, and why Ephapax supports both.

## The Resource Usage Spectrum

```
Unrestricted → Affine → Linear → Relevant
   (any)      (≤1)      (=1)      (≥1)
```

Most languages use **unrestricted** types (use values any number of times). Ephapax focuses on **affine** (at most once) and **linear** (exactly once).

## Affine Types: At Most Once

### Properties
- ✅ Can use zero times (drop implicitly)
- ✅ Can use one time
- ❌ Cannot use more than once

### Type Rule (Simplified)
```
Γ ⊢ x : T    (x may remain in Γ after use)
```

**Weakening is allowed**: You can throw away unused variables.

### Example

```ephapax
fn affine_example() -> i32 {
    let x = 42;
    let y = 100;

    // Use only x
    let result = x + 10;

    // y is not used - OK in affine mode!
    // y implicitly dropped

    result
}
```

### Why Affine?

**Pros**:
- Easier to use (less boilerplate)
- Better for prototyping
- Still prevents use-after-free
- Simpler type checker implementation

**Cons**:
- Doesn't prevent resource leaks
- Can accidentally drop expensive resources
- Less strict guarantees

### Languages Using Affine Types

- **Rust**: Ownership is affine (can drop owned values)
- **Cyclone**: Affine pointers
- **Clean**: Uniqueness types (affine-ish)

## Linear Types: Exactly Once

### Properties
- ❌ Cannot drop (must use)
- ✅ Must use exactly one time
- ❌ Cannot use more than once

### Type Rule (Simplified)
```
Γ ⊢ x : T ⊸ Δ    (x removed from Δ after use)
```

**No weakening**: Every variable must be consumed.

### Example

```ephapax
fn linear_example() -> i32 {
    let! x = 42;  // ! = linear
    let! y = 100;

    // Must use BOTH x and y
    let temp1 = drop(x);
    let temp2 = drop(y);

    0
}
```

### Why Linear?

**Pros**:
- Guarantees no resource leaks
- Perfect for safety-critical code
- Explicit resource management
- Stronger compiler guarantees

**Cons**:
- More boilerplate (explicit drops)
- Harder to prototype
- Stricter type checker

### Languages Using Linear Types

- **Linear Haskell**: Extension to GHC
- **Granule**: Graded modal types (includes linear)
- **Idris 2**: QTT (Quantitative Type Theory)
- **Ephapax**: First with both modes!

## Side-by-Side Comparison

### Affine Code

```ephapax
fn handle_request(req: Request) -> Response {
    // Affine mode
    let conn = open_connection();

    process(req);

    // BUG: conn never closed!
    // Compiles successfully in affine mode
    // Connection LEAKED - may run out of file descriptors

    ok_response()
}
```

**Affine mode**: ✅ Compiles
**Runtime**: ⚠️ Leaks connection

### Linear Code

```ephapax
fn handle_request(req: Request) -> Response {
    // Linear mode
    let! conn = open_connection();

    process(req);

    // TYPE ERROR: conn not consumed!
    // Compiler forces you to fix this

    ok_response()
}
```

**Linear mode**: ❌ Compile error
**Fix required**:

```ephapax
fn handle_request_fixed(req: Request) -> Response {
    let! conn = open_connection();

    process(&conn);  // Borrow, don't consume

    conn.close();  // Explicit cleanup

    ok_response()  // ✅ Now compiles!
}
```

## The Subtyping Relationship

```
Linear ⊆ Affine ⊆ Unrestricted
```

Every linear program can be made affine by allowing implicit drops.
Every affine program can be made unrestricted by allowing copying.

**Ephapax lets you move along this spectrum!**

## Real-World Scenarios

### Scenario 1: Prototyping a CLI Tool

**Use Affine Mode**:
```ephapax
fn main() -> i32 {
    let file = open("config.json");
    let config = parse(file);
    // file implicitly closed - OK for a CLI tool

    run_with_config(config);
    0
}
```

**Why**: Fast iteration, CLI tools exit anyway

### Scenario 2: Long-Running Server

**Use Linear Mode**:
```ephapax
fn handle_connection(conn: Connection!) -> Response {
    let! req = read_request(&conn);
    let! resp = handle(req);
    write_response(&conn, resp);
    conn.close();  // MUST close
    unit
}
```

**Why**: Server runs forever, leaks accumulate

### Scenario 3: Library Code

**Use Linear Mode**:
```ephapax
pub fn with_lock(lock: Lock!, callback: fn(&Lock) -> T) -> T {
    let! locked = lock.acquire();
    let result = callback(&locked);
    locked.release();
    result
}
```

**Why**: Libraries should provide strong guarantees

## Type Checking Differences

### Affine Type Checking

1. Parse program
2. Check each binding is used ≤1 times
3. Allow unused variables (implicit drop)
4. Succeed or report use-after-free errors

**Simpler**: No need to track consumption

### Linear Type Checking

1. Parse program
2. Check each binding is used **exactly** 1 time
3. **Track context through expressions**
4. Report both use-after-free AND unused variable errors

**More complex**: Must thread context through all operations

## Performance Implications

Both modes compile to identical code:
- No runtime overhead
- Same WASM output
- Same performance

**The difference is what the compiler allows you to write**, not how it runs.

## Migration Strategy

```
1. Write prototype in AFFINE mode
2. Test and refine logic
3. Switch to LINEAR mode
4. Fix "variable not consumed" errors
5. Deploy with leak prevention guarantees
```

**Example**: Add one line to your build script:
```bash
# Development
ephapax-affine myapp.eph -o myapp.wasm

# Production
ephapax-linear myapp.eph -o myapp.wasm
```

## Common Patterns

### Pattern 1: Resource Cleanup

**Affine** (may leak):
```ephapax
let file = open("data.txt");
process(file);
// file may or may not be closed
```

**Linear** (guaranteed):
```ephapax
let! file = open("data.txt");
process(&file);
file.close();  // MUST close
```

### Pattern 2: Conditional Use

**Affine**:
```ephapax
let x = compute();
let result = some_value + x;
// No need for if-else to handle x
```

**Linear**:
```ephapax
let! x = compute();
let result = some_value + drop(x);
// Must explicitly drop x to consume it
```

### Pattern 3: Error Handling

**Affine**:
```ephapax
let conn = try_connect();
// If error, conn dropped automatically
```

**Linear**:
```ephapax
let! conn = try_connect();
// Must handle error case explicitly
match conn {
    Ok(c) => use(c),
    Err(e) => drop(e)  // Must consume error too!
}
```

## FAQ

### Q: Can I mix affine and linear in one program?

**A**: Not yet, but planned! You'll be able to mark specific types/functions as linear within an affine program.

### Q: Which mode should I use by default?

**A**: Start with **affine** for development, switch to **linear** for production.

### Q: Is linear mode always better?

**A**: No! Affine is better for:
- Prototyping
- Scripts
- Code that exits quickly
- Teaching/learning

Linear is better for:
- Long-running processes
- Safety-critical systems
- Public APIs
- Resource-intensive code

### Q: How much boilerplate does linear add?

**A**: Typically 1-2 `drop()` calls per function. Worth it for leak prevention!

### Q: Can other languages do this?

**A**: Rust has affine types. Linear Haskell has linear types. **Ephapax is the first with both modes in one language**.

## Try It Yourself!

1. Load **30-comparison.eph** in the playground
2. Compile in **affine mode** - it works
3. Compile in **linear mode** - see the error
4. Fix the error by adding explicit drops
5. Now you understand the difference!

## Next Lesson

[03-regions-and-borrows.md](./03-regions-and-borrows.md) - Learn about Ephapax's region-based memory management

---

**Key Takeaway**: Affine = easy but may leak. Linear = strict but safe. Ephapax lets you choose per-project, or even migrate gradually. That's **dyadic design**.
