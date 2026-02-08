# What is Ephapax?

**Ephapax** (Greek: ἐφάπαξ, "once for all") is a programming language with **linear and affine type systems** designed to prevent memory leaks and use-after-free errors at compile time.

## The Core Idea

Traditional languages either:
- Use **garbage collection** (slow, unpredictable)
- Require **manual memory management** (error-prone)

Ephapax uses **linear types** to guarantee:
- Every resource is used **exactly once**
- No memory leaks (values must be consumed)
- No use-after-free (values can't be reused)
- **Zero runtime overhead** (all checks at compile time)

## What Makes Ephapax Unique?

### 1. Dyadic Design: Two Modes, One Language

Ephapax is the first language with **dyadic design** - it has TWO type system modes:

| Mode | Resource Usage | When to Use |
|------|----------------|-------------|
| **Affine** | At most once | Prototyping, scripting, rapid development |
| **Linear** | Exactly once | Production, embedded, safety-critical |

**You can switch between modes with a single flag!**

```ephapax
// Affine mode (permissive)
fn prototype() -> i32 {
    let x = expensive_resource();
    // x implicitly dropped - OK for prototyping
    0
}

// Linear mode (strict)
fn production() -> i32 {
    let! x = expensive_resource();
    drop(x);  // Must explicitly consume - enforces safety
    0
}
```

### 2. Gradual Migration Path

Unlike languages where you're stuck with one type system:
1. **Prototype** in affine mode (fast iteration)
2. **Test** and refine your logic
3. **Switch** to linear mode
4. **Fix** any resource leaks the compiler finds
5. **Ship** with strong safety guarantees

This is like **gradual typing** for resource management!

### 3. Educational Value

Ephapax lets you **see the difference** between type systems:
- Same code, different mode → different behavior
- Learn why strict type systems matter
- Understand the tradeoffs

### 4. WebAssembly Target

Ephapax compiles to **WebAssembly**:
- Runs in browsers
- Runs on servers
- Portable across platforms
- Small binaries (~500 bytes for "Hello World")

### 5. Formally Verified

The type systems are **mechanically verified in Coq**:
- Soundness proven
- Progress proven
- Preservation proven
- **You can trust the guarantees**

## Key Concepts

### Linear Types

```ephapax
fn linear_example() -> i32 {
    let! x = allocate(42);  // ! = linear
    // ERROR: x not consumed
}
```

**Linear types must be used exactly once.**

### Affine Types

```ephapax
fn affine_example() -> i32 {
    let x = allocate(42);
    // OK: x implicitly dropped
}
```

**Affine types can be used at most once.**

### Explicit Consumption

```ephapax
fn correct_linear() -> i32 {
    let! x = allocate(42);
    drop(x);  // Explicit consumption
    0         // Now OK!
}
```

### Region-Based Memory

```ephapax
fn with_region() -> i32 {
    region r:
        let buffer = allocate@r(1024);
        let result = process(buffer);
        result  // buffer deallocated here
}
```

## Why "Ephapax"?

The name comes from Greek **ἐφάπαξ** (ephapax):
- Meaning: "once for all", "once and for all time"
- Perfect metaphor for **linear types** (use exactly once)
- Also: **hapax legomenon** (word that appears once in a corpus)

## Comparison to Other Languages

| Language | Memory Safety | Leak Prevention | Ease of Use |
|----------|---------------|-----------------|-------------|
| C/C++ | ❌ Manual | ❌ No | ⚠️ Hard |
| Rust | ✅ Borrow checker | ✅ Mostly | ⚠️ Steep learning curve |
| Go/Java | ✅ GC | ❌ No (GC leaks) | ✅ Easy |
| **Ephapax** | ✅ Linear/Affine | ✅ Yes (linear mode) | ✅ Gradual adoption |

## Use Cases

### Where Ephapax Shines

1. **Embedded Systems** - Predictable cleanup, no GC
2. **Network Servers** - Guaranteed connection cleanup
3. **Resource Managers** - File handles, sockets, locks
4. **WebAssembly Modules** - Small, safe, fast
5. **Teaching** - Learn linear types interactively

### Where to Use Each Mode

**Affine Mode**:
- Scripts and tools
- Prototyping new features
- Test suites
- Internal utilities

**Linear Mode**:
- Production servers
- Safety-critical systems
- Public APIs and libraries
- Code that manages resources

## Try It Yourself!

The examples in this playground demonstrate:
- **01-hello-world**: Basic syntax
- **10-affine-drop**: Implicit drops in affine mode
- **20-linear-demo**: Linear type checking internals
- **21-linear-explicit**: Correct linear code
- **30-comparison**: Same code, different modes
- **40-connection-linear**: Real-world connection management
- **41-connection-leak**: How linear mode catches leaks
- **50-regions**: Region-based memory management

**Toggle between affine and linear modes** to see how the type checker behaves differently!

## Next Steps

1. Try the examples in both modes
2. Write your own code
3. See how linear types catch bugs
4. Read the [paper](../docs/dyadic-design-paper.pdf) on dyadic design
5. Join the community!

---

**Ephapax**: Once-for-all resource management. Zero runtime cost. Compile-time guarantees.
