# Ephapax Playground Examples

These examples demonstrate the **unique features of Ephapax**, particularly the dyadic design methodology with affine and linear type modes.

## Quick Start Guide

1. **Select an example** from the sidebar
2. **Toggle between Affine and Linear modes** at the top
3. **Click "Compile"** to see the result
4. **Read the comments** in each example to understand what's happening
5. **Try modifying** the code and recompiling!

## Example Categories

### Basics (01-0x)

Learn the fundamentals of Ephapax syntax and semantics.

#### 01-hello-world.eph
- **Description**: Classic "Hello World" - returns 42
- **Concepts**: Function definitions, return values
- **Works in**: Both affine and linear modes
- **Complexity**: Beginner

**What you'll learn**: Basic Ephapax syntax.

### Affine Mode (10-1x)

Explore affine types - variables used **at most once**.

#### 10-affine-drop.eph
- **Description**: Demonstrates implicit drops
- **Concepts**: Weakening rule, implicit resource cleanup
- **Works in**: Affine mode ✅ | Linear mode ❌ (error!)
- **Complexity**: Beginner

**What you'll learn**: Affine mode allows unused variables to be dropped implicitly. This is convenient but can cause resource leaks.

**Try this**:
1. Compile in affine mode → succeeds
2. Switch to linear mode → fails with "variable not consumed" error

### Linear Mode (20-2x)

Understand linear types - variables used **exactly once**.

#### 20-linear-demo.eph
- **Description**: Internal validation of linear type rules
- **Concepts**: Exact-once checking, no weakening
- **Works in**: Both modes (validates 4 core rules)
- **Complexity**: Advanced

**What you'll learn**: How linear type checking works internally. This example encodes boolean logic as integer arithmetic to implement 4 core linear type properties.

**What it validates**:
1. Affine can drop (test1 = 0)
2. Linear must consume (test2 = 1)
3. Affine allows drop with explicit use (test3 = 0)
4. Linear requires explicit drop (test4 = 1)

#### 21-linear-explicit.eph
- **Description**: Correct linear code with explicit consumption
- **Concepts**: `drop()` function, explicit resource management
- **Works in**: Both modes ✅
- **Complexity**: Beginner

**What you'll learn**: How to write correct linear code by explicitly consuming every variable. This pattern works in both affine and linear modes.

**Key pattern**:
```ephapax
let! x = value();
drop(x);  // Explicit consumption
```

### Comparison & Migration (30-3x)

See affine and linear side-by-side to understand the tradeoffs.

#### 30-comparison.eph ⭐ **START HERE**
- **Description**: Same code, different behavior in each mode
- **Concepts**: Dyadic design, gradual adoption
- **Works in**: Affine ✅ | Linear ❌ (shows difference!)
- **Complexity**: Beginner

**What you'll learn**: The core value proposition of Ephapax - you can prototype in affine mode (permissive) and migrate to linear mode (strict) when ready for production.

**The pattern**:
1. Write code quickly in affine mode
2. Test and iterate
3. Switch to linear mode
4. Fix any resource leaks the compiler finds
5. Deploy with strong guarantees

**This is dyadic design in action!**

### Real-World Applications (40-5x)

See how linear types solve actual problems.

#### 40-connection-linear.eph
- **Description**: HTTP connection lifecycle with guaranteed cleanup
- **Concepts**: Resource management, connection pooling
- **Works in**: Both modes (demonstrates best practices)
- **Complexity**: Intermediate

**What you'll learn**: How linear types guarantee that connections are always closed, preventing file descriptor leaks in long-running servers.

**Real-world impact**: Prevents production incidents caused by connection leaks.

#### 41-connection-leak.eph
- **Description**: Common bug - connection never closed
- **Concepts**: Resource leaks, type system catching bugs
- **Works in**: Affine ✅ (LEAKS!) | Linear ❌ (catches bug!)
- **Complexity**: Intermediate

**What you'll learn**: Linear mode catches resource leaks that affine mode allows. This is the **killer feature** of linear types.

**The bug**:
```ephapax
let conn = open_connection();
read_data(conn);
// BUG: Never closed!
// Affine: Compiles (leaks)
// Linear: Type error (catches bug)
```

#### 50-regions.eph
- **Description**: Region-based memory management
- **Concepts**: Regions, scoped allocation, bulk deallocation
- **Works in**: Both modes
- **Complexity**: Advanced

**What you'll learn**: Ephapax's region system allows efficient bulk allocation and deallocation without garbage collection.

**Why regions?**:
- Allocate many objects cheaply
- Deallocate all at once when region ends
- No GC pauses
- Predictable performance

## Learning Path

### For Beginners (30 minutes)

1. **01-hello-world.eph** - Get comfortable with syntax (5 min)
2. **30-comparison.eph** - Understand affine vs linear (10 min)
3. **10-affine-drop.eph** - See implicit drops (5 min)
4. **21-linear-explicit.eph** - Learn explicit consumption (10 min)

### For Intermediate Users (1 hour)

1. Complete beginner path above
2. **41-connection-leak.eph** - See real-world leak caught (15 min)
3. **40-connection-linear.eph** - Best practices (15 min)
4. **20-linear-demo.eph** - Understand internals (15 min)

### For Advanced Users (2 hours)

1. Complete intermediate path above
2. **50-regions.eph** - Advanced memory management (30 min)
3. Write your own examples
4. Try building a small HTTP server
5. Read the [dyadic design paper](../docs/dyadic-design-paper.pdf)

## What Makes These Examples Unique?

### 1. Dyadic Design Demonstration

**No other language** lets you toggle between type system strictness like this:
- Same code
- Different mode
- Different behavior

**Try it**: Load **30-comparison.eph** and toggle between modes!

### 2. Educational Focus

Each example teaches **one concept** clearly:
- Extensive comments
- Clear error messages
- Recommended next steps

### 3. Real-World Relevance

Examples aren't just toys:
- **41-connection-leak.eph** - Actual bug pattern from production
- **40-connection-linear.eph** - Server code template
- **50-regions.eph** - Performance optimization technique

### 4. Progressive Complexity

Start simple (**01-hello-world**), build to advanced (**50-regions**), with clear learning path.

## Common Patterns You'll Learn

### Pattern 1: Resource Acquisition Is Initialization (RAII)

```ephapax
fn with_resource() -> Result {
    let! resource = acquire();
    let result = use_resource(&resource);
    resource.release();
    Ok(result)
}
```

Linear types guarantee the `release()` call happens.

### Pattern 2: Builder Pattern with Linear Types

```ephapax
fn build_config() -> Config {
    let! builder = ConfigBuilder::new();
    let! builder2 = builder.set_host("localhost");
    let! builder3 = builder2.set_port(8080);
    builder3.build()
}
```

Each step consumes the previous builder, preventing reuse.

### Pattern 3: Error Handling

```ephapax
fn try_operation() -> Result {
    let! resource = try_acquire();
    match resource {
        Ok(r) => {
            let result = use(r);
            r.close();
            Ok(result)
        },
        Err(e) => Err(e)
    }
}
```

Both success and error paths must consume all variables.

## Tips for Writing Ephapax Code

### Start Affine, Migrate Linear

1. Write in affine mode first (fast iteration)
2. Get logic working
3. Switch to linear mode
4. Fix "not consumed" errors
5. Ship with guarantees

### Use Borrows When Possible

```ephapax
// Don't consume if you don't need to
fn inspect(resource: &Resource) -> Info {
    resource.get_info()  // Borrow, don't consume
}

let! r = acquire();
let info = inspect(&r);
r.close();  // Can still close
```

### Explicit is Better Than Implicit

Linear mode requires explicit cleanup:
```ephapax
drop(x);        // Clear intent
x.close();      // Clear action
x.deallocate(); // Clear cleanup
```

This is **good** - it makes resource management visible!

## Troubleshooting

### Error: "Variable not consumed"

**In affine mode**: This shouldn't happen (affine allows drops).

**In linear mode**: Add explicit consumption:
```ephapax
let! x = value();
drop(x);  // or use(x) or x.cleanup()
```

### Error: "Variable used multiple times"

You're trying to use a value twice:
```ephapax
let x = value();
use(x);
use(x);  // ERROR: x already consumed
```

**Fix**: Use borrows:
```ephapax
let x = value();
use(&x);  // Borrow
use(&x);  // Borrow again - OK!
drop(x);  // Finally consume
```

### Error: "Type mismatch"

Check that you're calling functions with correct types. Ephapax has no implicit conversions.

## Next Steps

1. **Try all examples** in both modes
2. **Modify examples** and see what happens
3. **Read the lessons** in the `lessons/` directory
4. **Write your own code** in the editor
5. **Share your programs** using the share button
6. **Read the paper** on dyadic design

## Resources

- [Lesson 1: What is Ephapax?](../lessons/01-what-is-ephapax.md)
- [Lesson 2: Linear vs Affine](../lessons/02-linear-vs-affine.md)
- [Paper: Dyadic Language Design](../docs/dyadic-design-paper.pdf)
- [HTTP Server Tutorial](../lessons/04-building-http-server.md)

## Contributing Examples

Have a great example? Submit a PR!

**Good examples**:
- Teach one concept clearly
- Include extensive comments
- Show affine vs linear difference
- Solve a real-world problem

---

**Remember**: The power of Ephapax is **choice**. Affine for prototyping, linear for production. That's dyadic design!
