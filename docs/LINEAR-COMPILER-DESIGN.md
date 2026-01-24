# ephapax-linear Compiler Design

## Goal

Implement a linear type checker **in Ephapax itself** that can be compiled with the existing affine compiler, creating a bootstrap path to self-hosting.

## Architecture

```
┌─────────────┐
│ S-expr IR   │  (input: already parsed by affine stage)
└──────┬──────┘
       │
       v
┌─────────────┐
│  Decode IR  │  (parse S-expr to AST)
└──────┬──────┘
       │
       v
┌─────────────┐
│ Linear TC   │  (type check with linear rules)
└──────┬──────┘
       │
       v
┌─────────────┐
│  Emit IR    │  (output checked S-expr)
└──────┬──────┘
       │
       v
┌─────────────┐
│ WASM backend│  (Rust - existing)
└─────────────┘
```

## Input/Output Format

### Input: S-Expression IR

Same format as affine compiler emits:
```scheme
(module <name>
  ((fn <name> (<params>) <ret-ty> <body>)
   ...))
```

Example:
```scheme
(module input
  ((fn main () (base i32)
     (let x (binop add (lit (i32 1)) (lit (i32 2)))
       (let y (binop mul (var x) (lit (i32 3)))
         (block (var y)))))))
```

### Output: Checked S-Expression IR

Same format (validated):
```scheme
(module input
  ((fn main () (base i32)
     (let x (binop add (lit (i32 1)) (lit (i32 2)))
       (let y (binop mul (var x) (lit (i32 3)))
         (block (var y)))))))
```

## Core Data Structures

### 1. Types

```ephapax
type BaseTy {
    I32,
    I64,
    F32,
    F64,
    Bool,
    Unit,
    String
}

type Ty {
    Base(BaseTy),
    Fn(List<Ty>, Ty),        // function type
    Product(Ty, Ty),          // pairs
    Sum(Ty, Ty),              // either/or
    Region(String)            // region annotation
}
```

### 2. Expressions

```ephapax
type Expr {
    Lit(Literal),
    Var(String),
    Let(String, Expr, Expr),       // let x = e1 in e2
    LetLin(String, Expr, Expr),    // let! x = e1 in e2
    Fn(String, List<String>, Ty, Expr),
    App(Expr, List<Expr>),
    If(Expr, Expr, Expr),
    BinOp(BinOp, Expr, Expr),
    Block(List<Expr>),
    Drop(String)                    // explicit drop
}
```

### 3. Context

```ephapax
type Entry = {
    ty: Ty,
    linear: bool,      // is this a linear binding?
    consumed: bool     // has it been consumed?
}

type Context = List<(String, Entry)>
```

## Type Checking Algorithm

### Main Function

```ephapax
fn check_module(module: Module) -> Result<Module, TypeError> {
    // Check each function definition
    let! results = map(module.functions, check_function);

    // Collect errors
    match collect_errors(results) {
        Ok(checked_fns) => Ok(Module { functions: checked_fns }),
        Err(errors) => Err(errors)
    }
}
```

### Function Checking

```ephapax
fn check_function(func: Function) -> Result<Function, TypeError> {
    // Build initial context from parameters
    let! ctx = build_param_context(func.params);

    // Check function body
    let! (body_ty, out_ctx) = check_expr(ctx, func.body);

    // Verify all linear params consumed
    check_all_consumed(out_ctx)?;

    // Verify return type matches
    if body_ty != func.ret_ty {
        Err(TypeMismatch(func.ret_ty, body_ty))
    } else {
        Ok(func)
    }
}
```

### Expression Checking (Core Algorithm)

```ephapax
fn check_expr(ctx: Context, expr: Expr) -> Result<(Ty, Context), TypeError> {
    match expr {
        // Variable: mark as consumed
        Var(name) => {
            let entry = lookup(ctx, name)?;
            if entry.consumed {
                Err(LinearReused(name))
            } else {
                let new_ctx = mark_consumed(ctx, name);
                Ok((entry.ty, new_ctx))
            }
        }

        // Let binding: thread contexts
        Let(x, e1, e2) => {
            let! (ty1, ctx1) = check_expr(ctx, e1);
            let ctx2 = extend(ctx1, x, Entry {
                ty: ty1,
                linear: false,
                consumed: false
            });
            let! (ty2, ctx3) = check_expr(ctx2, e2);

            // Check if x was consumed
            let x_entry = lookup(ctx3, x)?;
            if !x_entry.consumed {
                // Warning for affine, but we allow it
            }

            let final_ctx = remove(ctx3, x);
            Ok((ty2, final_ctx))
        }

        // Linear let: MUST consume
        LetLin(x, e1, e2) => {
            let! (ty1, ctx1) = check_expr(ctx, e1);
            let ctx2 = extend(ctx1, x, Entry {
                ty: ty1,
                linear: true,
                consumed: false
            });
            let! (ty2, ctx3) = check_expr(ctx2, e2);

            // Check if x was consumed (REQUIRED)
            let x_entry = lookup(ctx3, x)?;
            if !x_entry.consumed {
                Err(LinearNotConsumed(x))
            }

            let final_ctx = remove(ctx3, x);
            Ok((ty2, final_ctx))
        }

        // If: both branches must consume same vars
        If(cond, then_br, else_br) => {
            let! (cond_ty, ctx1) = check_expr(ctx, cond);
            if cond_ty != Bool {
                Err(TypeMismatch(Bool, cond_ty))
            }

            // Check both branches from same context
            let! (then_ty, then_ctx) = check_expr(ctx1, then_br);
            let! (else_ty, else_ctx) = check_expr(ctx1, else_br);

            // Types must match
            if then_ty != else_ty {
                Err(TypeMismatch(then_ty, else_ty))
            }

            // Consumption must match
            check_branch_agreement(then_ctx, else_ctx)?;

            Ok((then_ty, then_ctx))
        }

        // Drop: explicit consumption
        Drop(x) => {
            let entry = lookup(ctx, x)?;
            if !entry.linear {
                Err(UnnecessaryDrop(x))  // Only drop linear values
            }
            if entry.consumed {
                Err(LinearReused(x))
            }

            let new_ctx = mark_consumed(ctx, x);
            Ok((Unit, new_ctx))
        }

        // Other cases: BinOp, App, Block, etc.
        // ...
    }
}
```

### Branch Agreement Checking

```ephapax
fn check_branch_agreement(then_ctx: Context, else_ctx: Context) -> Result<(), TypeError> {
    // For each linear variable in input context,
    // check that both branches consumed it the same way

    for (name, entry) in then_ctx {
        if entry.linear {
            let else_entry = lookup(else_ctx, name)?;
            if entry.consumed != else_entry.consumed {
                Err(BranchMismatch(
                    name,
                    if entry.consumed { "consumed" } else { "not consumed" },
                    if else_entry.consumed { "consumed" } else { "not consumed" }
                ))
            }
        }
    }

    Ok(())
}
```

## Compilation Strategy

### Phase 1: Minimal Viable Compiler

Implement just enough to type-check simple linear programs:

**Supported:**
- ✅ Variables
- ✅ Let bindings (regular and linear)
- ✅ Literals (i32, bool)
- ✅ Binary operations (+, -, *, /)
- ✅ If expressions
- ✅ Drop expressions
- ✅ Function definitions (single function)
- ✅ Basic context threading

**Not Yet:**
- ❌ Function calls
- ❌ Regions
- ❌ Products/sums
- ❌ Borrows
- ❌ Multiple modules

### Phase 2: Bootstrap

Once Phase 1 compiles:

```bash
# Compile minimal linear checker with affine
cd ~/Documents/hyperpolymath-repos/ephapax
idris2/build/exec/ephapax-affine examples/linear-minimal.eph \
    --mode affine --out /tmp/linear.sexpr

cargo run --release -p ephapax-cli -- compile-sexpr /tmp/linear.sexpr \
    -o /tmp/ephapax-linear.wasm

# Use it to check itself
wasmtime /tmp/ephapax-linear.wasm < /tmp/linear.sexpr > /tmp/linear-checked.sexpr
```

### Phase 3: Full Linear Compiler

Add remaining features:
- Function calls with disjoint contexts
- Product/sum types
- Regions and borrows
- Multi-module support

### Phase 4: Self-Hosting

Recompile ephapax-linear with itself:

```bash
# linear compiles linear
wasmtime ephapax-linear.wasm < linear.sexpr > linear-v2.sexpr
cargo run -p ephapax-cli -- compile-sexpr linear-v2.sexpr -o linear-v2.wasm

# Verify: v2 should be identical or better
diff <(wasmtime linear.wasm < test.sexpr) \
     <(wasmtime linear-v2.wasm < test.sexpr)
```

## Testing Strategy

### Unit Tests (Rust)

Test the Rust components:
- S-expr parser
- AST validation
- Basic type checking

### Integration Tests (Ephapax)

Write `.eph` test files:

**Should Pass:**
```ephapax
// linear-pass-001-basic.eph
fn test() -> i32 {
    let! x = 42;
    drop(x);
    0
}
```

**Should Fail:**
```ephapax
// linear-fail-001-not-consumed.eph
fn test() -> i32 {
    let! x = 42;
    // ERROR: x not consumed
    0
}
```

### Conformance Suite

Located: `conformance/linear/`
- `pass/*.eph` - must type-check
- `fail/*.eph` - must reject with error

## Implementation Timeline

1. ✅ **Design linear semantics** (this document)
2. **Write minimal S-expr parser** in Ephapax
3. **Implement context threading** for simple exprs
4. **Add linear let checking**
5. **Add if branch agreement**
6. **Add drop checking**
7. **Test with hello.eph variant**
8. **Compile with affine → get linear.wasm**
9. **Verify linear.wasm works**
10. **Iterate to full feature coverage**

## Bootstrap Success Criteria

The bootstrap is successful when:

1. ✅ `ephapax-affine` compiles `ephapax-linear.eph`
2. ✅ `ephapax-linear.wasm` correctly type-checks linear programs
3. ✅ `ephapax-linear.wasm` rejects invalid linear programs
4. ✅ `ephapax-linear.wasm` can recompile itself
5. ✅ Test suite passes (conformance/linear/)

## Next Steps

Start with Phase 1: Write `examples/linear-minimal.eph` with:
- S-expr parser
- Basic AST
- Simple linear context threading
- Minimal type checker (just let! and drop)

Once that compiles and runs, expand incrementally.
