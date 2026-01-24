# Ephapax Bootstrap Status & Plan

**Date**: 2026-01-23
**Current Phase**: Affine Complete ✅ → Linear Implementation

## Current State

### ✅ Affine Compiler (100% Working)

**Location**: `idris2/src/Ephapax/Affine/`
**Binary**: `idris2/build/exec/ephapax-affine`

**Capabilities**:
- ✅ Parse Ephapax surface syntax
- ✅ Parse S-expression IR
- ✅ Type check in affine mode (≤1 use)
- ✅ Type check in linear mode (partial - see below)
- ✅ Emit S-expression IR
- ✅ End-to-end compilation to WASM

**Verified Working**:
```bash
# Compile hello.eph
idris2/build/exec/ephapax-affine examples/hello.eph \
    --mode affine --out /tmp/hello.sexpr

# Generate WASM
cargo run --release -p ephapax-cli -- compile-sexpr /tmp/hello.sexpr \
    -o /tmp/hello.wasm

# Result: 530 byte WASM binary ✅
```

### 🚧 Linear Mode (Partially Implemented)

**What Works**:
- ✅ Linear variable tracking (`let!`)
- ✅ Usage detection (marks variables as used)
- ✅ Basic consumption checking (`checkBoundUsed`)
- ✅ Branch merge logic (`mergeLinear`)
- ✅ Pair projection checking (Fst/Snd with linear components)

**What's Missing**:
- ❌ Explicit drop checking
- ❌ Comprehensive branch agreement enforcement
- ❌ Region escape prevention
- ❌ Full linear closure checking
- ❌ Error messages specific to linear violations

**Code Evidence** (`Affine/Typecheck.idr:102-110`):
```idris
checkBoundUsed : Mode -> String -> List Entry -> Either TypeError Builtin.Unit
checkBoundUsed Affine _ _ = Right ()
checkBoundUsed Linear name vars =
  case lookupVar name vars of
    Just entry =>
      if isLinear entry.ty && not entry.used
        then Left (LinearNotConsumed name)
        else Right ()
    Nothing => Right ()
```

This shows linear mode DOES enforce consumption, but not as strictly as the full linear semantics require.

## Bootstrap Path

### Phase 1: Demonstrate Affine→Linear Compilation ✅ (Current)

**Goal**: Prove affine can compile code that will become the linear compiler

**Status**: ✅ PROVEN
- Affine compiler works end-to-end
- Can compile both `--mode affine` and `--mode linear`
- Generates valid WASM

**Example**:
```bash
# Both modes work
ephapax-affine input.eph --mode affine --out affine.sexpr
ephapax-affine input.eph --mode linear --out linear.sexpr

# Both produce WASM
ephapax-cli compile-sexpr affine.sexpr -o affine.wasm
ephapax-cli compile-sexpr linear.sexpr -o linear.wasm
```

### Phase 2: Write Linear Compiler in Ephapax (In Progress)

**Goal**: Implement a stricter linear type checker in Ephapax itself

**Approach**: TWO OPTIONS

#### Option A: Enhance Current Idris2 Implementation
Pros:
- ✅ Faster (already 60% done)
- ✅ Can iterate quickly in Idris2
- ✅ Proven infrastructure

Cons:
- ❌ Not self-hosting yet
- ❌ Still depends on Idris2

**Next Steps**:
1. Add explicit `drop()` syntax to surface grammar
2. Implement `check_drop` in typecheck
3. Strengthen branch agreement checking
4. Add linear-specific error messages
5. Test with linear conformance suite

#### Option B: Write New Linear Checker in Ephapax (Self-Hosting Path)
Pros:
- ✅ Demonstrates self-hosting
- ✅ Pure Ephapax codebase
- ✅ Shows affine→linear bootstrap

Cons:
- ❌ More work (need to implement S-expr parser, etc.)
- ❌ Limited by current Ephapax features

**Next Steps**:
1. Write S-expr parser in Ephapax
2. Implement linear type checker
3. Compile with affine: `ephapax-affine linear-checker.eph → linear.wasm`
4. Use for validation: `wasmtime linear.wasm < program.sexpr`

### Phase 3: Complete Linear Implementation

**Deliverable**: Fully working linear type checker

**Requirements**:
- ✅ Enforce exact-once consumption
- ✅ Require explicit `drop()`
- ✅ Strict branch agreement
- ✅ Region escape prevention
- ✅ Clear error messages
- ✅ Pass all linear conformance tests

**Location** (depending on approach):
- Option A: `idris2/src/Ephapax/Linear/Typecheck.idr`
- Option B: `examples/ephapax-linear.eph`

### Phase 4: Self-Hosting Bootstrap

**Goal**: Use linear compiler to rebuild itself

```
┌─────────────────┐
│ ephapax-affine  │ (Idris2, trusted base)
└────────┬────────┘
         │
         v  compiles
┌─────────────────┐
│ephapax-linear.eph│ (Ephapax source)
└────────┬────────┘
         │
         v  produces
┌─────────────────┐
│ linear-v1.wasm  │ (WASM binary)
└────────┬────────┘
         │
         v  recompiles itself
┌─────────────────┐
│ linear-v2.wasm  │ (Self-hosted!)
└─────────────────┘
```

**Verification**:
```bash
# v1 and v2 should produce identical output
diff <(wasmtime linear-v1.wasm < test.sexpr) \
     <(wasmtime linear-v2.wasm < test.sexpr)
```

### Phase 5: Remake Affine with Linear

**Goal**: Use linear compiler to rebuild affine compiler

```
┌─────────────────┐
│ linear-v2.wasm  │ (Self-hosted linear)
└────────┬────────┘
         │
         v  compiles
┌─────────────────┐
│ephapax-affine.eph│ (Ephapax source, rewritten)
└────────┬────────┘
         │
         v  produces
┌─────────────────┐
│affine-v2.wasm   │ (New affine in WASM)
└─────────────────┘
```

**Deliverables**:
1. Write `ephapax-affine.eph` (affine checker in Ephapax)
2. Compile with linear: `linear.wasm → affine-v2.wasm`
3. Verify: both affine compilers produce same output

## Recommended Next Steps

### Immediate (This Week)

1. **Decide on Approach**: Option A (enhance Idris2) or Option B (write in Ephapax)

2. **If Option A**:
   - Add `drop()` syntax to parser
   - Implement drop checking in typecheck
   - Write linear conformance tests
   - Strengthen enforcement

3. **If Option B**:
   - Design simplified S-expr format for MVP
   - Write minimal S-expr parser in Ephapax
   - Implement context threading
   - Compile with affine, test

### Medium Term (This Month)

1. Complete linear type checker (whichever approach)
2. Build comprehensive test suite
3. Verify against formal semantics (Coq proofs)
4. Document differences from affine

### Long Term (This Quarter)

1. Self-hosting bootstrap (Phase 4)
2. Remake affine with linear (Phase 5)
3. Merge improvements back to Idris2 implementation
4. Publish paper on bootstrap methodology

## Key Insights

### Why Affine First?

Affine is **more permissive** than linear:
- Affine: ≤1 use (can drop)
- Linear: =1 use (must consume)

This means:
- ✅ Affine code is **easier to write** (less strict)
- ✅ Affine compiler is **easier to prototype**
- ✅ Affine can **compile linear** (by being stricter)
- ✅ Bootstrap path is **natural**: permissive → strict

### The Bootstrap Value

This demonstrates:
1. **Gradual strengthening**: Start permissive, add strictness
2. **Meta-circular compilation**: Compilers compiling compilers
3. **Type system as tool**: Affine for prototyping, linear for production
4. **Practical formalism**: Coq proofs guide implementation

### Applications

Once both compilers are self-hosted:
- ✅ Affine: Fast prototyping, framework code
- ✅ Linear: Production systems, safety-critical
- ✅ Mixed: Use both in same codebase (gradual migration)
- ✅ Teaching: Show type system progression

## Current Files

```
ephapax/
├── idris2/
│   ├── src/Ephapax/Affine/
│   │   ├── Typecheck.idr      ✅ Working (affine + partial linear)
│   │   └── Emit.idr            ✅ Working
│   └── build/exec/
│       └── ephapax-affine      ✅ Binary (2.7MB)
├── src/
│   ├── ephapax-cli/            ✅ Rust WASM backend
│   ├── ephapax-wasm/           ✅ Code generation
│   └── ephapax-ir/             ✅ S-expr handling
├── examples/
│   ├── hello.eph               ✅ Working example
│   ├── linear-simple.eph       ✅ Minimal test
│   └── linear-minimal.eph      🚧 Complex (parser issues)
└── docs/
    ├── LINEAR-SEMANTICS.md     ✅ Formal specification
    ├── LINEAR-COMPILER-DESIGN.md ✅ Implementation plan
    └── BOOTSTRAP-STATUS.md     ✅ This file
```

## Success Metrics

### Phase 1 ✅ (Complete)
- [x] Affine compiler works end-to-end
- [x] Produces valid WASM
- [x] Has partial linear support

### Phase 2 🚧 (In Progress)
- [ ] Decide approach (A or B)
- [ ] Implement linear checker
- [ ] Pass conformance tests
- [ ] Generate WASM

### Phase 3 ⏳ (Planned)
- [ ] Full linear semantics
- [ ] Comprehensive test suite
- [ ] Formal verification

### Phase 4 ⏳ (Planned)
- [ ] Self-hosting bootstrap
- [ ] v1 == v2 verification
- [ ] Performance benchmarks

### Phase 5 ⏳ (Planned)
- [ ] Affine in Ephapax
- [ ] Compiled with linear
- [ ] Feature parity with Idris2 version

## References

- **Formal Semantics**: `docs/LINEAR-SEMANTICS.md`
- **Implementation Design**: `docs/LINEAR-COMPILER-DESIGN.md`
- **Current Implementation**: `idris2/src/Ephapax/Affine/Typecheck.idr`
- **State Tracking**: `STATE.scm`
- **Milestones**: `MILESTONES.md`
- **Roadmap**: `ROADMAP.adoc`
