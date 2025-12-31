# Compiler Correctness for Ephapax

## Verified Compilation to WebAssembly

**Version**: 1.0.0
**Date**: 2025-12-31
**SPDX-License-Identifier**: EUPL-1.2

---

## Abstract

We develop a framework for proving the correctness of the Ephapax compiler. We establish a semantic preservation theorem: compiled programs exhibit the same observable behavior as their source-level semantics. This document provides the theoretical foundation and proof obligations for verified compilation.

---

## 1. Introduction

Compiler correctness ensures that the compiled program faithfully represents the source program's meaning. For Ephapax, this means:

1. **Type safety is preserved**: Well-typed source yields safe WASM
2. **Memory safety is preserved**: No use-after-free, double-free, or leaks in WASM
3. **Functional correctness**: Observable behavior matches source semantics

---

## 2. Compilation Phases

### 2.1 Compiler Pipeline

```
Source → Lexer → Parser → Type Checker → IR → Optimizer → WASM Emitter → WASM
         (1)     (2)         (3)        (4)      (5)          (6)
```

Each phase must preserve semantics:
- (1) Lexer: Characters → Tokens
- (2) Parser: Tokens → AST
- (3) Type Checker: AST → Typed AST (+ type errors)
- (4) IR: Typed AST → Intermediate Representation
- (5) Optimizer: IR → Optimized IR (optional)
- (6) WASM Emitter: IR → WebAssembly bytecode

### 2.2 Correctness Strategy

We prove correctness compositionally:
```
⟦source⟧_S = ⟦compile(source)⟧_W
```

Where:
- ⟦−⟧_S is source-level semantics
- ⟦−⟧_W is WASM-level semantics
- compile is the full compilation function

---

## 3. Source Semantics

### 3.1 Big-Step Semantics

For simplicity, we use big-step (natural) semantics:

```
⟨H, R, E, e⟩ ⇓ ⟨H', v⟩
```

Read: Under heap H, regions R, environment E, expression e evaluates to value v with new heap H'.

**Selected Rules**:

**Unit**:
```
─────────────────────────
⟨H, R, E, ()⟩ ⇓ ⟨H, ()⟩
```

**Variable**:
```
E(x) = v
────────────────────────
⟨H, R, E, x⟩ ⇓ ⟨H, v⟩
```

**Application**:
```
⟨H, R, E, e₁⟩ ⇓ ⟨H₁, ⟨λx.body, E'⟩⟩
⟨H₁, R, E, e₂⟩ ⇓ ⟨H₂, v₂⟩
⟨H₂, R, E'[x↦v₂], body⟩ ⇓ ⟨H₃, v₃⟩
──────────────────────────────────────
⟨H, R, E, e₁ e₂⟩ ⇓ ⟨H₃, v₃⟩
```

**String Allocation**:
```
ℓ = fresh(H)
H' = H[ℓ ↦ (s, r)]
r ∈ R
──────────────────────────────────────
⟨H, R, E, String.new@r(s)⟩ ⇓ ⟨H', ℓ⟩
```

**Region**:
```
⟨H, R ∪ {r}, E, e⟩ ⇓ ⟨H', v⟩
H'' = free_region(H', r)
─────────────────────────────────────
⟨H, R, E, region r { e }⟩ ⇓ ⟨H'', v⟩
```

### 3.2 Observable Behavior

**Definition 3.1** (Observable Behavior):
The observable behavior of a program is:
- Termination status (value, divergence, or error)
- Return value (if terminating)
- External I/O actions (if any)

---

## 4. Target Semantics (WASM)

### 4.1 WASM Execution Model

WASM has a stack-based execution model:

```
⟨S, F, instr*⟩ →_W ⟨S', F', instr*'⟩
```

Where:
- S = store (memories, globals, tables)
- F = frame (locals, module instance)
- instr* = instruction sequence

### 4.2 Key WASM Instructions

| Instruction | Effect |
|-------------|--------|
| `i32.const n` | Push n onto stack |
| `local.get $x` | Push local x onto stack |
| `local.set $x` | Pop and store in local x |
| `call $f` | Call function f |
| `i32.load` | Load from memory |
| `i32.store` | Store to memory |
| `block ... end` | Structured control |

### 4.3 WASM Memory Model

WASM linear memory:
```
Memory = Addr → Byte
Addr = 0, 1, 2, ...
```

Ephapax maps to this:
- Bump pointer at offset 0
- Region stack at offset 4
- Heap at offset 0x108

---

## 5. Compilation Functions

### 5.1 Type Compilation

```
compileType : EphapaxType → WASMType

compileType(Unit) = ()  (no representation)
compileType(Bool) = i32
compileType(I32) = i32
compileType(I64) = i64
compileType(F32) = f32
compileType(F64) = f64
compileType(String@r) = i32  (pointer)
compileType(T₁ × T₂) = i32  (pointer to struct)
compileType(T₁ + T₂) = i32  (pointer to tagged union)
compileType(T₁ → T₂) = i32  (function index)
compileType(&T) = i32  (pointer)
```

### 5.2 Expression Compilation

```
compileExpr : TypedExpr → WASMInstr*

compileExpr(EUnit) = []  (no code needed)

compileExpr(EBool true) = [i32.const 1]
compileExpr(EBool false) = [i32.const 0]

compileExpr(EI32 n) = [i32.const n]

compileExpr(EVar x) = [local.get $x]

compileExpr(EStringNew r s) =
  [i32.const (len s)]
  [call $bump_alloc]
  [local.tee $ptr]
  [i32.const (data_offset s)]
  [i32.const (len s)]
  [memory.copy]
  [local.get $ptr]

compileExpr(ELet x e₁ e₂) =
  compileExpr(e₁) ++
  [local.set $x] ++
  compileExpr(e₂)

compileExpr(ELam x T body) =
  // Generate closure
  [i32.const $closure_func_idx]

compileExpr(EApp e₁ e₂) =
  compileExpr(e₂) ++
  compileExpr(e₁) ++
  [call_indirect]

compileExpr(EPair e₁ e₂) =
  [i32.const 8]
  [call $bump_alloc]
  [local.tee $ptr]
  compileExpr(e₁) ++
  [i32.store offset=0] ++
  [local.get $ptr] ++
  compileExpr(e₂) ++
  [i32.store offset=4] ++
  [local.get $ptr]

compileExpr(ERegion r e) =
  [call $region_enter] ++
  compileExpr(e) ++
  [call $region_exit]

compileExpr(EDrop e) =
  compileExpr(e) ++
  [drop]  // WASM drop (or explicit free if needed)
```

### 5.3 Runtime Functions

```wasm
(func $bump_alloc (param $size i32) (result i32)
  (local $ptr i32)
  (local.set $ptr (i32.load (i32.const 0)))  ;; Load bump ptr
  (i32.store (i32.const 0)                   ;; Update bump ptr
    (i32.add (local.get $ptr) (local.get $size)))
  (local.get $ptr))                          ;; Return old ptr

(func $region_enter (result i32)
  (local $bump i32)
  (local $sp i32)
  (local.set $bump (i32.load (i32.const 0)))
  (local.set $sp (i32.load (i32.const 4)))
  (i32.store (i32.add (i32.const 8) (i32.mul (local.get $sp) (i32.const 4)))
             (local.get $bump))              ;; Push bump ptr
  (i32.store (i32.const 4)
             (i32.add (local.get $sp) (i32.const 1)))  ;; Increment SP
  (local.get $sp))

(func $region_exit
  (local $sp i32)
  (local.set $sp (i32.sub (i32.load (i32.const 4)) (i32.const 1)))
  (i32.store (i32.const 4) (local.get $sp))  ;; Decrement SP
  (i32.store (i32.const 0)                   ;; Restore bump ptr
    (i32.load (i32.add (i32.const 8) (i32.mul (local.get $sp) (i32.const 4))))))
```

---

## 6. Correctness Theorem

### 6.1 Simulation Relation

**Definition 6.1** (Simulation Relation):
Define a relation ≈ between source and target states:

```
(H, E) ≈ (S, F)
```

When:
1. Source heap H corresponds to WASM memory S.mem
2. Source environment E corresponds to WASM locals F.locals
3. All invariants (bump pointer, region stack) are maintained

### 6.2 Value Correspondence

**Definition 6.2** (Value Correspondence):
```
v_S ≈_T v_W

()       ≈_Unit    (any)
true     ≈_Bool    1
false    ≈_Bool    0
n        ≈_I32     n
ℓ        ≈_String  ptr  (where H(ℓ) corresponds to S.mem[ptr..])
(v₁,v₂)  ≈_{T₁×T₂} ptr  (where ptr points to compiled pair)
inl(v)   ≈_{T₁+T₂} ptr  (where ptr points to tagged 0 + v)
inr(v)   ≈_{T₁+T₂} ptr  (where ptr points to tagged 1 + v)
⟨λx.e,E⟩ ≈_{T→U}   idx  (function index in WASM table)
```

### 6.3 Main Theorem

**Theorem 6.1** (Compiler Correctness):
For all well-typed expressions e with `⊢ e : T`:

If `⟨H, R, E, e⟩ ⇓ ⟨H', v⟩` (source evaluates to v)

and `(H, E) ≈ (S, F)` (initial states correspond)

then `⟨S, F, compile(e)⟩ →*_W ⟨S', F', v_W::stack⟩`

where `v ≈_T v_W` and `(H', E) ≈ (S', F')`.

### 6.4 Proof Strategy

**Proof** (sketch):
By structural induction on the source evaluation derivation.

**Case EUnit**:
- Source: `⟨H, R, E, ()⟩ ⇓ ⟨H, ()⟩`
- Target: `compile(()) = []` (no instructions)
- The empty sequence produces no value, which is correct for Unit.
- Relation preserved trivially.

**Case EI32 n**:
- Source: `⟨H, R, E, n⟩ ⇓ ⟨H, n⟩`
- Target: `compile(n) = [i32.const n]` pushes n onto stack
- n ≈_I32 n by definition
- Relation preserved.

**Case EVar x**:
- Source: `⟨H, R, E, x⟩ ⇓ ⟨H, E(x)⟩`
- Target: `compile(x) = [local.get $x]` pushes F.locals(x)
- By (H, E) ≈ (S, F), E(x) ≈ F.locals(x)
- Relation preserved.

**Case ELet x e₁ e₂**:
- By IH on e₁: compiling e₁ produces v₁_W with v₁ ≈ v₁_W
- After `local.set $x`: v₁_W stored in local x
- By IH on e₂: compiling e₂ in updated context produces result
- Relation preserved.

**Case EApp**:
- By IH on e₁: produces closure index
- By IH on e₂: produces argument
- `call_indirect` invokes the closure with argument
- By IH on closure body: produces correct result
- Relation preserved.

**Case ERegion**:
- `region_enter` saves bump pointer
- By IH on body: produces value
- `region_exit` restores bump pointer (freeing region memory)
- This corresponds to source `free_region(H', r)`
- Relation preserved.

Full proof requires ~500 lines of detailed case analysis. □

---

## 7. Memory Layout Correctness

### 7.1 Heap Correspondence

**Definition 7.1** (Heap Correspondence):
```
H ≈_heap M iff
  ∀ℓ ∈ dom(H). ∃offset.
    H(ℓ) = (data, r, Allocated) ⟹
      M[offset..offset+len(data)] = encode(data)
```

### 7.2 Region Stack Invariant

**Definition 7.2** (Region Stack Invariant):
```
RegionInv(S, R) iff
  S.mem[4] = |R| ∧
  ∀i < |R|. S.mem[8 + 4*i] = saved_bump_ptr(R[i])
```

### 7.3 Preservation

**Lemma 7.1** (Memory Invariant Preservation):
If `(H, E) ≈ (S, F)` and we compile e, then the resulting state maintains all invariants.

*Proof*:
By induction on compilation. Each operation:
- Allocation: Updates bump pointer correctly
- Region enter/exit: Maintains region stack
- No operation violates the memory layout. □

---

## 8. Type Safety Preservation

### 8.1 WASM Type Safety

WASM is type-safe by design. The WASM validator ensures:
- Stack operations are type-correct
- Function calls have correct signatures
- Memory operations are within bounds

### 8.2 Ephapax → WASM Type Preservation

**Theorem 8.1** (Type Safety Preservation):
If `⊢ e : T` in Ephapax, then `compile(e)` produces valid WASM that passes validation.

*Proof*:
- compileType maps Ephapax types to WASM types
- compileExpr generates type-correct instruction sequences
- The WASM validator accepts the output. □

### 8.3 Memory Safety Preservation

**Theorem 8.2** (Memory Safety Preservation):
Compiled Ephapax programs cannot:
1. Access out-of-bounds memory
2. Use freed memory
3. Double-free memory

*Proof*:
- Bound checking: WASM traps on out-of-bounds
- Use-after-free: Prevented by source-level linearity; no dangling pointers
- Double-free: Prevented by source-level linearity; bump pointer only resets on region exit □

---

## 9. Verified Compilation (Future Work)

### 9.1 CompCert-Style Verification

Following CompCert [Leroy, 2009], we could:
1. Formalize source and target semantics in Coq
2. Implement compiler in Coq (or extract from Gallina)
3. Prove simulation relation
4. Extract certified compiler

### 9.2 Proof Effort Estimate

| Component | Coq Lines (est.) |
|-----------|------------------|
| Source semantics | 500 |
| WASM subset semantics | 800 |
| Compiler implementation | 1000 |
| Simulation relation | 400 |
| Correctness proof | 2000 |
| **Total** | ~4700 |

### 9.3 Alternatives

- **Translation validation**: Verify each compiled output
- **Proof-carrying code**: Attach proofs to compiled binaries
- **Random testing**: QuickCheck-style property testing

---

## 10. Optimizations and Correctness

### 10.1 Safe Optimizations

Optimizations that preserve semantics:
- **Constant folding**: Evaluate constants at compile time
- **Dead code elimination**: Remove unreachable code
- **Inlining**: Substitute function bodies
- **Common subexpression elimination**: Share computations

### 10.2 Optimization Correctness

Each optimization must preserve the simulation relation:

**Theorem 10.1** (Optimization Correctness):
If `optimize(code)` is an optimization, then:
```
⟦code⟧_W = ⟦optimize(code)⟧_W
```

*Proof*: Case analysis on each optimization, showing semantic equivalence. □

### 10.3 Linear-Specific Optimizations

- **Drop fusion**: Combine adjacent drops
- **Region coalescing**: Merge nested regions when safe
- **Borrow elimination**: Remove redundant borrow/deref pairs

---

## 11. TODO: Proof Obligations

### 11.1 Main Theorems

- [ ] Formalize source big-step semantics in Coq
- [ ] Formalize WASM subset semantics in Coq
- [ ] Define simulation relation formally
- [ ] Prove Theorem 6.1 (Compiler Correctness)
- [ ] Prove memory invariant preservation
- [ ] Prove type safety preservation

### 11.2 Implementation

- [ ] Implement certified compiler in Coq
- [ ] Extract to Rust/OCaml
- [ ] Validate against test suite

### 11.3 Optimizations

- [ ] Prove each optimization correct
- [ ] Develop optimization verification framework

---

## 12. References

1. Leroy, X. (2009). A formally verified compiler back-end. *Journal of Automated Reasoning*, 43(4).

2. Chlipala, A. (2010). A verified compiler for an impure functional language. *POPL*.

3. Tan, G. & Appel, A.W. (2006). A compositional logic for control flow. *VMCAI*.

4. Haas, A. et al. (2017). Bringing the web up to speed with WebAssembly. *PLDI*.

5. Watt, C. (2018). Mechanising and verifying the WebAssembly specification. *CPP*.

---

*End of Compiler Correctness*
