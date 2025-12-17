# Ephapax Language Specification

**Version**: 0.1.0-draft
**Date**: 2025-12-17
**Status**: Draft
**SPDX-License-Identifier**: EUPL-1.2

---

## 1. Introduction

### 1.1 Overview

Ephapax (from Greek ἐφάπαξ, "once for all") is a programming language with a linear type system designed for safe memory management targeting WebAssembly.

### 1.2 Design Goals

1. **Memory Safety**: Prevent use-after-free, double-free, and memory leaks
2. **No Runtime GC**: All memory management resolved at compile time
3. **WASM-First**: Optimised for WebAssembly's linear memory model
4. **Formal Foundation**: Type system grounded in linear logic with mechanised proofs

### 1.3 Influences

- **Rust**: Ownership and borrowing concepts (simplified)
- **Linear Haskell**: Linear types and multiplicity annotations
- **MLKit**: Region-based memory management
- **Cyclone**: Safe C with regions and unique pointers

---

## 2. Lexical Structure

### 2.1 Keywords

```
let       let!      fn        if        then      else
region    drop      copy      true      false     inl
inr       case      of        match     with      end
```

### 2.2 Operators

```
+   -   *   /   %           -- Arithmetic
==  !=  <   >   <=  >=      -- Comparison
&&  ||  !                    -- Logical
&                            -- Borrow
@                            -- Region annotation
->                           -- Function arrow
:                            -- Type annotation
```

### 2.3 Identifiers

```
identifier  ::= [a-zA-Z_][a-zA-Z0-9_]*
type_var    ::= '\'' [a-z]+
region_name ::= [a-z][a-z0-9_]*
```

### 2.4 Literals

```
integer     ::= [0-9]+
float       ::= [0-9]+ '.' [0-9]+
string      ::= '"' [^"]* '"'
bool        ::= 'true' | 'false'
unit        ::= '()'
```

---

## 3. Types

### 3.1 Base Types

| Type   | Description              | Linearity    |
|--------|--------------------------|--------------|
| `()`   | Unit type                | Unrestricted |
| `Bool` | Boolean                  | Unrestricted |
| `I32`  | 32-bit signed integer    | Unrestricted |
| `I64`  | 64-bit signed integer    | Unrestricted |
| `F32`  | 32-bit float             | Unrestricted |
| `F64`  | 64-bit float             | Unrestricted |

### 3.2 String Type

```
String@r
```

A string allocated in region `r`. Strings are **linear**: they must be used exactly once.

### 3.3 Function Types

```
T1 -> T2
```

Functions consume their linear arguments and produce a result.

### 3.4 Product Types

```
(T1, T2)
```

Pairs. If either component is linear, the pair is linear.

### 3.5 Sum Types

```
T1 + T2
```

Discriminated unions. Linear if either variant is linear.

### 3.6 Borrow Types

```
&T
```

A second-class borrow of type `T`. Borrows:
- Cannot be stored in data structures
- Cannot be returned from functions
- Cannot escape the scope where created

### 3.7 Region Types

```
region r { T }
```

Type `T` scoped to region `r`.

---

## 4. Expressions

### 4.1 Variables

```
x
```

Reference to a bound variable. Linear variables are consumed on use.

### 4.2 Let Bindings

Standard let:
```
let x = e1 in e2
```

Linear let (explicit annotation):
```
let! x = e1 in e2
```

### 4.3 String Operations

Allocation (in region):
```
String.new@r("hello")
```

Concatenation (consumes both):
```
String.concat(s1, s2)
```

Length (borrows):
```
String.len(&s)
```

### 4.4 Functions

Lambda:
```
fn(x: T) -> e
```

Application:
```
f(e)
```

### 4.5 Products

Construction:
```
(e1, e2)
```

Projection:
```
e.0    -- first
e.1    -- second
```

Destructuring let:
```
let (x, y) = e1 in e2
```

### 4.6 Sums

Injection:
```
inl[T2](e)    -- left
inr[T1](e)    -- right
```

Case analysis:
```
case e of
  inl(x) -> e1
  inr(y) -> e2
end
```

### 4.7 Conditionals

```
if e1 then e2 else e3
```

Both branches must consume the same linear resources.

### 4.8 Regions

```
region r {
  e
}
```

All allocations in `e` using `@r` are freed when the region exits.

### 4.9 Borrowing

Create borrow:
```
&e
```

The original value remains available; the borrow provides temporary read access.

### 4.10 Resource Management

Explicit drop:
```
drop(e)
```

Explicit copy (unrestricted types only):
```
copy(e)
```

---

## 5. Typing Rules

### 5.1 Judgement Form

```
R; Γ ⊢ e : T ⊣ Γ'
```

Where:
- `R` is the set of active regions
- `Γ` is the input typing context
- `e` is the expression
- `T` is the type
- `Γ'` is the output context (tracking consumption)

### 5.2 Context Operations

A context `Γ` is a list of `(x : T, used)` triples.

**Lookup**: `Γ(x) = T` if `(x : T, _) ∈ Γ`

**Mark used**: `Γ[x ↦ used]` sets the used flag for `x`

**Extend**: `Γ, x : T` adds a fresh binding

### 5.3 Selected Rules

**T-Var-Lin** (Linear variable use):
```
Γ(x) = T    linear(T)    ¬used(Γ, x)
─────────────────────────────────────
R; Γ ⊢ x : T ⊣ Γ[x ↦ used]
```

**T-StringNew** (String allocation):
```
r ∈ R
────────────────────────────────
R; Γ ⊢ String.new@r(s) : String@r ⊣ Γ
```

**T-StringConcat** (Concatenation):
```
R; Γ ⊢ e1 : String@r ⊣ Γ'
R; Γ' ⊢ e2 : String@r ⊣ Γ''
────────────────────────────────────────
R; Γ ⊢ String.concat(e1, e2) : String@r ⊣ Γ''
```

**T-Region** (Region scope):
```
r ∉ R    R ∪ {r}; Γ ⊢ e : T ⊣ Γ'    T does not mention r
──────────────────────────────────────────────────────────
R; Γ ⊢ region r { e } : T ⊣ Γ'
```

**T-Borrow** (Second-class borrow):
```
Γ(x) = T
────────────────────────────
R; Γ ⊢ &x : &T ⊣ Γ
```

---

## 6. Operational Semantics

### 6.1 Memory Model

Memory is a byte array indexed by 32-bit addresses. Strings are represented as `(ptr, len)` pairs.

### 6.2 Regions

A region is identified by a saved bump pointer. Region entry pushes the current bump pointer; region exit restores it, effectively freeing all allocations made within the region.

### 6.3 Key Reductions

**String Allocation**:
```
⟨μ, R, ρ, String.new@r(s)⟩
  ──→ ⟨μ', R, ρ, loc⟩
where μ' = μ[loc ↦ s], loc fresh
```

**String Concatenation**:
```
⟨μ, R, ρ, String.concat(loc1, loc2)⟩
  ──→ ⟨μ', R, ρ, loc3⟩
where μ(loc1) = s1, μ(loc2) = s2
      μ' = μ[loc1 ↦ ⊥][loc2 ↦ ⊥][loc3 ↦ s1++s2]
```

**Region Exit**:
```
⟨μ, r::R, ρ, region r { v }⟩
  ──→ ⟨free_region(μ, r), R, ρ, v⟩
```

---

## 7. Type Safety

### 7.1 Progress

If `R; Γ ⊢ e : T ⊣ Γ'` and `e` is not a value, then `e` can take a step.

### 7.2 Preservation

If `R; Γ ⊢ e : T ⊣ Γ'` and `e ──→ e'`, then `R; Γ'' ⊢ e' : T ⊣ Γ'` for some `Γ''`.

### 7.3 Linearity

If `R; Γ ⊢ e : T ⊣ Γ'` and `e ──→* v`, then all linear bindings in `Γ` are marked used in `Γ'`.

### 7.4 Memory Safety

1. **No use-after-free**: Linear types ensure resources are not accessed after consumption
2. **No double-free**: Linear types ensure resources are consumed at most once
3. **No leaks**: Linear types ensure resources are consumed at least once
4. **No region escapes**: Region-scoped types cannot outlive their region

---

## 8. Standard Library (Planned)

### 8.1 String Module

```
String.new : ∀r. (data: &[u8]) -> String@r
String.len : ∀r. (&String@r) -> I32
String.concat : ∀r. (String@r, String@r) -> String@r
String.slice : ∀r. (&String@r, I32, I32) -> String@r
String.eq : ∀r. (&String@r, &String@r) -> Bool
```

### 8.2 I/O Module (Future)

```
File.open : ∀r. (&String@r) -> Result[File@r, Error]
File.read : ∀r. (&mut File@r, &mut [u8]) -> Result[I32, Error]
File.write : ∀r. (&mut File@r, &[u8]) -> Result[I32, Error]
File.close : ∀r. (File@r) -> Result[(), Error]
```

---

## 9. WASM Compilation

### 9.1 Type Mapping

| Ephapax Type  | WASM Representation          |
|---------------|------------------------------|
| `()`          | (no value)                   |
| `Bool`        | `i32` (0 or 1)               |
| `I32`         | `i32`                        |
| `I64`         | `i64`                        |
| `F32`         | `f32`                        |
| `F64`         | `f64`                        |
| `String@r`    | `i32` (handle/pointer)       |
| `(T1, T2)`    | `i32` (pointer to struct)    |
| `T1 + T2`     | `i32` (pointer to tagged)    |

### 9.2 Calling Convention

- Arguments passed on WASM stack
- Linear arguments consumed (caller loses access)
- Return value on WASM stack

### 9.3 Memory Layout

```
[0x0000] Bump pointer (4 bytes)
[0x0004] Region stack pointer (4 bytes)
[0x0008] Region stack (256 bytes, 64 levels max)
[0x0108] Heap start
         ... bump-allocated data ...
```

---

## 10. Future Extensions

### 10.1 Typestate

```
type File : Linear
type File<Open> : Linear
type File<Closed> : Linear

fn close : File<Open> -> File<Closed>
```

### 10.2 Fractional Permissions

```
type File<P : Permission>

fn read : &(1/2) File -> Bytes
fn write : &(1) File -> ()
```

### 10.3 Concurrency

```
type Chan<T> : Linear

fn send : (Chan<T>, T) -> ()
fn recv : Chan<T> -> T
```

---

## Appendix A: Grammar

```ebnf
module     ::= decl*

decl       ::= fn_decl | type_decl

fn_decl    ::= 'fn' IDENT '(' params ')' ':' type '=' expr

type_decl  ::= 'type' IDENT '=' type

params     ::= (param (',' param)*)?
param      ::= IDENT ':' type

type       ::= base_type
             | 'String' '@' IDENT
             | type '->' type
             | '(' type ',' type ')'
             | type '+' type
             | '&' type
             | 'region' IDENT '{' type '}'

base_type  ::= '()' | 'Bool' | 'I32' | 'I64' | 'F32' | 'F64'

expr       ::= literal
             | IDENT
             | 'String.new' '@' IDENT '(' STRING ')'
             | 'String.concat' '(' expr ',' expr ')'
             | 'String.len' '(' expr ')'
             | 'let' IDENT '=' expr 'in' expr
             | 'let!' IDENT '=' expr 'in' expr
             | 'fn' '(' IDENT ':' type ')' '->' expr
             | expr '(' expr ')'
             | '(' expr ',' expr ')'
             | expr '.' ('0' | '1')
             | 'inl' '[' type ']' '(' expr ')'
             | 'inr' '[' type ']' '(' expr ')'
             | 'case' expr 'of' 'inl' '(' IDENT ')' '->' expr
                              'inr' '(' IDENT ')' '->' expr 'end'
             | 'if' expr 'then' expr 'else' expr
             | 'region' IDENT '{' expr '}'
             | '&' expr
             | 'drop' '(' expr ')'
             | 'copy' '(' expr ')'

literal    ::= INTEGER | FLOAT | STRING | 'true' | 'false' | '()'
```

---

## Appendix B: References

1. Wadler, P. (1990). *Linear types can change the world!*
2. Tofte, M. & Talpin, J.P. (1997). *Region-based memory management*
3. Walker, D. (2005). *Substructural type systems* (ATTAPL Chapter 1)
4. Bernardy, J.P. et al. (2018). *Linear Haskell: practical linearity in a higher-order polymorphic language*
5. Grossman, D. et al. (2002). *Region-based memory management in Cyclone*

---

*End of Specification*
