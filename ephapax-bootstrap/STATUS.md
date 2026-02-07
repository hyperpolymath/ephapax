# Self-Hosting Compiler Implementation Status

**Last Updated**: 2026-02-07
**Phase**: Language Feature Implementation
**Overall Progress**: 15% (1/6 phases complete)

---

## Summary

The self-hosting Ephapax compiler is being implemented in Ephapax itself using linear types.

**Current Status**: ✅ Lexer complete, adding missing language features to enable further development.

---

## Phase 1: Language Feature Implementation

### Task 6: String Operations ✅ COMPLETE

**Status**: Implemented in `ephapax-runtime`
**Time**: ~2 hours

**Added Functions:**
- ✅ `__ephapax_string_char_code(handle, idx) -> i32` - Get byte at index
- ✅ `__ephapax_string_substr(handle, start, len) -> StringHandle` - Extract substring
- ✅ `__ephapax_string_from_char(char_code) -> StringHandle` - Create from byte
- ✅ `__ephapax_string_eq(h1, h2) -> i32` - String equality

**Existing Functions** (already implemented):
- ✅ `__ephapax_string_new(ptr, len) -> StringHandle`
- ✅ `__ephapax_string_len(handle) -> u32`
- ✅ `__ephapax_string_ptr(handle) -> u32`
- ✅ `__ephapax_string_concat(h1, h2) -> StringHandle`
- ✅ `__ephapax_string_drop(handle)`

**Integration**: All functions exported as WASM imports, ready for use in compiled `.eph` code.

---

### Task 7: List/Vector Type ⏳ IN PROGRESS

**Status**: Not started
**Estimated**: 2 days

**Requirements:**
```ephapax
type List<T> = ...  // Growable array with linear ownership

fn list_new<T>(): List<T>
fn list_append<T>(list: List<T>, item: T): List<T>
fn list_len<T>(list: List<T>): I32
fn list_get<T>(list: List<T>, idx: I32): T
fn list_set<T>(list: List<T>, idx: I32, val: T): List<T>
```

**Implementation Plan:**
1. Define `List<T>` type in syntax
2. Add generic type support to type checker
3. Implement runtime functions in `ephapax-runtime`
4. Add list literal syntax `[1, 2, 3]`
5. Add list operations to stdlib

**Challenges:**
- Generic types (may need monomorphization)
- Linear ownership tracking for elements
- Memory layout (dynamic sizing)

---

### Task 8: Tuple Syntax ⏳ PENDING

**Status**: Not started
**Estimated**: 2 days

**Requirements:**
```ephapax
// Tuple types
type TokenAndLexer = (Token, Lexer)

// Tuple construction
let pair = (tok, lexer) in ...

// Tuple destructuring
let (tok, lexer2) = lex_token(lexer) in ...

// Function returns
fn lex_token(l: Lexer): (Token, Lexer) = ...
```

**Implementation Plan:**
1. Add tuple syntax to parser
   - Type syntax: `(T, U, V)`
   - Expression syntax: `(expr1, expr2)`
   - Pattern syntax: `(pat1, pat2)`

2. Extend type checker
   - Tuple type inference
   - Destructuring validation
   - Linearity tracking (tuple is linear if any element is linear)

3. Add codegen support
   - WASM representation (struct with N fields)
   - Construction: allocate + store fields
   - Destruction: extract fields + deallocate

**Challenges:**
- Multi-value returns (WASM has native support)
- Pattern matching integration
- Linear tracking for tuples

---

### Task 9: Complete Self-Hosting Compiler ⏳ PENDING

**Status**: Blocked on Tasks 7-8
**Estimated**: 3-4 weeks

**Components:**

#### 1. parser.eph (1 week)
- Recursive descent parser
- AST construction with linear ownership
- Error recovery
- Precedence climbing for expressions

#### 2. typechecker.eph (1 week)
- Linear type checking
- Affine type checking (mode parameter)
- Use-once enforcement
- Type inference

#### 3. wasm_codegen.eph (1.5 weeks)
- WASM bytecode emission
- Function compilation
- Expression compilation
- Linear value tracking
- Memory management

#### 4. main.eph (2 days)
- CLI argument parsing
- File I/O
- Error reporting
- Pipeline orchestration

---

## Completed Work

### ✅ lexer.eph (Phase 1.1)

**File**: `ephapax-bootstrap/lexer.eph` (677 lines)
**Status**: Complete (awaiting language features)

**Features:**
- All Ephapax keywords
- Identifiers, operators, literals
- String literals with escapes
- Line and block comments
- Position tracking
- Lambda syntax (`λ` and `\`)
- Error handling

**Token Types:**
```ephapax
type TokenKind =
    | TokKeyword   | TokIdent    | TokInt
    | TokFloat     | TokString   | TokOp
    | TokPunct     | TokArrow    | TokLambda
    | TokEof       | TokError
```

**Linear Design:**
```ephapax
type Token = {
    kind: TokenKind,
    lexeme: String,     // Linear: explicit management
    line: I32,
    col: I32,
}

type Lexer = {
    source: String,     // Linear: single owner
    pos: I32,
    line: I32,
    col: I32,
}
```

---

## Timeline

| Phase | Task | Status | Duration | End Date |
|-------|------|--------|----------|----------|
| 1.1 | lexer.eph | ✅ Complete | 4 hours | 2026-02-07 |
| 1.2 | String ops | ✅ Complete | 2 hours | 2026-02-07 |
| 1.3 | List type | ⏳ Pending | 2 days | TBD |
| 1.4 | Tuple syntax | ⏳ Pending | 2 days | TBD |
| 2.1 | parser.eph | ⏳ Blocked | 1 week | TBD |
| 2.2 | typechecker.eph | ⏳ Blocked | 1 week | TBD |
| 2.3 | wasm_codegen.eph | ⏳ Blocked | 1.5 weeks | TBD |
| 2.4 | main.eph | ⏳ Blocked | 2 days | TBD |
| 3.0 | Bootstrap test | ⏳ Blocked | 2 days | TBD |

**Total Estimated**: ~5-6 weeks from now

---

## Next Steps

1. ✅ ~~Implement string operations~~ (DONE)
2. **Implement list/vector type** (IN PROGRESS)
3. **Implement tuple syntax**
4. **Continue with parser.eph**
5. **Complete remaining compiler components**
6. **Bootstrap test: compile compiler with itself**

---

## Key Decisions Made

1. **String Operations**: Implemented as runtime functions using string handles
2. **Memory Management**: Strings use bump allocation within regions
3. **Error Handling**: Explicit Result types (no exceptions)
4. **State Threading**: Pure functions with explicit state passing
5. **Linear Enforcement**: All compiler data structures use linear types

---

## Blockers

- **lexer.eph**: Cannot compile yet (needs lists, tuples, string ops)
- **parser.eph**: Cannot start (needs lists for token stream, tuples for returns)
- **typechecker.eph**: Cannot start (needs lists for environments)
- **codegen.eph**: Cannot start (needs lists for instruction sequences)

**Resolution**: Complete Tasks 7-8 (lists + tuples) to unblock all components.

---

## Testing Strategy

### Unit Tests (Per Module)
- Test each module in isolation
- Compile with Rust compiler
- Run in WASM runtime

### Integration Tests
- Full pipeline: source → tokens → AST → typed AST → WASM
- Test both linear and affine modes
- Error handling tests

### Bootstrap Test
1. Use Rust compiler to compile Ephapax compiler
2. Use Ephapax compiler to compile itself
3. Verify bit-identical output
4. Use self-compiled compiler to compile itself again
5. Verify bit-identical output

---

## Documentation

- [README.md](README.md) - Overview and architecture
- [NOTES.md](NOTES.md) - Implementation notes and decisions
- [lexer.eph](lexer.eph) - Self-documenting code

---

**Progress**: 1/6 components complete (15%)
**Current Focus**: String operations (✅) → List type (⏳) → Tuple syntax (⏳)
