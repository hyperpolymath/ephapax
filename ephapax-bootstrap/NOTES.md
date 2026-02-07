# Self-Hosting Compiler Implementation Notes

## Missing Language Features for lexer.eph

The lexer implementation reveals several features that Ephapax needs before it can be self-hosting:

### 1. **String Operations** (CRITICAL)
```ephapax
// Need these as built-in functions or stdlib:
fn string_len(s: String): I32
fn string_char_code(s: String, idx: I32): I32   // Get char as ASCII
fn string_substr(s: String, start: I32, len: I32): String
fn string_from_char(c: I32): String             // ASCII to string
fn string_concat(s1: String, s2: String): String
```

**Status**: Currently missing from Ephapax
**Priority**: HIGH - Required for lexer/parser

### 2. **List/Array Operations**
```ephapax
// Need list/vector operations:
fn append<T>(list: [T], item: T): [T]
fn list_len<T>(list: [T]): I32
fn list_get<T>(list: [T], idx: I32): T
fn list_map<T, U>(list: [T], f: T -> U): [U]
fn list_fold<T, Acc>(list: [T], init: Acc, f: (Acc, T) -> Acc): Acc
```

**Status**: Need to implement growable arrays
**Priority**: HIGH - Required for token lists, AST nodes

### 3. **Record Syntax Clarification**
```ephapax
// Are these equivalent?
type Token = { kind: TokenKind, lexeme: String, ... }
let tok = { kind: TokInt, lexeme: "42", line: 1, col: 1 }

// Or do we need explicit constructor?
type Token = Token(TokenKind, String, I32, I32)
let tok = Token(TokInt, "42", 1, 1)
```

**Status**: Need to clarify syntax
**Priority**: MEDIUM - Affects ergonomics

### 4. **Equality for Strings**
```ephapax
if word == "fn" then TokKeyword else ...
```

**Status**: Need `==` operator for strings
**Priority**: HIGH - Required for keyword matching

### 5. **Tuples/Pair Returns**
```ephapax
fn lex_token(lexer: Lexer): (Token, Lexer) = ...
let (tok, lexer2) = lex_token(lexer) in ...
```

**Status**: Need tuple support
**Priority**: HIGH - State threading pattern

### 6. **Pattern Matching on Records**
```ephapax
case tok of
| { kind: TokEof, ... } -> ...
| { kind: TokIdent, lexeme: name, ... } -> ...
```

**Status**: Need pattern destructuring
**Priority**: MEDIUM - Can workaround with field access

### 7. **Recursive Types**
```ephapax
type Expr =
    | ELambda(String, Expr)       // Expr references itself
    | EApp(Expr, Expr)
    | ELet(String, Expr, Expr)
```

**Status**: Need support for recursive ADTs
**Priority**: HIGH - Required for AST

## Implementation Order

### Phase A: Core Language Extensions (1-2 weeks)

**Before we can continue self-hosting:**

1. **String library** (runtime.eph or WASM imports)
   - Implement basic string operations
   - Add to stdlib or as built-ins

2. **List/Vector type** (stdlib)
   - Growable array implementation
   - Linear ownership for elements
   - Basic operations (append, get, len)

3. **Tuple syntax**
   - Parser support for `(T, U)`
   - Destructuring in `let` bindings
   - Type checker support

4. **Record pattern matching**
   - Destructure records in case expressions
   - Wildcard patterns (`...`)

### Phase B: Continue Self-Hosting (2-3 weeks)

5. **Complete parser.eph** (depends on Phase A)
6. **Complete typechecker.eph**
7. **Complete wasm_codegen.eph**
8. **Complete main.eph**

### Phase C: Bootstrap (1 week)

9. **Use Rust compiler to compile Ephapax compiler**
10. **Use Ephapax compiler to compile itself**
11. **Verify bit-identical output**

## Alternative Approach: Simplified Lexer

We could simplify the lexer to avoid missing features:

```ephapax
// Simplified lexer using only available features
fn lex_char(source: String, pos: I32): TokenKind =
    // Character-by-character processing
    // No string operations needed (just char codes)
    ...

fn lex_all(source: String): I32 =
    // Process entire source in one pass
    // No token list - print as we go
    ...
```

**Tradeoff**: Less clean, but works with current language

## Decision Point

**Option 1**: Pause self-hosting, implement missing features in Rust compiler first
- Cleaner self-hosting code
- More complete language
- Longer path to self-hosting

**Option 2**: Continue with simplified approach using only available features
- Messier code
- Get to self-hosting faster
- Refactor later

**Option 3**: Implement minimal runtime in .eph first (runtime.eph)
- String ops as Ephapax functions
- Lists as linked lists (inefficient but works)
- Pure Ephapax (no WASM imports)

## Recommended: Option 1

**Implement missing features in Rust compiler first**, then complete self-hosting with clean code.

### Priority Features to Add:

1. **String operations** (1 day)
   - Add to `ephapax-stdlib` crate
   - WASM runtime helpers

2. **Growable list type** (2 days)
   - Implement in `ephapax-stdlib`
   - Linear ownership tracked

3. **Tuple syntax** (2 days)
   - Parser + type checker support
   - Codegen

4. **Pattern matching enhancements** (1 day)
   - Record destructuring
   - Wildcards

**Total**: ~1 week to enable self-hosting

## Next Steps

1. **Pause lexer.eph completion**
2. **Add string/list support to Rust compiler**
3. **Add tuple syntax**
4. **Resume self-hosting with complete features**

OR

1. **Continue with simplified lexer**
2. **Accept messier code initially**
3. **Refactor after bootstrap**

---

**Current Status**: lexer.eph written but requires language extensions
**Blocker**: String operations, lists, tuples
**Resolution**: TBD by user preference
