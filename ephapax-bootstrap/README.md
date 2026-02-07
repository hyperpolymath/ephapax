# Ephapax Self-Hosting Compiler

**Status**: In Development (Phase 1: WASM Backend)

This directory contains the **self-hosting compiler** for Ephapax, written entirely in Ephapax itself using **linear types**.

## Architecture

```
ephapax-bootstrap/
├── lexer.eph          ✅ Lexical analysis (tokenization)
├── parser.eph         ⏳ Syntax analysis (AST construction)
├── typechecker.eph    ⏳ Type checking (affine + linear modes)
├── wasm_codegen.eph   ⏳ WASM code generation
├── llvm_codegen.eph   ⏳ LLVM IR code generation (future)
├── runtime.eph        ⏳ Runtime support functions
└── main.eph           ⏳ CLI driver
```

## Design Principles

### 1. Linear Types Throughout

All compiler data structures use **linear types** for memory safety:

```ephapax
type Token = {
    kind: TokenKind,
    lexeme: String,     // Linear: must be explicitly dropped
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

**Benefits:**
- No garbage collection needed
- Memory safety guaranteed at compile time
- Explicit resource management
- Predictable performance

### 2. Mode Duality

The compiler runs in **linear mode** but can compile programs in **both modes**:

```ephapax
fn typecheck(ast: Ast, mode: Mode): Result =
    case mode of
    | Linear -> typecheck_linear(ast)
    | Affine -> typecheck_affine(ast)
```

**Mode Parameter** flows through:
- Type checker (enforces mode rules)
- Code generator (emits appropriate checks)

### 3. Explicit Error Handling

No exceptions - all errors are explicit values:

```ephapax
type Result<T> =
    | Ok(T)
    | Err(String)

fn parse_expr(parser: Parser): (Result<Expr>, Parser) =
    case lex_token(parser) of
    | Ok(tok) -> ...
    | Err(msg) -> (Err(msg), parser)
```

### 4. Functional Style

Pure functions with explicit state threading:

```ephapax
fn advance(lexer: Lexer): Lexer =
    { source: lexer.source
    , pos: lexer.pos + 1
    , line: lexer.line
    , col: lexer.col + 1
    }
```

## Implementation Status

### ✅ Phase 1.1: Lexer (Complete)

**File**: `lexer.eph`

**Features:**
- [x] Keywords: `fn`, `let`, `if`, `case`, etc.
- [x] Identifiers and operators
- [x] Integer and float literals
- [x] String literals with escapes
- [x] Line comments (`//`)
- [x] Block comments (`/* */`)
- [x] Position tracking (line/column)
- [x] Lambda syntax (`λ` or `\`)
- [x] Error tokens

**Token Types:**
```ephapax
type TokenKind =
    | TokKeyword   | TokIdent    | TokInt
    | TokFloat     | TokString   | TokOp
    | TokPunct     | TokArrow    | TokLambda
    | TokEof       | TokError
```

**API:**
```ephapax
fn tokenize(source: String): [Token]
fn lex_token(lexer: Lexer): (Token, Lexer)
```

### ⏳ Phase 1.2: Parser (Next)

**File**: `parser.eph`

**Planned:**
- Recursive descent parser
- AST construction with linear ownership
- Error recovery
- Precedence climbing for expressions
- Pattern matching support

**AST Types:**
```ephapax
type Expr =
    | EVar(String)
    | EInt(I32)
    | ELambda(String, Expr)
    | EApp(Expr, Expr)
    | ELet(String, Expr, Expr)
    | EIf(Expr, Expr, Expr)
    | ECase(Expr, [Arm])
    // ...

type Decl =
    | DFn(String, [Param], Ty, Expr)
    | DType(String, [Variant])

type Module = [Decl]
```

### ⏳ Phase 1.3: Type Checker

**File**: `typechecker.eph`

**Planned:**
- Linear type checking
- Affine type checking (mode parameter)
- Use-once enforcement
- Drop insertion (affine mode)
- Type inference (basic)

**Mode-Aware Checking:**
```ephapax
fn check_expr(expr: Expr, env: Env, mode: Mode): (Result<Ty>, Env) =
    case mode of
    | Linear -> enforce_use_once(expr, env)
    | Affine -> allow_implicit_drop(expr, env)
```

### ⏳ Phase 1.4: WASM Codegen

**File**: `wasm_codegen.eph`

**Planned:**
- WASM bytecode emission
- Function compilation
- Memory management
- String handling
- Linear value tracking

**WASM Encoding:**
```ephapax
fn compile_expr(expr: Expr, ctx: Context): [Instruction] =
    case expr of
    | EInt(n) -> [I32Const(n)]
    | EAdd(l, r) -> compile_expr(l, ctx) ++ compile_expr(r, ctx) ++ [I32Add]
    // ...
```

### ⏳ Phase 1.5: CLI Driver

**File**: `main.eph`

**Planned:**
- Command-line argument parsing
- File I/O
- Error reporting
- Output writing

## Bootstrap Process

### Stage 1: Rust → Ephapax (Current)

Use the **Rust compiler** to compile the Ephapax-written compiler:

```bash
# Compile lexer.eph using Rust compiler
ephapax compile ephapax-bootstrap/lexer.eph -o lexer.wasm

# Compile parser.eph
ephapax compile ephapax-bootstrap/parser.eph -o parser.wasm

# ... continue for all modules
```

### Stage 2: Ephapax → Ephapax (Self-Hosting)

Use the **Ephapax-compiled compiler** to compile itself:

```bash
# Compile the compiler with itself
./ephapax-bootstrap compile ephapax-bootstrap/main.eph -o ephapax2.wasm

# Verify bit-identical output
./ephapax2 compile ephapax-bootstrap/main.eph -o ephapax3.wasm
diff ephapax2.wasm ephapax3.wasm  # Should be identical
```

### Stage 3: Multiple Targets

The self-hosting compiler outputs to multiple targets:

```bash
# Compile to WASM (default)
./ephapax compile program.eph -o program.wasm

# Compile to LLVM IR
./ephapax compile program.eph --target llvm -o program.ll

# Compile to native
llc program.ll -o program.o
gcc program.o -o program
```

## Building Dependencies

The self-hosting compiler requires these **runtime functions** (implemented in Ephapax or as WASM imports):

### String Operations
```ephapax
fn string_len(s: String): I32
fn string_char_code(s: String, i: I32): I32
fn string_substr(s: String, start: I32, len: I32): String
fn string_from_char(c: I32): String
fn string_concat(s1: String, s2: String): String
```

### List Operations
```ephapax
fn append<T>(list: [T], item: T): [T]
fn list_len<T>(list: [T]): I32
fn list_get<T>(list: [T], i: I32): T
```

### I/O Operations
```ephapax
fn print_string(s: String): I32
fn print_int(n: I32): I32
fn read_file(path: String): String
fn write_file(path: String, content: String): I32
```

## Testing Strategy

### Unit Tests (Per Module)

```ephapax
// lexer_test.eph
fn test_lex_keywords(): Bool =
    let tokens = tokenize("fn let if") in
    assert(list_len(tokens) == 4)  // 3 keywords + EOF

fn test_lex_operators(): Bool =
    let tokens = tokenize("+ - * / == !=") in
    assert(list_len(tokens) == 7)  // 6 ops + EOF
```

### Integration Tests (Full Pipeline)

```ephapax
// integration_test.eph
fn test_compile_fibonacci(): Bool =
    let source = "fn fib(n: I32): I32 = if n <= 1 then n else fib(n-1) + fib(n-2)" in
    let tokens = tokenize(source) in
    let ast = parse(tokens) in
    let typed_ast = typecheck(ast, Linear) in
    let wasm = codegen(typed_ast) in
    assert(wasm_valid(wasm))
```

## Performance Goals

| Metric | Target | Status |
|--------|--------|--------|
| Lexer throughput | 1 MB/s | TBD |
| Parser throughput | 500 KB/s | TBD |
| Type check time | < 100ms for 1K LOC | TBD |
| Codegen time | < 200ms for 1K LOC | TBD |
| Binary size | < 100 KB (WASM) | TBD |

## Next Steps

1. **Complete lexer.eph** ✅ (DONE)
2. **Implement parser.eph** ⏳ (NEXT)
3. **Implement typechecker.eph**
4. **Implement wasm_codegen.eph**
5. **Implement main.eph CLI**
6. **Bootstrap test**
7. **Add LLVM backend**
8. **Full self-hosting**

## Contributing

This is a demonstration of linear type system capabilities. Contributions should:
- Use only linear types (no affine shortcuts)
- Explicit resource management (no GC)
- Pure functions with state threading
- Comprehensive error handling

## License

PMPL-1.0-or-later

---

**Progress Tracker**: Phase 1.1/5 (20% complete)
