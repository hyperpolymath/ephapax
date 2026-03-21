# Solo Lexical Blueprint for Ephapax Linear

This document captures the lexical decisions for the Solo v1.0 grammar (`grammar/solo-v1-grammar.ebnf`). The ephapax linear toolchain tokenizes the source code into a deterministic stream before syntax or type checking runs.

## Token classes

1. **Keywords** – words that the parser treats specially (no identifiers):
   - Control and declarations: `fn`, `async`, `#[safe]`, `struct`, `effect`, `contract`, `impl`, `comptime`, `arena`
   - Modifiers: `pub`, `let`, `mut`, `go`, `return`, `await`, `try`, `restrict`
   - Flow: `if`, `else`, `while`, `for`, `in`
   - Literals: `true`, `false`
   - Module/namespace: `use`

2. **Literals**
   - **Integers:** sequences of ASCII digits (`0-9`).
   - **Strings:** double-quoted, support `\n`, `\r`, `\t`, `\"`, `\\`.
   - **Booleans:** `true`/`false` tokens map to dedicated literal tokens.

3. **Operators and punctuators**
   - Arithmetic/comparison: `+`, `-`, `*`, `/`, `%`, `=`, `==`, `!=`, `<`, `<=`, `>`, `>=`
   - Logical: `&&`, `||`, `!`
   - Structural: `(` `)` `{` `}` `[` `]` `;` `:` `::` `,` `.` `..` `->` `?`
   - Ownership: `&`, `#`, `#[safe]`.

4. **Identifiers**
   - Start with ASCII letter or `_`, followed by letters, digits, or `_`.

5. **Comments**
   - Line comments begin with `//` and continue to end-of-line.
   - Block comments start with `/*` and end with `*/`. Nested blocks are not supported yet.

## Lexer behavior

- **Whitespace**: spaces, tabs, carriage returns, and newlines only separate tokens and are otherwise ignored.
- **Keyword detection**: once an identifier is read, the lexer consults a keyword table and returns the corresponding token.
- **Multi-character operators**: `==`, `!=`, `<=`, `>=`, `::`, `->`, `&&`, `||`, and `..` are handled by peeking ahead during lexing.
- **Strings and escapes**: the lexer's `read_string_literal` stops at the closing `"` and processes escape sequences so the parser always receives normalized string content.
- **Error resilience**: unknown characters are skipped but recorded in diagnostic metadata for future phases.

## Usage

The lexer produces a `Vec<Token>` consumed by the parser. Each token is annotated with semantic meaning (keywords vs identifiers) so the parser can stay focused on grammar rules while the lexer enforces the ephapax linear encoding of Solo's surface syntax.

Future work: expand to handle floating-point literals, character literals, and attribute macros beyond `#[safe]` once the grammar grows.
