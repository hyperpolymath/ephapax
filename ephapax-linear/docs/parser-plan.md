# Solo Parser Implementation Plan

This plan captures how the ephapax linear parser will evolve now that the canonical Solo grammar and lexer are in place.

## Goals

- **Complete coverage of the Solo v1 grammar** in `grammar/solo-v1-grammar.ebnf`. The parser must consume every production listed in the document, starting with top-level declarations (functions, structs, effects, imports, arenas, comptime).
- **Linear-friendly AST**: Every node will carry affinity metadata (leaning on `Affinity` in `src/ast.rs`) so that downstream passes can enforce affine ownership without re-traversing the whole tree.
- **Fast diagnostic surface**: The parser will propagate span-like data from the lexer so the error messages from `ParserError` can reference exact token boundaries.

## Workstream

1. **Statements & Declarations**
   - Extend `parse_statement` to handle `if`, `while`, `for`, `go`, `await`, `try`, `comptime`, and contract clauses.
   - Support `struct`, `effect`, and `effect impl` declarations by adding new AST nodes (or reusing existing ones with metadata).
   - Map `pub`/`use`/`arena` forms to separate parsing helpers so the module-level loop remains manageable.

2. **Expressions**
   - Add Pratt-style precedence for comparison (`==`, `!=`, `<`, `>`, `<=`, `>=`), logical (`&&`, `||`), assignment (`=`), and field/call chaining.
   - Handle tuple/array/record literals (`[ ... ]`, `{ ... }`, `( ... )`), range expressions (`..`), lambda expressions (`|...|`), and `restrict`.
   - Keep the expression grammar extensible for Duet attributes later (`@synth`, `intent`).

3. **Types & Contracts**
   - Implement a lightweight `parse_type` so function signatures, struct fields, and effect declarations can record types.
   - Parse contract clauses (`pre`, `post`, `invariant`) and keep them attached to the relevant `Function` nodes.

4. **Next Steps**
   - Once the parser accepts Solo programs, hook the AST into `type_checker.rs` so affinity rules and contracts can be validated.
   - Build a minimal interpreter/repl (or reuse `src/interpreter.rs`) to execute parsed output and verify semantics.
   - Add regression tests under `src/tests/` covering each new grammar piece (contracts, comptime, effects).

## Reminder

Keep the `grammar/solo-v1-grammar.ebnf` file as the single source of truth. If any grammar tweaks are required (lambda expressions, range types, new literal forms), update the grammar file first, then adjust the lexer/parser accordingly.
