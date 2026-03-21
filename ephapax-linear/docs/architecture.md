# Ephapax Linear Interpreter Architecture

## Vision
Rebuild My Language from the ground up in the ephapax linear style:
- Solo v1 grammar as canonical syntax (`grammar/solo-v1-grammar.ebnf`).
- Linear interpreter that enforces affine/resource usage at runtime.
- Duet/Ensemble layers represented as metadata / orchestration constructs within the same interpreter.

## Core Components
1. **Parser** (linear S-expression AST)
   - Reads tokens defined by the grammar; produces AST nodes with span info.
   - Supports `fn`, `struct`, `effect`, `comptime`, `agent`, `intent/@synth`, and `comptime orchestrate` keywords.
   - Each AST node carries `affinity` metadata (affine vs unrestricted).

2. **Type System**
   - Simple judgement `Γ ⊢ e : τ [affinity]`.
   - Affine/linear types (`affine_type = !τ`) restrict duplication.
   - Contracts/intent directives attach metadata for Duet-level verification.

3. **Interpreter / Evaluator**
   - Linear evaluation context tracks resource ownership.
   - Moves consume variables unless explicitly cloned (with `copy` rules).
   - Effects and comptime blocks run in dedicated environments.
   - Agents orchestrated via `comptime orchestrate` configs from the ensemble grammar doc.

4. **Toolchain Flow**
   - Parser → AST → Linear type checker → Interpreter.
   - Duet/Ensemble metadata is layered on the AST so the same runtime can simulate agent orchestration (for now via ambient interpretation).

## Next Steps
- Build `src/ast.rs`, `src/parser.rs`, `src/type_checker.rs`, `src/interpreter.rs` inside `ephapax-linear/src/`.
- Implement a minimal REPL or script runner to exercise the Solo grammar and Duet intents.
- Capture Duet/Ensemble semantics in `docs/` so the blueprint remains documented alongside the code.
