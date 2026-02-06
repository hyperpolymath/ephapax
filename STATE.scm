;; SPDX-License-Identifier: PMPL-1.0-or-later
;; STATE.scm - Current project state

(define state
  '((metadata
     (version "1.0")
     (schema-version "1.0")
     (created "2026-02-04")
     (updated "2026-02-06T2")
     (project "ephapax")
     (repo "hyperpolymath/ephapax"))

    (project-context
     (name "Ephapax")
     (tagline "Linear type system with once-only evaluation and formal Coq proofs")
     (tech-stack ("rust" "idris2" "coq" "zig")))

    (current-position
     (phase "type-checker-and-wasm")
     (overall-completion 60)
     (components
       (("lexer" "Tokenization with logos (736 LOC)" 100)
        ("parser" "Full parser with chumsky (1240 LOC)" 100)
        ("syntax" "AST definitions (328 LOC)" 100)
        ("interpreter" "Tree-walking interpreter (832 LOC)" 100)
        ("typing" "Type checker - in progress (1002 LOC)" 60)
        ("wasm-backend" "WASM code generation with function compilation, linear lowering (2434 LOC)" 65)
        ("ir" "S-expression intermediate representation (758 LOC)" 100)
        ("runtime" "Runtime support (211 LOC)" 80)
        ("stdlib" "Standard library skeleton (290 LOC)" 40)
        ("repl" "Interactive shell (398 LOC)" 100)
        ("cli" "Command-line interface (460 LOC)" 100)
        ("vram-cache" "VRAM caching layer (363 LOC)" 80)
        ("coq-proofs" "Syntax, typing rules, operational semantics (619 LOC)" 100)
        ("idris2-abi" "Experimental two-stage compiler (parser/typechecker)" 30)
        ("zig-ffi" "C ABI compatibility layer (1620 LOC across 40 files)" 70)
        ("ephapax-proven" "Formally verified data structures (LRU, Buffer, Resource, Queue, Set, Hex)" 90)
        ("ephapax-proven-ffi" "Zig FFI for proven data structures" 70)
        ("debugger" "Not started" 0)
        ("lsp" "Not started" 0)
        ("package-manager" "Not started" 0)))
     (working-features
       ("Full lexer/parser/interpreter/REPL/CLI pipeline"
        "S-expression intermediate representation"
        "Formal Coq proofs: syntax formalization, linear typing rules, operational semantics with soundness"
        "Experimental Idris2 -> Rust two-stage compiler (parser/typechecker in Idris2, WASM backend in Rust)"
        "ephapax-proven library: 6 formally verified data structures"
        "  - LRU cache, Buffer, Resource tracker, Queue, Set, Hex encoding"
        "  - 113 tests (45 unit + 17 integration + 51 doc)"
        "Zig FFI layer: C ABI compatibility for proven data structures"
        "15+ example programs (.eph files)"
        "Conformance test suite (pass/fail directories)"
        "VRAM caching layer for GPU-accelerated operations"
        "12-crate Rust workspace (~7,918 LOC total)")))

    (route-to-mvp
     (milestones
      ((milestone-id "m1")
       (name "Core Language")
       (status "complete")
       (completion 100)
       (items ("Lexer with logos"
               "Parser with chumsky"
               "AST definitions"
               "Tree-walking interpreter"
               "REPL and CLI"
               "S-expression IR")))

      ((milestone-id "m2")
       (name "Formal Verification")
       (status "complete")
       (completion 100)
       (items ("Coq syntax formalization (Syntax.v)"
               "Linear typing rules (Typing.v)"
               "Operational semantics with soundness proofs (Semantics.v)")))

      ((milestone-id "m3")
       (name "Type Checker")
       (status "in-progress")
       (completion 60)
       (items ("Linear type inference engine (in progress)"
               "Affine type tracking"
               "Use-once enforcement"
               "Type error reporting")))

      ((milestone-id "m4")
       (name "WASM Backend")
       (status "in-progress")
       (completion 65)
       (items ("WASM code generation module with wasmparser validation (done)"
               "Top-level function compilation to real WASM functions (done)"
               "Function calls between named functions (done)"
               "Proper local variable management with two-pass compilation (done)"
               "Integer/boolean operations, all BinOp/UnaryOp (done)"
               "Control flow: if/else, let bindings, blocks (done)"
               "Pair/sum type lowering to linear memory (done)"
               "Region-scoped memory management (done)"
               "String allocation/concat/length in linear memory (done)"
               "Linear type tracking: drop insertion, consumption marking (done)"
               "57 validated tests (wasmparser verification) (done)"
               "Lambda/closure conversion (stub - needs closure conversion)"
               "Browser and server target support (not started)")))

      ((milestone-id "m5")
       (name "Proven Data Structures")
       (status "in-progress")
       (completion 90)
       (items ("LRU cache (done)"
               "Buffer (done)"
               "Resource tracker (done)"
               "Queue (done)"
               "Set (done)"
               "Hex encoding (done)"
               "Rust wrappers (done)"
               "Zig FFI bindings (done)"
               "Full integration tests (done)")))))

    (blockers-and-issues
     (critical
       ("Type checker incomplete - critical path to MVP"))
     (high
       ("Lambda/closure conversion not yet implemented in WASM backend"
        "Standard library is skeletal (290 LOC)"))
     (medium
       ("Idris2 two-stage compiler is experimental, not production-ready"
        "No LSP server"
        "No debugger"))
     (low
       ("VRAM cache needs GPU testing on real hardware")))

    (critical-next-actions
     (immediate
       ("Complete linear type checker with use-once enforcement"
        "Expand type error reporting with hints"))
     (this-week
       ("Advance WASM code generation for basic programs"
        "Expand standard library beyond skeleton"))
     (this-month
       ("Achieve end-to-end: source -> type check -> WASM output"
        "Begin LSP server implementation"
        "Stabilize Idris2 two-stage compiler")))

    (session-history
     ((date "2026-02-06")
      (accomplishments
        ("Updated STATE.scm with accurate project status from code audit")))
     ((date "2026-02-06-session2")
      (accomplishments
        ("Major WASM backend overhaul: 1219 LOC -> 2434 LOC"
         "Implemented top-level function compilation (Decl::Fn -> real WASM functions)"
         "Implemented function calls between named functions (App + Var -> call instruction)"
         "Added proper local variable management with two-pass compilation"
         "Fixed WASM section ordering (Type, Import, Function, Memory, Export, Code, Data)"
         "Fixed region_enter/region_exit stack balance bugs"
         "Fixed compile_copy stack balance bug"
         "Added wasmparser validation to all tests (dev-dependency)"
         "Added ty_to_valtype mapping for Ephapax types to WASM value types"
         "Added dynamic type registration for arbitrary function signatures"
         "Expanded test suite: 6 tests -> 57 tests (all wasmparser-validated)"
         "Tests cover: literals, arithmetic, comparison, logic, if/else, let, nested let,"
         "  pairs, sums, case analysis, blocks, regions, strings, copy, drop,"
         "  borrow/deref, negation, module compilation, function calling"
         "WASM backend completion: 40% -> 65%"
         "Overall project completion: 55% -> 60%"))))))
