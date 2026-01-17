;; SPDX-License-Identifier: PMPL-1.0
;; STATE.scm - Project state for ephapax

(state
  (metadata
    (version "0.1.0")
    (schema-version "1.0")
    (created "2024-06-01")
    (updated "2026-01-17")
    (project "ephapax")
    (repo "hyperpolymath/ephapax"))

  (project-context
    (name "Ephapax")
    (tagline "Linear type system for safe memory management targeting WebAssembly")
    (tech-stack ("idris2" "zig" "rust" "wasm")))

  (current-position
    (phase "alpha")
    (overall-completion 60)
    (working-features
      ("Linear type system design"
       "Locked surface syntax"
       "Affine parser stage (Idris2)"
       "Affine typechecker completeness"
       "IR emit + backend alignment"
       "Zig token buffer FFI"
       "Parser profiling counters"
       "End-to-end affine compile to WASM"
       "Smoke CI pipeline"
       "Usability pass"
       "Proven library integration scaffolding"
       "No use-after-free guarantees"
       "No memory leak guarantees"))))
