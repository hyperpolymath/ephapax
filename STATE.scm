;; SPDX-License-Identifier: PMPL-1.0
;; STATE.scm - Project state for ephapax

(state
  (metadata
    (version "0.1.0")
    (schema-version "1.0")
    (created "2024-06-01")
    (updated "2025-01-17")
    (project "ephapax")
    (repo "hyperpolymath/ephapax"))

  (project-context
    (name "Ephapax")
    (tagline "Linear type system for safe memory management targeting WebAssembly")
    (tech-stack ("rust" "wasm")))

  (current-position
    (phase "alpha")
    (overall-completion 20)
    (working-features
      ("Linear type system design"
       "No use-after-free guarantees"
       "No memory leak guarantees"))))
