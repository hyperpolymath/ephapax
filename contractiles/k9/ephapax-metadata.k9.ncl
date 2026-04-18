K9!
# SPDX-License-Identifier: PMPL-1.0-or-later
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
# K9 Kennel-level guard: ephapax project metadata and linear type invariants
# Security Level: Kennel (data-only, no execution)
# No signature required

{
  pedigree = {
    schema_version = "1.0.0",
    component_type = "language-compiler-metadata",
    security = {
      leash = 'Kennel,
      trust_level = "data-only",
      allow_network = false,
      allow_filesystem_write = false,
      allow_subprocess = false,
    },
    metadata = {
      name = "ephapax-metadata",
      version = "0.1.0",
      description = "Ephapax: linearly-typed language with Coq-verified semantics — project invariants",
      author = "Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>",
    },
  },

  # Project configuration
  config = {
    # Workspace crates that must be present
    required_crates = [
      "ephapax-ir",
      "ephapax-syntax",
      "ephapax-typing",
      "ephapax-wasm",
      "ephapax-runtime",
      "ephapax-lexer",
      "ephapax-parser",
      "ephapax-interp",
      "ephapax-repl",
    ],

    # Proof system invariants (CRITICAL)
    proof_system = {
      # Target: 0 Admitted, 0 sorry in all Coq files
      admitted_count_max = 0,
      # Dangerous bypasses forbidden
      forbidden_proof_patterns = [
        "Admitted",
        "sorry",
        "believe_me",
        "assert_total",
        "unsafeCoerce",
      ],
      # Linear type soundness must be formally proven
      linear_soundness_proof_required = true,
    },

    # Safety invariants (linear type guarantees must propagate to Rust impl)
    safety = {
      forbidden_patterns = [
        "unwrap()",
        "expect()",
        "todo!()",
        "unimplemented!()",
      ],
      # No unsafe in typing/runtime critical paths
      unsafe_in_typing_forbidden = true,
    },

    # Test requirements
    tests = {
      min_total_tests = 300,
      coq_proof_files_required = true,
      e2e_pipeline_tests_required = true,
    },

    # Build configuration
    build = {
      edition = "2021",
      msrv = "1.75",
      workspace_resolver = "2",
    },

    # Language policy
    banned_files = ["Makefile", "Dockerfile"],
    banned_languages = ["python", "typescript", "javascript", "go"],
  },

  # RSR compliance
  rsr = {
    explainme = true,
    ai_manifest = true,
    machine_readable = true,
    spdx_headers_required = true,
    security_md_required = true,
    idris2_abi = true,
    zig_ffi = true,
  },
}
