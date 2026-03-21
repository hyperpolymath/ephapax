; SPDX-License-Identifier: PMPL-1.0-or-later
; Tree-sitter local variable tracking for Ephapax

; Scopes
(fn_decl body: (_) @local.scope)
(block) @local.scope
(region_expr body: (_) @local.scope)
(lambda_expr body: (_) @local.scope)

; Definitions
(fn_decl name: (identifier) @local.definition)
(param name: (identifier) @local.definition)
(let_expr pattern: (identifier) @local.definition)
(let_linear_expr pattern: (identifier) @local.definition)

; References
(identifier) @local.reference
