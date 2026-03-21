; SPDX-License-Identifier: PMPL-1.0-or-later
; Tree-sitter highlight queries for Ephapax

; Keywords
["fn" "let" "in" "type" "module" "import" "return"] @keyword
["if" "else" "match"] @keyword.conditional
["region"] @keyword.storage
["true" "false"] @constant.builtin
["copy" "borrow" "move" "drop"] @keyword.operator

; The dyadic marker — most important syntax element
["let!"] @keyword.linear

; Types
(type_identifier) @type
(primitive_type) @type.builtin
(generic_type (type_identifier) @type)

; Functions
(fn_decl name: (identifier) @function)
(call_expr callee: (identifier) @function.call)
(lambda_expr) @function

; Variables
(identifier) @variable
(param name: (identifier) @variable.parameter)

; Region annotations — visually distinct
(region_expr name: (identifier) @label)
(region_alloc region: (identifier) @label)
(region_type (identifier) @label)

; Module paths
(module_path (type_identifier) @module)

; Operators
(binary_expr operator: _ @operator)
["=" ":" "->" "=>" "@" "&" "!" ";" ","] @punctuation.delimiter
["(" ")" "{" "}" "[" "]" "<" ">"] @punctuation.bracket

; Literals
(integer) @number
(float) @number.float
(string) @string
(char) @character
(escape_sequence) @string.escape
(boolean) @constant.builtin

; Comments
(comment) @comment

; Patterns
(constructor_pattern (type_identifier) @constructor)
"_" @variable.builtin
