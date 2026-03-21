# Ephapax Complete Language Specification v0.1

<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
<!-- Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) -->

## Purpose

This document specifies Ephapax (ἐφάπαξ — "once for all"), a dyadic programming
language combining:
- **Affine types** (values used at most once — implicit drop permitted)
- **Linear types** (values used exactly once — implicit drop is a compile error)
- **Region-based memory management** (scoped arenas, no GC)
- **WASM-first** compilation (no garbage collector required)

The dyadic principle: both disciplines coexist at per-binding granularity.

---

# PART 1: LEXICAL GRAMMAR

## 1.1 Character Classes

```ebnf
letter        = 'a'..'z' | 'A'..'Z' ;
digit         = '0'..'9' ;
alpha_num     = letter | digit | '_' ;
hex_digit     = digit | 'a'..'f' | 'A'..'F' ;
bin_digit     = '0' | '1' ;
oct_digit     = '0'..'7' ;
```

## 1.2 Whitespace and Comments

```ebnf
whitespace    = ' ' | '\t' | '\n' | '\r' ;
line_comment  = '//' { any_char - '\n' } '\n' ;
skip          = whitespace | line_comment ;
```

## 1.3 Identifiers

```ebnf
lower_ident   = ('a'..'z' | '_') { alpha_num } ;
upper_ident   = ('A'..'Z') { alpha_num } ;
ident         = lower_ident ;
type_ident    = upper_ident ;
module_path   = upper_ident { '.' upper_ident } ;
```

## 1.4 Keywords

```
fn        let       let!      in        region
match     if        else      type      module
import    return    true      false     copy
borrow    move      drop
```

## 1.5 Operators

```
+  -  *  /  %  ==  !=  <  >  <=  >=
&&  ||  !  &  @  ::  ->  =>  :  ;
=  |  ,  .  ..  ( )  { }  [ ]
```

## 1.6 Literals

```ebnf
integer       = digit { digit | '_' }
              | '0x' hex_digit { hex_digit | '_' }
              | '0b' bin_digit { bin_digit | '_' }
              | '0o' oct_digit { oct_digit | '_' } ;

float         = digit { digit } '.' digit { digit }
                [ ('e' | 'E') ['+' | '-'] digit { digit } ] ;

boolean       = 'true' | 'false' ;

string        = '"' { string_char | escape_seq } '"' ;
string_char   = any_char - '"' - '\\' ;
escape_seq    = '\\' ( 'n' | 'r' | 't' | '\\' | '"' | '\''
              | 'x' hex_digit hex_digit
              | 'u' '{' hex_digit { hex_digit } '}' ) ;

char          = '\'' ( any_char - '\'' - '\\' | escape_seq ) '\'' ;

unit          = '(' ')' ;
```

---

# PART 2: SYNTAX

## 2.1 Top-Level Declarations

```ebnf
program       = { declaration } ;

declaration   = fn_decl
              | type_decl
              | module_decl
              | import_decl ;

fn_decl       = 'fn' ident [ type_params ] '(' [ params ] ')' '->' type_expr block ;
type_params   = '<' type_param { ',' type_param } '>' ;
type_param    = upper_ident
              | upper_ident ':' upper_ident   (* bounded *)
              ;

params        = param { ',' param } ;
param         = ident ':' type_expr ;

type_decl     = 'type' upper_ident [ type_params ] '=' type_expr ;

module_decl   = 'module' module_path block ;

import_decl   = 'import' module_path ;
```

## 2.2 Expressions

```ebnf
expr          = let_expr
              | let_linear_expr
              | region_expr
              | if_expr
              | match_expr
              | lambda_expr
              | binary_expr
              | call_expr
              | borrow_expr
              | copy_expr
              | block
              | literal
              | ident
              | '(' expr ')' ;

let_expr      = 'let' pattern '=' expr [ 'in' expr ]
              | 'let' pattern '=' expr ';' expr ;

let_linear_expr = 'let!' pattern '=' expr [ 'in' expr ]
              | 'let!' pattern '=' expr ';' expr ;

region_expr   = 'region' ident ':' block ;

if_expr       = 'if' expr block [ 'else' ( block | if_expr ) ] ;

match_expr    = 'match' expr '{' { match_arm } '}' ;
match_arm     = pattern '=>' expr [ ',' ] ;

lambda_expr   = 'fn' '(' [ params ] ')' [ '->' type_expr ] block
              | 'fn' '(' [ params ] ')' [ '->' type_expr ] '=>' expr ;

binary_expr   = expr bin_op expr ;
bin_op        = '+' | '-' | '*' | '/' | '%'
              | '==' | '!=' | '<' | '>' | '<=' | '>='
              | '&&' | '||' | '++' ;

call_expr     = expr '(' [ args ] ')'
              | module_path '.' ident '(' [ args ] ')' ;
args          = expr { ',' expr } ;

borrow_expr   = '&' expr ;

copy_expr     = 'copy' '(' expr ')' ;

block         = '{' { stmt } [ expr ] '}' ;
stmt          = expr ';'
              | let_expr
              | let_linear_expr ;
```

## 2.3 Region-Specific Syntax

```ebnf
(* Region-scoped allocation: value allocated in region r *)
region_alloc  = expr '@' ident '(' args ')' ;

(* Example: String.new@r("hello") *)
(* The @r is the region annotation — binds value's lifetime to region r *)
```

## 2.4 Patterns

```ebnf
pattern       = '_'                         (* wildcard *)
              | ident                       (* variable binding *)
              | literal                     (* literal pattern *)
              | upper_ident '(' pattern { ',' pattern } ')'  (* constructor *)
              | '(' pattern ',' pattern { ',' pattern } ')'  (* tuple *)
              ;
```

## 2.5 Type Expressions

```ebnf
type_expr     = type_ident                  (* named type *)
              | type_ident '<' type_expr { ',' type_expr } '>'  (* generic *)
              | '(' type_expr { ',' type_expr } ')'  (* tuple *)
              | type_expr '->' type_expr    (* function *)
              | '&' type_expr              (* borrow/reference *)
              | type_expr '@' ident        (* region-scoped type *)
              | 'i32' | 'i64' | 'f32' | 'f64' | 'bool' | 'String' | '()' ;
```

---

# PART 3: TYPE SYSTEM

## 3.1 Qualifiers

Every binding has a qualifier:
- **Affine** (`let`): value may be used at most once. Unused values are
  implicitly dropped at scope exit.
- **Linear** (`let!`): value must be used exactly once. Unused values are
  a compile-time error.

## 3.2 Context Splitting

When an expression has sub-expressions, the typing context is split:
- Linear bindings go to exactly one sub-expression.
- Affine bindings go to at most one sub-expression (may be dropped).

## 3.3 Branch Consistency

Both branches of `if`/`match` must consume the same linear bindings.

## 3.4 Region Scoping

A value of type `T@r` (allocated in region `r`) cannot appear in any
type that outlives `r`. This prevents region escape.

## 3.5 Borrowing

`&x` borrows `x` without consuming it. The borrow's lifetime is bounded
by `x`'s region. Borrows are always read-only.

---

# PART 4: SEMANTICS

## 4.1 Region Semantics

- `region r: { ... }` creates an arena allocator `r`.
- `Foo.new@r(...)` allocates in `r`.
- At region exit, all memory in `r` is freed in bulk.
- Values in `r` are inaccessible after exit (enforced by type system).

## 4.2 Linear Semantics

- A linear binding (`let!`) must appear exactly once in the continuation.
- If unused: compile error "linear variable not consumed".
- If used twice: compile error "linear variable already consumed".

## 4.3 Affine Semantics

- An affine binding (`let`) may appear at most once.
- If unused: silently dropped (weakening rule applies).
- If used twice: compile error "affine variable already consumed".

## 4.4 Evaluation Order

- Left-to-right evaluation of arguments.
- Eager/strict evaluation (no laziness).
- Block expressions evaluate sequentially; final expression is the result.
