# Syntax

Complete syntax reference for Ephapax.

## Lexical Elements

### Comments

```ephapax
-- Single line comment

{- Multi-line
   comment -}
```

### Identifiers

```ephapax
variable_name     -- Variables and functions
TypeName          -- Types (conventionally capitalized)
'a                -- Type variables (future)
```

### Literals

```ephapax
42                -- I32
42L               -- I64 (future)
3.14              -- F64
3.14f             -- F32 (future)
"hello"           -- String literal
true, false       -- Bool
()                -- Unit
```

## Types

### Base Types

```ephapax
()      -- Unit
Bool    -- Boolean
I32     -- 32-bit integer
I64     -- 64-bit integer
F32     -- 32-bit float
F64     -- 64-bit float
```

### Compound Types

```ephapax
String@r          -- String in region r
T1 -> T2          -- Function type
(T1, T2)          -- Product (pair)
T1 + T2           -- Sum (variant)
&T                -- Borrow
```

## Expressions

### Literals

```ephapax
42                -- Integer
3.14              -- Float
"hello"           -- String (must allocate)
true              -- Boolean
()                -- Unit
```

### Variables

```ephapax
x                 -- Variable reference
```

### Let Bindings

```ephapax
let x = e1 in e2

let x: T = e1 in e2   -- With type annotation

let! x = e1 in e2     -- Linear annotation
```

### Functions

```ephapax
-- Lambda
fn(x: T) -> body

-- Multi-argument lambda
fn(x: T1) -> fn(y: T2) -> body

-- Application
f(arg)

-- Chained application
f(a)(b)(c)
```

### Operators

```ephapax
-- Arithmetic
x + y
x - y
x * y
x / y
x % y

-- Comparison
x == y
x != y
x < y
x > y
x <= y
x >= y

-- Logical
x && y
x || y
!x
```

### Conditionals

```ephapax
if condition then expr1 else expr2
```

### Pairs

```ephapax
-- Construction
(e1, e2)

-- Projection
pair.0
pair.1

-- Destructuring
let (x, y) = pair in body
```

### Sums

```ephapax
-- Injection
inl[RightType](expr)
inr[LeftType](expr)

-- Case analysis
case expr of
  inl(x) -> body1
  inr(y) -> body2
end
```

### Regions

```ephapax
region r {
  body
}
```

### String Operations

```ephapax
-- Allocation
String.new@r("content")

-- Operations
String.len(&s)
String.concat(s1, s2)
String.eq(&s1, &s2)
```

### Borrowing

```ephapax
&expr             -- Create borrow
```

### Resource Management

```ephapax
drop(expr)        -- Consume and discard
copy(expr)        -- Duplicate (unrestricted only)
```

## Declarations

### Functions

```ephapax
fn name(param1: T1, param2: T2): ReturnType =
  body
```

### Type Aliases (Future)

```ephapax
type Name = Type
type Pair[A, B] = (A, B)
```

## Grammar Summary

```ebnf
module     ::= decl*

decl       ::= 'fn' IDENT '(' params ')' ':' type '=' expr
             | 'type' IDENT '=' type

params     ::= (param (',' param)*)?
param      ::= IDENT ':' type

type       ::= base_type
             | 'String' '@' IDENT
             | type '->' type
             | '(' type ',' type ')'
             | type '+' type
             | '&' type

expr       ::= literal
             | IDENT
             | 'String.new' '@' IDENT '(' STRING ')'
             | 'let' IDENT '=' expr 'in' expr
             | 'fn' '(' IDENT ':' type ')' '->' expr
             | expr '(' expr ')'
             | '(' expr ',' expr ')'
             | 'inl' '[' type ']' '(' expr ')'
             | 'inr' '[' type ']' '(' expr ')'
             | 'case' expr 'of' branches 'end'
             | 'if' expr 'then' expr 'else' expr
             | 'region' IDENT '{' expr '}'
             | '&' expr
             | 'drop' '(' expr ')'
             | 'copy' '(' expr ')'
```

## Operator Precedence

| Precedence | Operators | Associativity |
|------------|-----------|---------------|
| 1 (lowest) | `||` | Left |
| 2 | `&&` | Left |
| 3 | `==` `!=` | Left |
| 4 | `<` `>` `<=` `>=` | Left |
| 5 | `+` `-` | Left |
| 6 | `*` `/` `%` | Left |
| 7 | `!` `-` (unary) | Right |
| 8 | `.` (projection) | Left |
| 9 (highest) | Function application | Left |

## Keywords

```
let       let!      fn        if        then      else
region    drop      copy      true      false     inl
inr       case      of        end       in        type
```

## Reserved for Future

```
match     with      where     forall    exists    mut
async     await     import    export    module    trait
impl      self      Self      pub       priv      struct
enum      interface class     new       ref
```

## Style Conventions

### Naming

- Variables: `snake_case`
- Types: `PascalCase`
- Constants: `SCREAMING_SNAKE_CASE`
- Functions: `snake_case`

### Indentation

- 2 or 4 spaces (project choice)
- Consistent throughout

### Line Length

- Soft limit: 80 characters
- Hard limit: 120 characters

### Examples

```ephapax
-- Good style
fn process_data(input: String@r): Result@r =
  region temp {
    let parsed = parse@temp(input)
    let validated = validate(parsed)
    transform@r(validated)
  }

-- Multiline expressions
let result =
  if condition then
    complex_expression_1
  else
    complex_expression_2
```

## Further Reading

- [Types](types.md) - Type system details
- [Specification](../../spec/SPEC.md) - Formal grammar
- [Style Guide](../contributing/style-guide.md) - Coding conventions
