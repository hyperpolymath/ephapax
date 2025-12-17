// SPDX-License-Identifier: EUPL-1.2
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Standard Library
//!
//! This module provides the standard library definitions for Ephapax,
//! including built-in functions, type definitions, and prelude items.

use ephapax_syntax::{BaseTy, Module, Span, Ty};
use smol_str::SmolStr;

/// Standard library prelude - items that are always available
pub const PRELUDE_SOURCE: &str = r#"
// Identity function (polymorphic, works with any type)
fn id(x: a) -> a = x

// Compose two functions
fn compose(f: b -> c, g: a -> b) -> (a -> c) =
    fn(x: a) -> f(g(x))

// Flip function arguments
fn flip(f: (a, b) -> c) -> ((b, a) -> c) =
    fn(args: (b, a)) -> let (b, a) = args in f((a, b))

// Constant function - returns first argument, consumes second
fn const(x: a, _y: b) -> a = x

// Pair operations
fn fst(p: (a, b)) -> a = let (x, _) = p in x
fn snd(p: (a, b)) -> b = let (_, y) = p in y
fn swap(p: (a, b)) -> (b, a) = let (x, y) = p in (y, x)

// Boolean operations
fn not(b: Bool) -> Bool = if b then false else true
fn and(x: Bool, y: Bool) -> Bool = if x then y else false
fn or(x: Bool, y: Bool) -> Bool = if x then true else y

// Integer operations
fn succ(n: I32) -> I32 = n + 1
fn pred(n: I32) -> I32 = n - 1
fn abs(n: I32) -> I32 = if n < 0 then 0 - n else n
fn min(a: I32, b: I32) -> I32 = if a < b then a else b
fn max(a: I32, b: I32) -> I32 = if a > b then a else b
fn clamp(x: I32, lo: I32, hi: I32) -> I32 = min(max(x, lo), hi)

// Floating point operations
fn abs_f32(n: F32) -> F32 = if n < 0.0 then 0.0 - n else n
fn abs_f64(n: F64) -> F64 = if n < 0.0 then 0.0 - n else n

// Either/Sum type operations
fn is_left(e: a + b) -> Bool =
    case e of
        inl _ => true,
        inr _ => false
    end

fn is_right(e: a + b) -> Bool =
    case e of
        inl _ => false,
        inr _ => true
    end

// Apply a function based on which variant
fn either(f: a -> c, g: b -> c, e: a + b) -> c =
    case e of
        inl x => f(x),
        inr y => g(y)
    end

// Map over left side of sum
fn map_left(f: a -> c, e: a + b) -> (c + b) =
    case e of
        inl x => inl f(x),
        inr y => inr y
    end

// Map over right side of sum
fn map_right(f: b -> c, e: a + b) -> (a + c) =
    case e of
        inl x => inl x,
        inr y => inr f(y)
    end
"#;

/// I/O operations module source
pub const IO_SOURCE: &str = r#"
// Print a string to stdout (consumes the string linearly)
fn print(s: String@r) -> () = __builtin_print(s)

// Print with newline
fn println(s: String@r) -> () = __builtin_println(s)

// Read a line from stdin (allocates in region r)
fn read_line@r() -> String@r = __builtin_read_line@r()

// Print an integer
fn print_i32(n: I32) -> () = __builtin_print_i32(n)
fn print_i64(n: I64) -> () = __builtin_print_i64(n)
fn print_f32(n: F32) -> () = __builtin_print_f32(n)
fn print_f64(n: F64) -> () = __builtin_print_f64(n)
fn print_bool(b: Bool) -> () = if b then __builtin_print("true") else __builtin_print("false")
"#;

/// String operations module source
pub const STRING_SOURCE: &str = r#"
// String length
fn length(s: &String@r) -> I32 = __builtin_string_length(s)

// Concatenate two strings (allocates result in region r)
fn concat@r(a: String@r, b: String@r) -> String@r = __builtin_string_concat@r(a, b)

// Create a new string from a literal (allocates in region r)
fn from_literal@r(s: &str) -> String@r = __builtin_string_from_literal@r(s)

// Clone a string (allocates copy in region r)
fn clone@r(s: &String@r) -> String@r = __builtin_string_clone@r(s)

// Check if string is empty
fn is_empty(s: &String@r) -> Bool = length(s) == 0

// Compare two strings
fn eq(a: &String@r1, b: &String@r2) -> Bool = __builtin_string_eq(a, b)
"#;

/// Math operations module source
pub const MATH_SOURCE: &str = r#"
// Constants
let pi: F64 = 3.141592653589793
let e: F64 = 2.718281828459045
let tau: F64 = 6.283185307179586

// Basic math functions (F64)
fn sqrt(x: F64) -> F64 = __builtin_sqrt(x)
fn sin(x: F64) -> F64 = __builtin_sin(x)
fn cos(x: F64) -> F64 = __builtin_cos(x)
fn tan(x: F64) -> F64 = __builtin_tan(x)
fn exp(x: F64) -> F64 = __builtin_exp(x)
fn log(x: F64) -> F64 = __builtin_log(x)
fn log10(x: F64) -> F64 = __builtin_log10(x)
fn pow(base: F64, exp: F64) -> F64 = __builtin_pow(base, exp)
fn floor(x: F64) -> F64 = __builtin_floor(x)
fn ceil(x: F64) -> F64 = __builtin_ceil(x)
fn round(x: F64) -> F64 = __builtin_round(x)

// Type conversions
fn i32_to_f64(n: I32) -> F64 = __builtin_i32_to_f64(n)
fn f64_to_i32(n: F64) -> I32 = __builtin_f64_to_i32(n)
fn i32_to_i64(n: I32) -> I64 = __builtin_i32_to_i64(n)
fn i64_to_i32(n: I64) -> I32 = __builtin_i64_to_i32(n)
"#;

/// Memory/Region operations module source
pub const MEMORY_SOURCE: &str = r#"
// Allocate memory in a region
fn alloc@r(size: I32) -> Ref@r(Unit) = __builtin_alloc@r(size)

// Free a region (called automatically at region end)
fn free_region(r: Region) -> () = __builtin_free_region(r)

// Get current region memory usage
fn region_size(r: &Region) -> I32 = __builtin_region_size(r)
"#;

/// Build the complete standard library module
pub fn build_stdlib_module() -> Module {
    Module {
        name: SmolStr::new("std"),
        decls: vec![],  // Built-in declarations are handled specially
    }
}

/// Get all standard library source as a single string
pub fn get_stdlib_source() -> String {
    format!(
        "// Ephapax Standard Library\n\n{}\n\n// IO\n{}\n\n// String\n{}\n\n// Math\n{}\n\n// Memory\n{}",
        PRELUDE_SOURCE,
        IO_SOURCE,
        STRING_SOURCE,
        MATH_SOURCE,
        MEMORY_SOURCE
    )
}

/// List of built-in function names that the interpreter/compiler must handle specially
pub const BUILTIN_FUNCTIONS: &[&str] = &[
    // I/O
    "__builtin_print",
    "__builtin_println",
    "__builtin_read_line",
    "__builtin_print_i32",
    "__builtin_print_i64",
    "__builtin_print_f32",
    "__builtin_print_f64",
    // String
    "__builtin_string_length",
    "__builtin_string_concat",
    "__builtin_string_from_literal",
    "__builtin_string_clone",
    "__builtin_string_eq",
    // Math
    "__builtin_sqrt",
    "__builtin_sin",
    "__builtin_cos",
    "__builtin_tan",
    "__builtin_exp",
    "__builtin_log",
    "__builtin_log10",
    "__builtin_pow",
    "__builtin_floor",
    "__builtin_ceil",
    "__builtin_round",
    // Conversions
    "__builtin_i32_to_f64",
    "__builtin_f64_to_i32",
    "__builtin_i32_to_i64",
    "__builtin_i64_to_i32",
    // Memory
    "__builtin_alloc",
    "__builtin_free_region",
    "__builtin_region_size",
];

/// Create a span for stdlib items (zero-length at position 0)
fn stdlib_span() -> Span {
    Span::dummy()
}

/// Helper to create a type variable
fn type_var(name: &str) -> Ty {
    Ty::Var(SmolStr::new(name))
}

/// Helper to create a base type
fn base_ty(ty: BaseTy) -> Ty {
    Ty::Base(ty)
}

/// Helper to create a function type
fn fun_ty(param: Ty, ret: Ty) -> Ty {
    Ty::Fun {
        param: Box::new(param),
        ret: Box::new(ret),
    }
}

/// Helper to create a product type
fn prod_ty(left: Ty, right: Ty) -> Ty {
    Ty::Prod {
        left: Box::new(left),
        right: Box::new(right),
    }
}

/// Helper to create a sum type
fn sum_ty(left: Ty, right: Ty) -> Ty {
    Ty::Sum {
        left: Box::new(left),
        right: Box::new(right),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_prelude_source_valid() {
        // Just check that the source strings are not empty
        assert!(!PRELUDE_SOURCE.is_empty());
        assert!(!IO_SOURCE.is_empty());
        assert!(!STRING_SOURCE.is_empty());
        assert!(!MATH_SOURCE.is_empty());
        assert!(!MEMORY_SOURCE.is_empty());
    }

    #[test]
    fn test_builtin_functions_list() {
        assert!(BUILTIN_FUNCTIONS.contains(&"__builtin_print"));
        assert!(BUILTIN_FUNCTIONS.contains(&"__builtin_sqrt"));
        assert!(BUILTIN_FUNCTIONS.len() > 20);
    }

    #[test]
    fn test_get_stdlib_source() {
        let source = get_stdlib_source();
        assert!(source.contains("fn id("));
        assert!(source.contains("fn print("));
        assert!(source.contains("fn sqrt("));
    }
}
