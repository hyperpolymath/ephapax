// SPDX-License-Identifier: PMPL-1.0-or-later
// Fibonacci benchmark - recursive implementation (Rust wasm32)

#[no_mangle]
pub extern "C" fn fib(n: i32) -> i32 {
    if n <= 1 {
        n
    } else {
        fib(n - 1) + fib(n - 2)
    }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    fib(30)
}
