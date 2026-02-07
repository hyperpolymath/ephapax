// SPDX-License-Identifier: PMPL-1.0-or-later
// Factorial benchmark - recursive implementation (Rust wasm32)

#[no_mangle]
pub extern "C" fn factorial(n: i32) -> i32 {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}

#[no_mangle]
pub extern "C" fn main() -> i32 {
    factorial(20)
}
