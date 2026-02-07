// SPDX-License-Identifier: PMPL-1.0-or-later
// Fibonacci benchmark - recursive implementation (AssemblyScript)

export function fib(n: i32): i32 {
    if (n <= 1) {
        return n;
    } else {
        return fib(n - 1) + fib(n - 2);
    }
}

export function main(): i32 {
    return fib(30);
}
