// SPDX-License-Identifier: PMPL-1.0-or-later
// Factorial benchmark - recursive implementation (AssemblyScript)

export function factorial(n: i32): i32 {
    if (n <= 1) {
        return 1;
    } else {
        return n * factorial(n - 1);
    }
}

export function main(): i32 {
    return factorial(20);
}
