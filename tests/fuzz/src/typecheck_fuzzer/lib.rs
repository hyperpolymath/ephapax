#![no_main]
// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

use libfuzzer_sys::fuzz_target;
use ephapax_parser::parse;
use ephapax_typing::TypeChecker;

fuzz_target!(|data: &[u8]| {
    // Convert arbitrary bytes to UTF-8 string
    let input = String::from_utf8_lossy(data);
    
    // Try to parse first
    if let Ok(expr) = parse(&input) {
        // If parsing succeeds, try type checking
        let mut tc = TypeChecker::new();
        let _result = tc.check(&expr);
        // The fuzzer will detect any panics in type checking
    }
    // If parsing fails, that's fine - we're testing robustness
});
