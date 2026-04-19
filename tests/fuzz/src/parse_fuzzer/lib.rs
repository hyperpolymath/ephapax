#![no_main]
// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

use libfuzzer_sys::fuzz_target;
use ephapax_parser::parse;

fuzz_target!(|data: &[u8]| {
    // Convert arbitrary bytes to UTF-8 string (replace invalid sequences)
    let input = String::from_utf8_lossy(data);
    
    // Try to parse the input
    let _result = parse(&input);
    
    // The fuzzer will detect panics, hangs, or memory issues
    // We don't need to assert anything - just exercising the parser
});
