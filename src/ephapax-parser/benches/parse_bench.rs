// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Parser benchmarks — measures parse throughput for various expression sizes.

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use ephapax_parser::parse;

/// Simple integer literal
fn bench_literal(c: &mut Criterion) {
    c.bench_function("parse_literal", |b| b.iter(|| parse(black_box("42"))));
}

/// Simple let binding
fn bench_let(c: &mut Criterion) {
    c.bench_function("parse_let", |b| {
        b.iter(|| parse(black_box("let x = 42 in x")))
    });
}

/// Nested let bindings (depth 10)
fn bench_nested_let(c: &mut Criterion) {
    let source = "let a = 1 in let b = 2 in let c = 3 in let d = 4 in \
                  let e = 5 in let f = 6 in let g = 7 in let h = 8 in \
                  let i = 9 in let j = 10 in a";
    c.bench_function("parse_nested_let_10", |b| {
        b.iter(|| parse(black_box(source)))
    });
}

/// Lambda + application
fn bench_lambda_app(c: &mut Criterion) {
    c.bench_function("parse_lambda_app", |b| {
        b.iter(|| parse(black_box("(fn(x: I32) -> x)(42)")))
    });
}

/// If-then-else
fn bench_if(c: &mut Criterion) {
    c.bench_function("parse_if", |b| {
        b.iter(|| parse(black_box("if true then 1 else 2")))
    });
}

/// Pair construction + projection
fn bench_pair(c: &mut Criterion) {
    c.bench_function("parse_pair", |b| b.iter(|| parse(black_box("(1, 2).0"))));
}

/// Arithmetic expression
fn bench_arithmetic(c: &mut Criterion) {
    c.bench_function("parse_arithmetic", |b| {
        b.iter(|| parse(black_box("1 + 2 * 3 - 4 / 5")))
    });
}

/// Complex expression combining multiple features
fn bench_complex(c: &mut Criterion) {
    let source = "let f = fn(x: I32) -> if x == 0 then 1 else x * 2 in \
                  let p = (f(10), f(20)) in \
                  let! r = p.0 + p.1 in r";
    c.bench_function("parse_complex", |b| b.iter(|| parse(black_box(source))));
}

criterion_group!(
    benches,
    bench_literal,
    bench_let,
    bench_nested_let,
    bench_lambda_app,
    bench_if,
    bench_pair,
    bench_arithmetic,
    bench_complex,
);
criterion_main!(benches);
