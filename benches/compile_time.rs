// SPDX-License-Identifier: PMPL-1.0-or-later
// Compilation time benchmarks for Ephapax

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use std::path::Path;
use std::fs;

fn compile_ephapax_file(source_path: &Path) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
    let source = fs::read_to_string(source_path)?;

    // Parse
    let module = ephapax_syntax::parse_module(&source, source_path.to_str().unwrap())?;

    // Type check
    ephapax_typing::check_module(&module)?;

    // Compile to WASM
    let wasm = ephapax_wasm::compile_module(&module)?;

    Ok(wasm)
}

fn benchmark_compilation(c: &mut Criterion) {
    let benchmarks = vec![
        ("fibonacci", "benches/comparison/ephapax/fibonacci.eph"),
        ("factorial", "benches/comparison/ephapax/factorial.eph"),
    ];

    let mut group = c.benchmark_group("compile_time");

    for (name, path) in benchmarks {
        group.bench_with_input(BenchmarkId::new("ephapax", name), &path, |b, &path| {
            b.iter(|| {
                let path = Path::new(path);
                compile_ephapax_file(black_box(path)).unwrap()
            });
        });
    }

    group.finish();
}

criterion_group!(benches, benchmark_compilation);
criterion_main!(benches);
