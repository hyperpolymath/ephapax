// SPDX-License-Identifier: PMPL-1.0-or-later
// Runtime performance benchmarks using wasmtime

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use wasmtime::*;
use std::path::Path;
use std::fs;

struct WasmBenchmark {
    name: String,
    language: String,
    module: Module,
}

fn load_wasm_module(engine: &Engine, path: &Path) -> Result<Module, Box<dyn std::error::Error>> {
    let wasm_bytes = fs::read(path)?;
    let module = Module::new(engine, &wasm_bytes)?;
    Ok(module)
}

fn setup_benchmarks() -> Result<Vec<WasmBenchmark>, Box<dyn std::error::Error>> {
    let engine = Engine::default();
    let mut benchmarks = Vec::new();

    // Load Ephapax benchmarks
    for file in &["fibonacci", "factorial"] {
        let path = Path::new(&format!("benches/comparison/ephapax/{}.wasm", file));
        if path.exists() {
            let module = load_wasm_module(&engine, path)?;
            benchmarks.push(WasmBenchmark {
                name: file.to_string(),
                language: "Ephapax".to_string(),
                module,
            });
        }
    }

    // Load Rust benchmarks
    for file in &["fibonacci", "factorial"] {
        let path = Path::new(&format!("benches/comparison/rust/{}.wasm", file));
        if path.exists() {
            let module = load_wasm_module(&engine, path)?;
            benchmarks.push(WasmBenchmark {
                name: file.to_string(),
                language: "Rust".to_string(),
                module,
            });
        }
    }

    // Load AssemblyScript benchmarks
    for file in &["fibonacci", "factorial"] {
        let path = Path::new(&format!("benches/comparison/assemblyscript/{}.wasm", file));
        if path.exists() {
            let module = load_wasm_module(&engine, path)?;
            benchmarks.push(WasmBenchmark {
                name: file.to_string(),
                language: "AssemblyScript".to_string(),
                module,
            });
        }
    }

    Ok(benchmarks)
}

fn execute_wasm(module: &Module) -> Result<i32, Box<dyn std::error::Error>> {
    let mut store = Store::new(module.engine(), ());
    let instance = Instance::new(&mut store, module, &[])?;

    let main_func = instance.get_typed_func::<(), i32>(&mut store, "main")?;
    let result = main_func.call(&mut store, ())?;

    Ok(result)
}

fn benchmark_runtime(c: &mut Criterion) {
    let benchmarks = setup_benchmarks().expect("Failed to load WASM modules");

    let mut group = c.benchmark_group("runtime_perf");

    for bench in benchmarks {
        let id = format!("{}/{}", bench.name, bench.language);
        group.bench_with_input(BenchmarkId::from_parameter(&id), &bench.module, |b, module| {
            b.iter(|| {
                execute_wasm(black_box(module)).unwrap()
            });
        });
    }

    group.finish();
}

criterion_group!(benches, benchmark_runtime);
criterion_main!(benches);
