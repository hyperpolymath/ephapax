// SPDX-License-Identifier: EUPL-1.2
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use ephapax_vram_cache::VramCache;

fn bench_cache_hit(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache_operations");

    for size in [1024, 10240, 102400].iter() {
        let mut cache = VramCache::new(10 * 1024 * 1024).unwrap();
        let test_data = vec![0u8; *size];
        cache.insert("test.eph", &test_data).unwrap();

        group.bench_with_input(
            BenchmarkId::new("hit", size),
            size,
            |b, _| {
                b.iter(|| {
                    let result = cache.get("test.eph").unwrap();
                    black_box(result);
                });
            },
        );
    }

    group.finish();
}

fn bench_cache_insert(c: &mut Criterion) {
    let mut group = c.benchmark_group("cache_insert");

    for size in [1024, 10240, 102400].iter() {
        let test_data = vec![0u8; *size];

        group.bench_with_input(
            BenchmarkId::new("insert", size),
            size,
            |b, _| {
                let mut cache = VramCache::new(10 * 1024 * 1024).unwrap();
                let mut counter = 0;
                b.iter(|| {
                    cache.insert(&format!("file{}.eph", counter), &test_data).unwrap();
                    counter += 1;
                });
            },
        );
    }

    group.finish();
}

fn bench_vs_ram_cache(c: &mut Criterion) {
    use std::collections::HashMap;

    let mut group = c.benchmark_group("vram_vs_ram");
    let test_data = vec![0u8; 10240];

    // VRAM cache
    group.bench_function("vram_cache", |b| {
        let mut cache = VramCache::new(10 * 1024 * 1024).unwrap();
        cache.insert("test.eph", &test_data).unwrap();
        b.iter(|| {
            black_box(cache.get("test.eph").unwrap());
        });
    });

    // RAM cache (HashMap)
    group.bench_function("ram_cache", |b| {
        let mut cache: HashMap<String, Vec<u8>> = HashMap::new();
        cache.insert("test.eph".to_string(), test_data.clone());
        b.iter(|| {
            black_box(cache.get("test.eph"));
        });
    });

    group.finish();
}

criterion_group!(benches, bench_cache_hit, bench_cache_insert, bench_vs_ram_cache);
criterion_main!(benches);
