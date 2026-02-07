#!/usr/bin/env python3
# SPDX-License-Identifier: PMPL-1.0-or-later
# Generate markdown comparison tables from benchmark results

import json
import os
from pathlib import Path
from typing import Dict, List

def load_criterion_results(bench_name: str) -> Dict:
    """Load Criterion benchmark results from JSON."""
    criterion_path = Path(f"target/criterion/{bench_name}")

    results = {}
    for subdir in criterion_path.glob("*"):
        if subdir.is_dir() and (subdir / "base" / "estimates.json").exists():
            with open(subdir / "base" / "estimates.json") as f:
                data = json.load(f)
                results[subdir.name] = data

    return results

def format_time(nanoseconds: float) -> str:
    """Format time in appropriate units."""
    if nanoseconds < 1000:
        return f"{nanoseconds:.2f} ns"
    elif nanoseconds < 1_000_000:
        return f"{nanoseconds / 1000:.2f} µs"
    elif nanoseconds < 1_000_000_000:
        return f"{nanoseconds / 1_000_000:.2f} ms"
    else:
        return f"{nanoseconds / 1_000_000_000:.2f} s"

def format_size(bytes_size: int) -> str:
    """Format byte size in appropriate units."""
    if bytes_size < 1024:
        return f"{bytes_size} B"
    elif bytes_size < 1024 * 1024:
        return f"{bytes_size / 1024:.2f} KB"
    else:
        return f"{bytes_size / (1024 * 1024):.2f} MB"

def generate_compile_time_table(results: Dict) -> str:
    """Generate markdown table for compilation times."""
    table = ["## Compilation Time Comparison\n"]
    table.append("| Benchmark | Language | Mean Time | Std Dev |")
    table.append("|-----------|----------|-----------|---------|")

    for name, data in sorted(results.items()):
        mean = data["mean"]["point_estimate"]
        std_dev = data["std_dev"]["point_estimate"]

        # Parse name format: "ephapax/fibonacci"
        parts = name.split("/")
        lang = parts[0] if len(parts) > 0 else "unknown"
        bench = parts[1] if len(parts) > 1 else name

        table.append(f"| {bench} | {lang} | {format_time(mean)} | ±{format_time(std_dev)} |")

    return "\n".join(table)

def generate_runtime_perf_table(results: Dict) -> str:
    """Generate markdown table for runtime performance."""
    table = ["## Runtime Performance Comparison\n"]
    table.append("| Benchmark | Language | Mean Time | Throughput |")
    table.append("|-----------|----------|-----------|------------|")

    for name, data in sorted(results.items()):
        mean = data["mean"]["point_estimate"]
        throughput = 1_000_000_000 / mean if mean > 0 else 0

        # Parse name format: "fibonacci/Ephapax"
        parts = name.split("/")
        bench = parts[0] if len(parts) > 0 else name
        lang = parts[1] if len(parts) > 1 else "unknown"

        table.append(f"| {bench} | {lang} | {format_time(mean)} | {throughput:.2f} ops/s |")

    return "\n".join(table)

def main():
    print("Generating benchmark comparison report...\n")

    report = ["# Ephapax Performance Benchmarks\n"]
    report.append(f"*Generated: {Path.cwd().name}*\n")

    # Compilation time results
    try:
        compile_results = load_criterion_results("compile_time")
        report.append(generate_compile_time_table(compile_results))
        report.append("\n")
    except Exception as e:
        print(f"Warning: Could not load compile_time results: {e}")

    # Runtime performance results
    try:
        runtime_results = load_criterion_results("runtime_perf")
        report.append(generate_runtime_perf_table(runtime_results))
        report.append("\n")
    except Exception as e:
        print(f"Warning: Could not load runtime_perf results: {e}")

    # Write report
    output_path = Path("benches/BENCHMARK-RESULTS.md")
    with open(output_path, "w") as f:
        f.write("\n".join(report))

    print(f"✓ Report generated: {output_path}")

if __name__ == "__main__":
    main()
