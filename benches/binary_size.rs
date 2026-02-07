// SPDX-License-Identifier: PMPL-1.0-or-later
// Binary size measurement for compiled WASM modules

use std::path::Path;
use std::fs;
use std::process::Command;

struct SizeReport {
    name: String,
    language: String,
    raw_size: u64,
    gzipped_size: u64,
}

fn measure_wasm_size(wasm_path: &Path) -> Result<(u64, u64), Box<dyn std::error::Error>> {
    // Raw size
    let raw_size = fs::metadata(wasm_path)?.len();

    // Gzip the WASM to measure compressed size
    let gzipped_path = wasm_path.with_extension("wasm.gz");
    Command::new("gzip")
        .arg("-9")
        .arg("-c")
        .arg(wasm_path)
        .stdout(fs::File::create(&gzipped_path)?)
        .status()?;

    let gzipped_size = fs::metadata(&gzipped_path)?.len();

    // Clean up
    fs::remove_file(&gzipped_path)?;

    Ok((raw_size, gzipped_size))
}

fn compile_all_benchmarks() -> Result<(), Box<dyn std::error::Error>> {
    println!("Compiling all benchmark implementations...\n");

    // Compile Ephapax benchmarks
    for file in &["fibonacci", "factorial"] {
        let input = format!("benches/comparison/ephapax/{}.eph", file);
        let output = format!("benches/comparison/ephapax/{}.wasm", file);

        let source = fs::read_to_string(&input)?;
        let module = ephapax_syntax::parse_module(&source, &input)?;
        ephapax_typing::check_module(&module)?;
        let wasm = ephapax_wasm::compile_module(&module)?;
        fs::write(&output, wasm)?;

        println!("✓ Compiled {}", input);
    }

    // Compile Rust benchmarks
    for file in &["fibonacci", "factorial"] {
        let input = format!("benches/comparison/rust/{}.rs", file);
        let output = format!("benches/comparison/rust/{}.wasm", file);

        Command::new("rustc")
            .args(&[
                "--target", "wasm32-unknown-unknown",
                "-C", "opt-level=3",
                "-C", "lto=fat",
                "-C", "codegen-units=1",
                "--crate-type", "cdylib",
                &input,
                "-o", &output,
            ])
            .status()?;

        println!("✓ Compiled {}", input);
    }

    // Compile AssemblyScript benchmarks (requires npm dependencies)
    if Path::new("benches/comparison/assemblyscript/node_modules").exists() {
        Command::new("npm")
            .current_dir("benches/comparison/assemblyscript")
            .arg("run")
            .arg("build")
            .status()?;

        println!("✓ Compiled AssemblyScript benchmarks");
    } else {
        println!("⚠ Skipping AssemblyScript (run 'npm install' in benches/comparison/assemblyscript/)");
    }

    Ok(())
}

fn generate_report() -> Result<(), Box<dyn std::error::Error>> {
    let mut reports = Vec::new();

    // Measure Ephapax
    for file in &["fibonacci", "factorial"] {
        let path = Path::new(&format!("benches/comparison/ephapax/{}.wasm", file));
        if path.exists() {
            let (raw, gzipped) = measure_wasm_size(path)?;
            reports.push(SizeReport {
                name: file.to_string(),
                language: "Ephapax".to_string(),
                raw_size: raw,
                gzipped_size: gzipped,
            });
        }
    }

    // Measure Rust
    for file in &["fibonacci", "factorial"] {
        let path = Path::new(&format!("benches/comparison/rust/{}.wasm", file));
        if path.exists() {
            let (raw, gzipped) = measure_wasm_size(path)?;
            reports.push(SizeReport {
                name: file.to_string(),
                language: "Rust".to_string(),
                raw_size: raw,
                gzipped_size: gzipped,
            });
        }
    }

    // Measure AssemblyScript
    for file in &["fibonacci", "factorial"] {
        let path = Path::new(&format!("benches/comparison/assemblyscript/{}.wasm", file));
        if path.exists() {
            let (raw, gzipped) = measure_wasm_size(path)?;
            reports.push(SizeReport {
                name: file.to_string(),
                language: "AssemblyScript".to_string(),
                raw_size: raw,
                gzipped_size: gzipped,
            });
        }
    }

    // Print markdown table
    println!("\n## Binary Size Comparison\n");
    println!("| Benchmark | Language | Raw Size | Gzipped Size |");
    println!("|-----------|----------|----------|--------------|");

    for report in &reports {
        println!(
            "| {} | {} | {} bytes | {} bytes |",
            report.name, report.language, report.raw_size, report.gzipped_size
        );
    }

    Ok(())
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    compile_all_benchmarks()?;
    println!("\n");
    generate_report()?;
    Ok(())
}
