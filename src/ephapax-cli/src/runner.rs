// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>

//! `ephapax run`: execute a compiled module under wasmtime (v2 plan rung E4).
//!
//! Host imports provided, all in module `env`:
//!
//! - `print_i32(v)` and `print_string(ptr, len)`: the two imports every
//!   compiled module declares. Each writes one line to stdout.
//! - `argv_count`, `argv_arg_len`, `argv_arg_get`: the contract in
//!   `stdlib/Argv.eph`.
//!
//! A module that imports anything else fails to instantiate, with
//! wasmtime's "unknown import" error.

use std::io::Write;

use wasmtime::{Caller, Engine, Error, Linker, Memory, Module, Store, Val};

/// Host state: the argument vector, `argv[0]` first.
type Argv = Vec<String>;

/// Call the exported, parameterless `main` of `wasm` and return its result.
pub fn run_main(wasm: &[u8], argv: Argv) -> Result<Val, String> {
    let engine = Engine::default();
    let module = Module::new(&engine, wasm).map_err(|e| format!("cannot load module: {e}"))?;
    let mut linker = Linker::new(&engine);
    define_host(&mut linker).map_err(|e| format!("cannot define host imports: {e}"))?;
    let mut store = Store::new(&engine, argv);
    let instance = linker
        .instantiate(&mut store, &module)
        .map_err(|e| format!("cannot instantiate module: {e}"))?;
    let main = instance
        .get_func(&mut store, "main")
        .ok_or("module exports no `main`")?;
    // Every Ephapax function returns exactly one value.
    let mut results = [Val::I32(0)];
    main.call(&mut store, &[], &mut results)
        .map_err(|e| format!("Runtime error: {}", e.root_cause()))?;
    Ok(results[0])
}

/// The linear memory that the module exports as `memory`.
fn memory(caller: &mut Caller<'_, Argv>) -> wasmtime::Result<Memory> {
    caller
        .get_export("memory")
        .and_then(|e| e.into_memory())
        .ok_or_else(|| Error::msg("module exports no `memory`"))
}

/// Define the host functions that a compiled program can import from the
/// module `env`.
fn define_host(linker: &mut Linker<Argv>) -> wasmtime::Result<()> {
    linker.func_wrap("env", "print_i32", |v: i32| println!("{v}"))?;
    linker.func_wrap(
        "env",
        "print_string",
        |mut caller: Caller<'_, Argv>, ptr: i32, len: i32| -> wasmtime::Result<()> {
            let mem = memory(&mut caller)?;
            // Wasm addresses are unsigned 32-bit.
            let (start, len) = (ptr as u32 as usize, len as u32 as usize);
            let bytes = start
                .checked_add(len)
                .and_then(|end| mem.data(&caller).get(start..end))
                .ok_or_else(|| Error::msg("print_string: range is outside linear memory"))?;
            let mut out = std::io::stdout().lock();
            out.write_all(bytes)?;
            out.write_all(b"\n")?;
            Ok(())
        },
    )?;
    linker.func_wrap("env", "argv_count", |caller: Caller<'_, Argv>| {
        caller.data().len() as i32
    })?;
    linker.func_wrap(
        "env",
        "argv_arg_len",
        |caller: Caller<'_, Argv>, idx: i32| arg(caller.data(), idx).map_or(-1, |a| a.len() as i32),
    )?;
    linker.func_wrap(
        "env",
        "argv_arg_get",
        |mut caller: Caller<'_, Argv>,
         idx: i32,
         buf_ptr: i32,
         buf_len: i32|
         -> wasmtime::Result<i32> {
            let Some(bytes) = arg(caller.data(), idx).map(|a| a.as_bytes().to_vec()) else {
                return Ok(-1);
            };
            // A negative or too-small `buf_len` is "insufficient".
            if usize::try_from(buf_len).map_or(true, |n| n < bytes.len()) {
                return Ok(-1);
            }
            // A buffer outside linear memory is a program bug: trap.
            let mem = memory(&mut caller)?;
            mem.write(&mut caller, buf_ptr as u32 as usize, &bytes)?;
            Ok(bytes.len() as i32)
        },
    )?;
    Ok(())
}

/// Argument `idx`, or `None` when `idx` is out of range (negative included).
fn arg(argv: &Argv, idx: i32) -> Option<&String> {
    argv.get(usize::try_from(idx).ok()?)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The one thing an .eph program cannot observe yet: the bytes
    /// `argv_arg_get` copies into linear memory.
    #[test]
    fn argv_arg_get_copies_the_argument_bytes() {
        let engine = Engine::default();
        let module = Module::new(
            &engine,
            r#"(module
                 (import "env" "argv_arg_get" (func $get (param i32 i32 i32) (result i32)))
                 (memory (export "memory") 1)
                 (func (export "get") (param i32 i32 i32) (result i32)
                   (call $get (local.get 0) (local.get 1) (local.get 2))))"#,
        )
        .unwrap();
        let mut linker = Linker::new(&engine);
        define_host(&mut linker).unwrap();
        let argv = vec!["prog.eph".to_string(), "héllo".to_string()];
        let mut store = Store::new(&engine, argv);
        let instance = linker.instantiate(&mut store, &module).unwrap();
        let get = instance
            .get_typed_func::<(i32, i32, i32), i32>(&mut store, "get")
            .unwrap();
        let mem = instance.get_memory(&mut store, "memory").unwrap();

        // "héllo" is 6 bytes of UTF-8.
        assert_eq!(get.call(&mut store, (1, 16, 64)).unwrap(), 6);
        assert_eq!(&mem.data(&store)[16..22], "héllo".as_bytes());
        // Buffer too small, negative length, index out of range: -1.
        assert_eq!(get.call(&mut store, (1, 16, 5)).unwrap(), -1);
        assert_eq!(get.call(&mut store, (1, 16, -1)).unwrap(), -1);
        assert_eq!(get.call(&mut store, (2, 16, 64)).unwrap(), -1);
        assert_eq!(get.call(&mut store, (-1, 16, 64)).unwrap(), -1);
        // Buffer outside linear memory: a trap, not a silent -1.
        assert!(get.call(&mut store, (1, 65_534, 64)).is_err());
    }
}
