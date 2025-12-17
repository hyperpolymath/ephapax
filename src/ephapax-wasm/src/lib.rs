// SPDX-License-Identifier: EUPL-1.2
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax WASM Code Generator
//!
//! Compiles Ephapax IR to WebAssembly with explicit memory management.
//!
//! ## String Representation
//!
//! Strings are represented as (ptr: i32, len: i32) pairs in linear memory.
//! The ptr points to UTF-8 encoded bytes.
//!
//! ## Memory Layout
//!
//! ```text
//! +------------------+
//! | Region Metadata  |  <- 0x0000
//! +------------------+
//! | String Data      |  <- bump allocated
//! +------------------+
//! | Free Space       |
//! +------------------+
//! | Stack (grows down)|  <- top of memory
//! +------------------+
//! ```

use ephapax_syntax::Module as EphapaxModule;
use thiserror::Error;
use wasm_encoder::{
    CodeSection, ExportKind, ExportSection, Function, FunctionSection, Instruction, MemorySection,
    MemoryType, Module, TypeSection, ValType,
};

/// Compilation errors
#[derive(Error, Debug)]
pub enum CompileError {
    #[error("Unsupported expression: {0}")]
    UnsupportedExpression(String),

    #[error("Unbound variable: {0}")]
    UnboundVariable(String),

    #[error("Internal error: {0}")]
    Internal(String),
}

/// Compile an Ephapax module to WebAssembly bytes
pub fn compile_module(module: &EphapaxModule) -> Result<Vec<u8>, CompileError> {
    let mut codegen = Codegen::new();
    // For now, just generate the runtime functions
    // TODO: Compile actual expressions from the module
    let _ = module; // Acknowledge the module parameter
    Ok(codegen.generate())
}

/// WASM representation of a string: (pointer, length)
pub const STRING_SIZE: u32 = 8; // 2 x i32

/// Region metadata size
pub const REGION_HEADER_SIZE: u32 = 16;

/// Initial memory pages (64KB each)
pub const INITIAL_PAGES: u64 = 1;

/// Maximum memory pages
pub const MAX_PAGES: u64 = 256; // 16MB max

/// Code generator state
pub struct Codegen {
    /// Current bump pointer for allocations
    bump_ptr: u32,
    /// Region stack for tracking active regions
    region_stack: Vec<RegionInfo>,
    /// Generated WASM module
    module: Module,
}

#[derive(Debug, Clone)]
struct RegionInfo {
    /// Region name
    #[allow(dead_code)]
    name: String,
    /// Start of region allocations
    #[allow(dead_code)]
    start_ptr: u32,
}

impl Codegen {
    pub fn new() -> Self {
        Self {
            bump_ptr: REGION_HEADER_SIZE,
            region_stack: Vec::new(),
            module: Module::new(),
        }
    }

    /// Generate the complete WASM module
    pub fn generate(&mut self) -> Vec<u8> {
        self.emit_types();
        self.emit_memory();
        self.emit_runtime_functions();
        self.emit_exports();
        self.module.clone().finish()
    }

    fn emit_types(&mut self) {
        let mut types = TypeSection::new();

        // Type 0: () -> i32 (allocator, getters)
        types.ty().function(vec![], vec![ValType::I32]);

        // Type 1: (i32) -> () (free, setters)
        types.ty().function(vec![ValType::I32], vec![]);

        // Type 2: (i32, i32) -> i32 (string ops with ptr+len)
        types
            .ty()
            .function(vec![ValType::I32, ValType::I32], vec![ValType::I32]);

        // Type 3: (i32, i32, i32, i32) -> i64 (string concat)
        types.ty().function(
            vec![ValType::I32, ValType::I32, ValType::I32, ValType::I32],
            vec![ValType::I64],
        );

        // Type 4: () -> () (region management)
        types.ty().function(vec![], vec![]);

        self.module.section(&types);
    }

    fn emit_memory(&mut self) {
        let mut memories = MemorySection::new();
        memories.memory(MemoryType {
            minimum: INITIAL_PAGES,
            maximum: Some(MAX_PAGES),
            memory64: false,
            shared: false,
            page_size_log2: None,
        });
        self.module.section(&memories);
    }

    fn emit_runtime_functions(&mut self) {
        let mut functions = FunctionSection::new();
        let mut code = CodeSection::new();

        // Function 0: __ephapax_bump_alloc(size: i32) -> ptr: i32
        functions.function(2);
        code.function(&self.gen_bump_alloc());

        // Function 1: __ephapax_string_new(ptr: i32, len: i32) -> handle: i32
        functions.function(2);
        code.function(&self.gen_string_new());

        // Function 2: __ephapax_string_len(handle: i32) -> len: i32
        functions.function(2);
        code.function(&self.gen_string_len());

        // Function 3: __ephapax_string_concat(h1: i32, h2: i32) -> handle: i32
        functions.function(2);
        code.function(&self.gen_string_concat());

        // Function 4: __ephapax_string_drop(handle: i32)
        functions.function(1);
        code.function(&self.gen_string_drop());

        // Function 5: __ephapax_region_enter()
        functions.function(4);
        code.function(&self.gen_region_enter());

        // Function 6: __ephapax_region_exit()
        functions.function(4);
        code.function(&self.gen_region_exit());

        self.module.section(&functions);
        self.module.section(&code);
    }

    /// Bump allocator: advances pointer, returns old value
    fn gen_bump_alloc(&self) -> Function {
        let mut f = Function::new(vec![(1, ValType::I32)]); // local for old_ptr

        // old_ptr = global.get $bump_ptr
        f.instruction(&Instruction::I32Const(0)); // Address of bump_ptr global
        f.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));
        f.instruction(&Instruction::LocalSet(2)); // Store in local

        // global.set $bump_ptr (old_ptr + size)
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::LocalGet(2)); // old_ptr
        f.instruction(&Instruction::LocalGet(0)); // size parameter
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));

        // return old_ptr
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::End);

        f
    }

    /// String allocation: copies data and returns handle
    fn gen_string_new(&self) -> Function {
        let mut f = Function::new(vec![(1, ValType::I32)]); // local for handle

        // Allocate space for string header (ptr + len = 8 bytes)
        f.instruction(&Instruction::I32Const(STRING_SIZE as i32));
        f.instruction(&Instruction::I32Const(0)); // dummy second param
        f.instruction(&Instruction::Call(0)); // __ephapax_bump_alloc
        f.instruction(&Instruction::LocalSet(2)); // handle

        // Store ptr at handle
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::LocalGet(0)); // ptr param
        f.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));

        // Store len at handle + 4
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::LocalGet(1)); // len param
        f.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
            offset: 4,
            align: 2,
            memory_index: 0,
        }));

        // Return handle
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::End);

        f
    }

    /// Get string length from handle
    fn gen_string_len(&self) -> Function {
        let mut f = Function::new(vec![]);

        // Load len from handle + 4
        f.instruction(&Instruction::LocalGet(0)); // handle
        f.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 4,
            align: 2,
            memory_index: 0,
        }));
        f.instruction(&Instruction::End);

        f
    }

    /// Concatenate two strings (consumes both handles)
    fn gen_string_concat(&self) -> Function {
        let mut f = Function::new(vec![
            (1, ValType::I32), // ptr1
            (1, ValType::I32), // len1
            (1, ValType::I32), // ptr2
            (1, ValType::I32), // len2
            (1, ValType::I32), // new_ptr
            (1, ValType::I32), // new_handle
        ]);

        // Load ptr1, len1 from handle1
        f.instruction(&Instruction::LocalGet(0)); // handle1
        f.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));
        f.instruction(&Instruction::LocalSet(2)); // ptr1

        f.instruction(&Instruction::LocalGet(0));
        f.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 4,
            align: 2,
            memory_index: 0,
        }));
        f.instruction(&Instruction::LocalSet(3)); // len1

        // Load ptr2, len2 from handle2
        f.instruction(&Instruction::LocalGet(1)); // handle2
        f.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));
        f.instruction(&Instruction::LocalSet(4)); // ptr2

        f.instruction(&Instruction::LocalGet(1));
        f.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 4,
            align: 2,
            memory_index: 0,
        }));
        f.instruction(&Instruction::LocalSet(5)); // len2

        // Allocate new buffer: len1 + len2
        f.instruction(&Instruction::LocalGet(3)); // len1
        f.instruction(&Instruction::LocalGet(5)); // len2
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::Call(0)); // __ephapax_bump_alloc
        f.instruction(&Instruction::LocalSet(6)); // new_ptr

        // memory.copy: dest=new_ptr, src=ptr1, len=len1
        f.instruction(&Instruction::LocalGet(6));
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::LocalGet(3));
        f.instruction(&Instruction::MemoryCopy {
            src_mem: 0,
            dst_mem: 0,
        });

        // memory.copy: dest=new_ptr+len1, src=ptr2, len=len2
        f.instruction(&Instruction::LocalGet(6));
        f.instruction(&Instruction::LocalGet(3));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::LocalGet(4));
        f.instruction(&Instruction::LocalGet(5));
        f.instruction(&Instruction::MemoryCopy {
            src_mem: 0,
            dst_mem: 0,
        });

        // Allocate new handle
        f.instruction(&Instruction::I32Const(STRING_SIZE as i32));
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::Call(0));
        f.instruction(&Instruction::LocalSet(7)); // new_handle

        // Store ptr in new handle
        f.instruction(&Instruction::LocalGet(7));
        f.instruction(&Instruction::LocalGet(6));
        f.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));

        // Store len in new handle
        f.instruction(&Instruction::LocalGet(7));
        f.instruction(&Instruction::LocalGet(3));
        f.instruction(&Instruction::LocalGet(5));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
            offset: 4,
            align: 2,
            memory_index: 0,
        }));

        // Return new handle
        f.instruction(&Instruction::LocalGet(7));
        f.instruction(&Instruction::End);

        f
    }

    /// Drop a string handle (no-op in bump allocator, freed on region exit)
    fn gen_string_drop(&self) -> Function {
        let mut f = Function::new(vec![]);
        // In a bump allocator with regions, individual drops are no-ops
        // Memory is reclaimed when the region exits
        f.instruction(&Instruction::End);
        f
    }

    /// Enter a new region: save current bump pointer
    fn gen_region_enter(&self) -> Function {
        let mut f = Function::new(vec![]);

        // Push current bump_ptr to region stack (at fixed location)
        // Region stack at offset 4, stack pointer at offset 8
        f.instruction(&Instruction::I32Const(8)); // region_sp address
        f.instruction(&Instruction::I32Const(8));
        f.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));
        f.instruction(&Instruction::I32Const(4));
        f.instruction(&Instruction::I32Add); // new_sp = old_sp + 4

        // Store current bump_ptr at stack[new_sp]
        f.instruction(&Instruction::I32Const(0)); // bump_ptr address
        f.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));
        f.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));

        f.instruction(&Instruction::End);
        f
    }

    /// Exit region: restore bump pointer (frees all region allocations)
    fn gen_region_exit(&self) -> Function {
        let mut f = Function::new(vec![(1, ValType::I32)]); // local for saved_ptr

        // Pop from region stack
        f.instruction(&Instruction::I32Const(8)); // region_sp address
        f.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));
        f.instruction(&Instruction::LocalTee(0)); // sp

        // Load saved bump_ptr
        f.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));

        // Restore bump_ptr
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));

        // Decrement region_sp
        f.instruction(&Instruction::I32Const(8));
        f.instruction(&Instruction::LocalGet(0));
        f.instruction(&Instruction::I32Const(4));
        f.instruction(&Instruction::I32Sub);
        f.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));

        f.instruction(&Instruction::End);
        f
    }

    fn emit_exports(&mut self) {
        let mut exports = ExportSection::new();
        exports.export("__ephapax_bump_alloc", ExportKind::Func, 0);
        exports.export("__ephapax_string_new", ExportKind::Func, 1);
        exports.export("__ephapax_string_len", ExportKind::Func, 2);
        exports.export("__ephapax_string_concat", ExportKind::Func, 3);
        exports.export("__ephapax_string_drop", ExportKind::Func, 4);
        exports.export("__ephapax_region_enter", ExportKind::Func, 5);
        exports.export("__ephapax_region_exit", ExportKind::Func, 6);
        exports.export("memory", ExportKind::Memory, 0);
        self.module.section(&exports);
    }
}

impl Default for Codegen {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generates_valid_wasm() {
        let mut codegen = Codegen::new();
        let wasm = codegen.generate();

        // Basic validation: WASM magic number
        assert_eq!(&wasm[0..4], b"\x00asm");
        // Version 1
        assert_eq!(&wasm[4..8], &[1, 0, 0, 0]);
    }
}
