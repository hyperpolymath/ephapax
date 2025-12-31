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

use ephapax_syntax::{BaseTy, BinOp, Expr, ExprKind, Literal, Ty, UnaryOp};
use std::collections::HashMap;
use wasm_encoder::{
    CodeSection, ExportKind, ExportSection, Function, FunctionSection, ImportSection, Instruction,
    MemorySection, MemoryType, Module, TypeSection, ValType,
};

/// WASM representation of a string: (pointer, length)
pub const STRING_SIZE: u32 = 8; // 2 x i32

/// Region metadata size
pub const REGION_HEADER_SIZE: u32 = 16;

/// Initial memory pages (64KB each)
pub const INITIAL_PAGES: u64 = 1;

/// Maximum memory pages
pub const MAX_PAGES: u64 = 256; // 16MB max

/// Function indices after imports
const IMPORT_PRINT_I32: u32 = 0;
const IMPORT_PRINT_STRING: u32 = 1;

/// Runtime function indices (offset by number of imports)
const FN_BUMP_ALLOC: u32 = 2;
const FN_STRING_NEW: u32 = 3;
const FN_STRING_LEN: u32 = 4;
const FN_STRING_CONCAT: u32 = 5;
const FN_STRING_DROP: u32 = 6;
const FN_REGION_ENTER: u32 = 7;
const FN_REGION_EXIT: u32 = 8;

/// Code generator state
pub struct Codegen {
    /// Current bump pointer for allocations (reserved for future interpreter use)
    #[allow(dead_code)]
    bump_ptr: u32,
    /// Region stack for tracking active regions (reserved for future interpreter use)
    #[allow(dead_code)]
    region_stack: Vec<RegionInfo>,
    /// Generated WASM module
    module: Module,
    /// Variable to local index mapping for current function
    locals: HashMap<String, u32>,
    /// Next local index
    next_local: u32,
    /// Data section entries for string literals
    data_entries: Vec<(u32, Vec<u8>)>,
    /// Next data offset
    data_offset: u32,
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
            locals: HashMap::new(),
            next_local: 0,
            data_entries: Vec::new(),
            data_offset: 1024, // Start string data after metadata area
        }
    }

    /// Generate the complete WASM module
    pub fn generate(&mut self) -> Vec<u8> {
        self.emit_types();
        self.emit_imports();
        self.emit_memory();
        self.emit_runtime_functions();
        self.emit_exports();
        self.emit_data_section();
        self.module.clone().finish()
    }

    /// Generate a complete WASM module with a main expression
    pub fn compile_program(&mut self, main_expr: &Expr) -> Vec<u8> {
        self.emit_types();
        self.emit_imports();
        self.emit_memory();
        self.emit_runtime_functions();
        self.emit_main_function(main_expr);
        self.emit_exports();
        self.emit_data_section();
        self.module.clone().finish()
    }

    fn emit_types(&mut self) {
        let mut types = TypeSection::new();

        // Type 0: () -> i32 (allocator, getters)
        types.ty().function(vec![], vec![ValType::I32]);

        // Type 1: (i32) -> () (print_i32, free, setters)
        types.ty().function(vec![ValType::I32], vec![]);

        // Type 2: (i32, i32) -> () (print_string: ptr, len)
        types.ty().function(vec![ValType::I32, ValType::I32], vec![]);

        // Type 3: (i32, i32) -> i32 (string ops with ptr+len)
        types.ty().function(vec![ValType::I32, ValType::I32], vec![ValType::I32]);

        // Type 4: () -> () (region management, main)
        types.ty().function(vec![], vec![]);

        // Type 5: (i32, i32, i32, i32) -> i64 (string concat)
        types.ty().function(
            vec![ValType::I32, ValType::I32, ValType::I32, ValType::I32],
            vec![ValType::I64],
        );

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

        // Function indices offset by 2 imports
        // Function 2: __ephapax_bump_alloc(size: i32) -> ptr: i32
        functions.function(3); // Type 3: (i32, i32) -> i32
        code.function(&self.gen_bump_alloc());

        // Function 3: __ephapax_string_new(ptr: i32, len: i32) -> handle: i32
        functions.function(3); // Type 3: (i32, i32) -> i32
        code.function(&self.gen_string_new());

        // Function 4: __ephapax_string_len(handle: i32) -> len: i32
        functions.function(3); // Type 3: (i32, i32) -> i32 (first param is handle)
        code.function(&self.gen_string_len());

        // Function 5: __ephapax_string_concat(h1: i32, h2: i32) -> handle: i32
        functions.function(3); // Type 3: (i32, i32) -> i32
        code.function(&self.gen_string_concat());

        // Function 6: __ephapax_string_drop(handle: i32)
        functions.function(1); // Type 1: (i32) -> ()
        code.function(&self.gen_string_drop());

        // Function 7: __ephapax_region_enter()
        functions.function(4); // Type 4: () -> ()
        code.function(&self.gen_region_enter());

        // Function 8: __ephapax_region_exit()
        functions.function(4); // Type 4: () -> ()
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
        exports.export("__ephapax_bump_alloc", ExportKind::Func, FN_BUMP_ALLOC);
        exports.export("__ephapax_string_new", ExportKind::Func, FN_STRING_NEW);
        exports.export("__ephapax_string_len", ExportKind::Func, FN_STRING_LEN);
        exports.export("__ephapax_string_concat", ExportKind::Func, FN_STRING_CONCAT);
        exports.export("__ephapax_string_drop", ExportKind::Func, FN_STRING_DROP);
        exports.export("__ephapax_region_enter", ExportKind::Func, FN_REGION_ENTER);
        exports.export("__ephapax_region_exit", ExportKind::Func, FN_REGION_EXIT);
        exports.export("memory", ExportKind::Memory, 0);
        self.module.section(&exports);
    }

    fn emit_imports(&mut self) {
        let mut imports = ImportSection::new();
        // Import print functions from host environment
        // Type 1: (i32) -> () for print_i32
        imports.import("env", "print_i32", wasm_encoder::EntityType::Function(1));
        // Type 2: (i32, i32) -> () for print_string (ptr, len)
        imports.import("env", "print_string", wasm_encoder::EntityType::Function(2));
        self.module.section(&imports);
    }

    fn emit_data_section(&mut self) {
        if self.data_entries.is_empty() {
            return;
        }
        let mut data = wasm_encoder::DataSection::new();
        for (offset, bytes) in &self.data_entries {
            data.active(
                0, // memory index
                &wasm_encoder::ConstExpr::i32_const(*offset as i32),
                bytes.iter().copied(),
            );
        }
        self.module.section(&data);
    }

    /// Add a string literal to the data section, return (ptr, len)
    fn add_string_literal(&mut self, s: &str) -> (u32, u32) {
        let bytes = s.as_bytes().to_vec();
        let len = bytes.len() as u32;
        let ptr = self.data_offset;
        self.data_entries.push((ptr, bytes));
        self.data_offset += len;
        // Align to 4 bytes
        if self.data_offset % 4 != 0 {
            self.data_offset += 4 - (self.data_offset % 4);
        }
        (ptr, len)
    }

    /// Emit the main function with the given expression
    fn emit_main_function(&mut self, expr: &Expr) {
        let mut functions = FunctionSection::new();
        let mut code = CodeSection::new();

        // Main function: type 4 () -> ()
        functions.function(4);

        // Reset locals for this function
        self.locals.clear();
        self.next_local = 0;

        // Compile the expression
        let mut func = Function::new(vec![]);
        self.compile_expr(&mut func, expr);

        // If expression returns a value, we need to drop it or print it
        // For now, assume we want to print the result
        func.instruction(&Instruction::Drop);
        func.instruction(&Instruction::End);

        code.function(&func);

        self.module.section(&functions);
        self.module.section(&code);
    }

    /// Compile an expression into WASM instructions
    pub fn compile_expr(&mut self, func: &mut Function, expr: &Expr) {
        match &expr.kind {
            ExprKind::Lit(lit) => self.compile_lit(func, lit),
            ExprKind::Var(name) => self.compile_var(func, name),
            ExprKind::StringNew { region: _, value } => self.compile_string_new(func, value),
            ExprKind::StringConcat { left, right } => self.compile_string_concat(func, left, right),
            ExprKind::StringLen(inner) => self.compile_string_len(func, inner),
            ExprKind::Let { name, value, body, .. } => self.compile_let(func, name, value, body),
            ExprKind::LetLin { name, value, body, .. } => self.compile_let(func, name, value, body),
            ExprKind::Lambda { .. } => {
                // Lambdas need closure conversion - simplified for now
                func.instruction(&Instruction::I32Const(0));
            }
            ExprKind::App { func: fn_expr, arg } => self.compile_app(func, fn_expr, arg),
            ExprKind::Pair { left, right } => self.compile_pair(func, left, right),
            ExprKind::Fst(inner) => self.compile_fst(func, inner),
            ExprKind::Snd(inner) => self.compile_snd(func, inner),
            ExprKind::Inl { value, .. } => self.compile_inl(func, value),
            ExprKind::Inr { value, .. } => self.compile_inr(func, value),
            ExprKind::Case { scrutinee, left_var, left_body, right_var, right_body } => {
                self.compile_case(func, scrutinee, left_var, left_body, right_var, right_body)
            }
            ExprKind::If { cond, then_branch, else_branch } => {
                self.compile_if(func, cond, then_branch, else_branch)
            }
            ExprKind::Region { name: _, body } => self.compile_region(func, body),
            ExprKind::Borrow(inner) => {
                // Borrow just passes through the value (second-class, same representation)
                self.compile_expr(func, inner);
            }
            ExprKind::Deref(inner) => {
                // Deref just passes through
                self.compile_expr(func, inner);
            }
            ExprKind::Drop(inner) => {
                self.compile_expr(func, inner);
                func.instruction(&Instruction::Drop);
                func.instruction(&Instruction::I32Const(0)); // Return unit (0)
            }
            ExprKind::Copy(inner) => {
                // For unrestricted types, just duplicate the value
                self.compile_expr(func, inner);
                // The value is now on the stack; to copy we'd need to dup
                // For i32, we can use local.tee
            }
            ExprKind::Block(exprs) => self.compile_block(func, exprs),
            ExprKind::BinOp { op, left, right } => self.compile_binop(func, *op, left, right),
            ExprKind::UnaryOp { op, operand } => self.compile_unaryop(func, *op, operand),
        }
    }

    fn compile_lit(&self, func: &mut Function, lit: &Literal) {
        match lit {
            Literal::Unit => func.instruction(&Instruction::I32Const(0)),
            Literal::Bool(b) => func.instruction(&Instruction::I32Const(if *b { 1 } else { 0 })),
            Literal::I32(n) => func.instruction(&Instruction::I32Const(*n)),
            Literal::I64(n) => func.instruction(&Instruction::I64Const(*n)),
            Literal::F32(n) => func.instruction(&Instruction::F32Const(*n)),
            Literal::F64(n) => func.instruction(&Instruction::F64Const(*n)),
            Literal::String(_) => {
                // String literals should use StringNew
                func.instruction(&Instruction::I32Const(0))
            }
        };
    }

    fn compile_var(&self, func: &mut Function, name: &str) {
        if let Some(&local_idx) = self.locals.get(name) {
            func.instruction(&Instruction::LocalGet(local_idx));
        } else {
            // Variable not found - should have been caught by type checker
            func.instruction(&Instruction::Unreachable);
        }
    }

    fn compile_string_new(&mut self, func: &mut Function, value: &str) {
        let (ptr, len) = self.add_string_literal(value);
        func.instruction(&Instruction::I32Const(ptr as i32));
        func.instruction(&Instruction::I32Const(len as i32));
        func.instruction(&Instruction::Call(FN_STRING_NEW));
    }

    fn compile_string_concat(&mut self, func: &mut Function, left: &Expr, right: &Expr) {
        self.compile_expr(func, left);
        self.compile_expr(func, right);
        func.instruction(&Instruction::Call(FN_STRING_CONCAT));
    }

    fn compile_string_len(&mut self, func: &mut Function, inner: &Expr) {
        self.compile_expr(func, inner);
        func.instruction(&Instruction::Call(FN_STRING_LEN));
    }

    fn compile_let(&mut self, func: &mut Function, name: &str, value: &Expr, body: &Expr) {
        // Compile the value
        self.compile_expr(func, value);

        // Store in a local
        let local_idx = self.next_local;
        self.next_local += 1;
        self.locals.insert(name.to_string(), local_idx);
        func.instruction(&Instruction::LocalSet(local_idx));

        // Compile the body
        self.compile_expr(func, body);
    }

    fn compile_app(&mut self, func: &mut Function, _fn_expr: &Expr, _arg: &Expr) {
        // Function application - requires closure conversion
        // For now, simplified
        func.instruction(&Instruction::I32Const(0));
    }

    fn compile_pair(&mut self, func: &mut Function, left: &Expr, right: &Expr) {
        // Allocate space for pair (2 x i32 = 8 bytes)
        func.instruction(&Instruction::I32Const(8));
        func.instruction(&Instruction::Call(FN_BUMP_ALLOC));

        // Store left at offset 0
        let pair_local = self.next_local;
        self.next_local += 1;
        func.instruction(&Instruction::LocalTee(pair_local));
        self.compile_expr(func, left);
        func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));

        // Store right at offset 4
        func.instruction(&Instruction::LocalGet(pair_local));
        self.compile_expr(func, right);
        func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
            offset: 4,
            align: 2,
            memory_index: 0,
        }));

        // Return pair pointer
        func.instruction(&Instruction::LocalGet(pair_local));
    }

    fn compile_fst(&mut self, func: &mut Function, inner: &Expr) {
        self.compile_expr(func, inner);
        func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));
    }

    fn compile_snd(&mut self, func: &mut Function, inner: &Expr) {
        self.compile_expr(func, inner);
        func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 4,
            align: 2,
            memory_index: 0,
        }));
    }

    fn compile_inl(&mut self, func: &mut Function, value: &Expr) {
        // Sum types: tag (i32) + value (i32) = 8 bytes
        func.instruction(&Instruction::I32Const(8));
        func.instruction(&Instruction::Call(FN_BUMP_ALLOC));

        let sum_local = self.next_local;
        self.next_local += 1;
        func.instruction(&Instruction::LocalTee(sum_local));

        // Store tag 0 for left
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));

        // Store value
        func.instruction(&Instruction::LocalGet(sum_local));
        self.compile_expr(func, value);
        func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
            offset: 4,
            align: 2,
            memory_index: 0,
        }));

        func.instruction(&Instruction::LocalGet(sum_local));
    }

    fn compile_inr(&mut self, func: &mut Function, value: &Expr) {
        func.instruction(&Instruction::I32Const(8));
        func.instruction(&Instruction::Call(FN_BUMP_ALLOC));

        let sum_local = self.next_local;
        self.next_local += 1;
        func.instruction(&Instruction::LocalTee(sum_local));

        // Store tag 1 for right
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));

        func.instruction(&Instruction::LocalGet(sum_local));
        self.compile_expr(func, value);
        func.instruction(&Instruction::I32Store(wasm_encoder::MemArg {
            offset: 4,
            align: 2,
            memory_index: 0,
        }));

        func.instruction(&Instruction::LocalGet(sum_local));
    }

    fn compile_case(
        &mut self,
        func: &mut Function,
        scrutinee: &Expr,
        left_var: &str,
        left_body: &Expr,
        right_var: &str,
        right_body: &Expr,
    ) {
        self.compile_expr(func, scrutinee);

        let scrutinee_local = self.next_local;
        self.next_local += 1;
        func.instruction(&Instruction::LocalTee(scrutinee_local));

        // Load tag
        func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 0,
            align: 2,
            memory_index: 0,
        }));

        // If tag == 0, execute left branch, else right branch
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Result(ValType::I32)));

        // Right branch (tag != 0)
        func.instruction(&Instruction::LocalGet(scrutinee_local));
        func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 4,
            align: 2,
            memory_index: 0,
        }));
        let right_local = self.next_local;
        self.next_local += 1;
        self.locals.insert(right_var.to_string(), right_local);
        func.instruction(&Instruction::LocalSet(right_local));
        self.compile_expr(func, right_body);

        func.instruction(&Instruction::Else);

        // Left branch (tag == 0)
        func.instruction(&Instruction::LocalGet(scrutinee_local));
        func.instruction(&Instruction::I32Load(wasm_encoder::MemArg {
            offset: 4,
            align: 2,
            memory_index: 0,
        }));
        let left_local = self.next_local;
        self.next_local += 1;
        self.locals.insert(left_var.to_string(), left_local);
        func.instruction(&Instruction::LocalSet(left_local));
        self.compile_expr(func, left_body);

        func.instruction(&Instruction::End);
    }

    fn compile_if(&mut self, func: &mut Function, cond: &Expr, then_branch: &Expr, else_branch: &Expr) {
        self.compile_expr(func, cond);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Result(ValType::I32)));
        self.compile_expr(func, then_branch);
        func.instruction(&Instruction::Else);
        self.compile_expr(func, else_branch);
        func.instruction(&Instruction::End);
    }

    fn compile_region(&mut self, func: &mut Function, body: &Expr) {
        // Enter region
        func.instruction(&Instruction::Call(FN_REGION_ENTER));

        // Compile body
        self.compile_expr(func, body);

        // Exit region (frees all allocations)
        func.instruction(&Instruction::Call(FN_REGION_EXIT));
    }

    fn compile_block(&mut self, func: &mut Function, exprs: &[Expr]) {
        if exprs.is_empty() {
            func.instruction(&Instruction::I32Const(0)); // Unit
            return;
        }

        for (i, expr) in exprs.iter().enumerate() {
            self.compile_expr(func, expr);
            if i < exprs.len() - 1 {
                func.instruction(&Instruction::Drop);
            }
        }
    }

    fn compile_binop(&mut self, func: &mut Function, op: BinOp, left: &Expr, right: &Expr) {
        self.compile_expr(func, left);
        self.compile_expr(func, right);

        match op {
            BinOp::Add => { func.instruction(&Instruction::I32Add); }
            BinOp::Sub => { func.instruction(&Instruction::I32Sub); }
            BinOp::Mul => { func.instruction(&Instruction::I32Mul); }
            BinOp::Div => { func.instruction(&Instruction::I32DivS); }
            BinOp::Mod => { func.instruction(&Instruction::I32RemS); }
            BinOp::Lt => { func.instruction(&Instruction::I32LtS); }
            BinOp::Le => { func.instruction(&Instruction::I32LeS); }
            BinOp::Gt => { func.instruction(&Instruction::I32GtS); }
            BinOp::Ge => { func.instruction(&Instruction::I32GeS); }
            BinOp::Eq => { func.instruction(&Instruction::I32Eq); }
            BinOp::Ne => { func.instruction(&Instruction::I32Ne); }
            BinOp::And => { func.instruction(&Instruction::I32And); }
            BinOp::Or => { func.instruction(&Instruction::I32Or); }
        }
    }

    fn compile_unaryop(&mut self, func: &mut Function, op: UnaryOp, operand: &Expr) {
        match op {
            UnaryOp::Not => {
                self.compile_expr(func, operand);
                func.instruction(&Instruction::I32Eqz);
            }
            UnaryOp::Neg => {
                // For negation: compute 0 - operand
                // Push 0 first, then the operand, then subtract
                func.instruction(&Instruction::I32Const(0));
                self.compile_expr(func, operand);
                func.instruction(&Instruction::I32Sub);
            }
        }
    }

    /// Compile a "Hello World" program that prints a string
    pub fn compile_hello_world(&mut self, message: &str) -> Vec<u8> {
        self.emit_types();
        self.emit_imports();
        self.emit_memory();
        self.emit_runtime_hello_world(message);
        self.emit_exports_with_main();
        self.emit_data_section();
        self.module.clone().finish()
    }

    fn emit_runtime_hello_world(&mut self, message: &str) {
        let mut functions = FunctionSection::new();
        let mut code = CodeSection::new();

        // Add the runtime functions first (7 functions, indices 2-8)
        functions.function(3); code.function(&self.gen_bump_alloc());
        functions.function(3); code.function(&self.gen_string_new());
        functions.function(3); code.function(&self.gen_string_len());
        functions.function(3); code.function(&self.gen_string_concat());
        functions.function(1); code.function(&self.gen_string_drop());
        functions.function(4); code.function(&self.gen_region_enter());
        functions.function(4); code.function(&self.gen_region_exit());

        // Main function (function index 9 = 2 imports + 7 runtime)
        functions.function(4); // Type 4: () -> ()

        let (ptr, len) = self.add_string_literal(message);
        let mut main_func = Function::new(vec![]);
        main_func.instruction(&Instruction::I32Const(ptr as i32));
        main_func.instruction(&Instruction::I32Const(len as i32));
        main_func.instruction(&Instruction::Call(IMPORT_PRINT_STRING));
        main_func.instruction(&Instruction::End);
        code.function(&main_func);

        self.module.section(&functions);
        self.module.section(&code);
    }

    fn emit_exports_with_main(&mut self) {
        let mut exports = ExportSection::new();
        exports.export("__ephapax_bump_alloc", ExportKind::Func, FN_BUMP_ALLOC);
        exports.export("__ephapax_string_new", ExportKind::Func, FN_STRING_NEW);
        exports.export("__ephapax_string_len", ExportKind::Func, FN_STRING_LEN);
        exports.export("__ephapax_string_concat", ExportKind::Func, FN_STRING_CONCAT);
        exports.export("__ephapax_string_drop", ExportKind::Func, FN_STRING_DROP);
        exports.export("__ephapax_region_enter", ExportKind::Func, FN_REGION_ENTER);
        exports.export("__ephapax_region_exit", ExportKind::Func, FN_REGION_EXIT);
        exports.export("memory", ExportKind::Memory, 0);
        exports.export("main", ExportKind::Func, 9); // Main is function index 9
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
    use ephapax_syntax::Span;

    #[test]
    fn generates_valid_wasm() {
        let mut codegen = Codegen::new();
        let wasm = codegen.generate();

        // Basic validation: WASM magic number
        assert_eq!(&wasm[0..4], b"\x00asm");
        // Version 1
        assert_eq!(&wasm[4..8], &[1, 0, 0, 0]);
    }

    #[test]
    fn hello_world_generates_valid_wasm() {
        let mut codegen = Codegen::new();
        let wasm = codegen.compile_hello_world("Hello, Ephapax!");

        // Basic validation: WASM magic number
        assert_eq!(&wasm[0..4], b"\x00asm");
        // Version 1
        assert_eq!(&wasm[4..8], &[1, 0, 0, 0]);

        // Wasm should have sections for types, imports, functions, memory, exports, code, data
        assert!(wasm.len() > 100, "WASM too small: {} bytes", wasm.len());
    }

    #[test]
    fn compile_literal_expression() {
        let mut codegen = Codegen::new();

        // Create a simple expression: 42
        let expr = Expr::new(
            ExprKind::Lit(Literal::I32(42)),
            Span::dummy(),
        );

        let wasm = codegen.compile_program(&expr);

        // Basic validation: WASM magic number
        assert_eq!(&wasm[0..4], b"\x00asm");
    }

    #[test]
    fn compile_arithmetic_expression() {
        let mut codegen = Codegen::new();

        // Create expression: 1 + 2
        let expr = Expr::new(
            ExprKind::BinOp {
                op: BinOp::Add,
                left: Box::new(Expr::new(
                    ExprKind::Lit(Literal::I32(1)),
                    Span::dummy(),
                )),
                right: Box::new(Expr::new(
                    ExprKind::Lit(Literal::I32(2)),
                    Span::dummy(),
                )),
            },
            Span::dummy(),
        );

        let wasm = codegen.compile_program(&expr);

        // Basic validation: WASM magic number
        assert_eq!(&wasm[0..4], b"\x00asm");
    }

    #[test]
    fn compile_if_expression() {
        let mut codegen = Codegen::new();

        // Create expression: if true then 1 else 2
        let expr = Expr::new(
            ExprKind::If {
                cond: Box::new(Expr::new(
                    ExprKind::Lit(Literal::Bool(true)),
                    Span::dummy(),
                )),
                then_branch: Box::new(Expr::new(
                    ExprKind::Lit(Literal::I32(1)),
                    Span::dummy(),
                )),
                else_branch: Box::new(Expr::new(
                    ExprKind::Lit(Literal::I32(2)),
                    Span::dummy(),
                )),
            },
            Span::dummy(),
        );

        let wasm = codegen.compile_program(&expr);

        // Basic validation: WASM magic number
        assert_eq!(&wasm[0..4], b"\x00asm");
    }

    #[test]
    fn compile_let_expression() {
        let mut codegen = Codegen::new();

        // Create expression: let x = 42 in x
        let expr = Expr::new(
            ExprKind::Let {
                name: "x".into(),
                ty: None,
                value: Box::new(Expr::new(
                    ExprKind::Lit(Literal::I32(42)),
                    Span::dummy(),
                )),
                body: Box::new(Expr::new(
                    ExprKind::Var("x".into()),
                    Span::dummy(),
                )),
            },
            Span::dummy(),
        );

        let wasm = codegen.compile_program(&expr);

        // Basic validation: WASM magic number
        assert_eq!(&wasm[0..4], b"\x00asm");
    }
}
