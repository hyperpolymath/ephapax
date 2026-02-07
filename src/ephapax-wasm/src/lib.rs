// SPDX-License-Identifier: PMPL-1.0-or-later
//! SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax WASM Code Generator (Dyadic: Affine + Linear modes)
//!
//! Compiles Ephapax AST / IR to WebAssembly with explicit memory management
//! and dyadic type lowering (affine or linear).
//!
//! ## Architecture
//!
//! The code generator works in two phases:
//!
//! 1. **Collection** -- gather all top-level function declarations, assign WASM
//!    function indices, and build the WASM type section.
//! 2. **Emission** -- compile each function body to WASM instructions, emitting
//!    proper local declarations, control flow, and resource management.
//!
//! ## String Representation
//!
//! Strings are represented as `(ptr: i32, len: i32)` pairs in linear memory.
//! The `ptr` points to UTF-8 encoded bytes.
//!
//! ## Memory Layout
//!
//! ```text
//! +------------------+
//! | Region Metadata  |  <- 0x0000  (bump_ptr at 0, region_sp at 8)
//! +------------------+
//! | String Data      |  <- bump allocated (starts at 1024)
//! +------------------+
//! | Free Space       |
//! +------------------+
//! | Stack (grows down)|  <- top of memory
//! +------------------+
//! ```
//!
//! ## Dyadic Type Lowering
//!
//! The code generator supports both affine and linear modes:
//!
//! - **Linear mode**: Use-once values tracked at compile time. Explicit drops required.
//! - **Affine mode**: Use-at-most-once values. Implicit drops allowed at scope exit.
//!
//! Mode is set per-module compilation and affects how unused linear values are handled.

use ephapax_ir::module_from_sexpr;
use ephapax_syntax::{
    BaseTy, BinOp, Decl, Expr, ExprKind, Literal, Module as AstModule, Ty, UnaryOp,
};
use std::collections::HashMap;
use wasm_encoder::{
    CodeSection, ConstExpr, ElementSection, Elements, ExportKind, ExportSection, Function,
    FunctionSection, ImportSection, Instruction, MemorySection, MemoryType, Module as WasmModule,
    RefType, TableSection, TableType, TypeSection, ValType,
};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// WASM representation of a string: (pointer, length)
pub const STRING_SIZE: u32 = 8; // 2 x i32

/// Region metadata size (bump_ptr + padding + region_sp + padding)
pub const REGION_HEADER_SIZE: u32 = 16;

/// Initial memory pages (64 KiB each)
pub const INITIAL_PAGES: u64 = 1;

/// Maximum memory pages (16 MiB)
pub const MAX_PAGES: u64 = 256;

// ---------------------------------------------------------------------------
// Fixed function indices -- these are *after* the 2 host imports.
// ---------------------------------------------------------------------------

/// Number of host imports (print_i32, print_string)
const NUM_IMPORTS: u32 = 2;

/// Indices of the 7 built-in runtime helpers (2..8 inclusive)
const FN_BUMP_ALLOC: u32 = 2;
const FN_STRING_NEW: u32 = 3;
const FN_STRING_LEN: u32 = 4;
const FN_STRING_CONCAT: u32 = 5;
const FN_STRING_DROP: u32 = 6;
const FN_REGION_ENTER: u32 = 7;
const FN_REGION_EXIT: u32 = 8;

/// Number of runtime helper functions
const NUM_RUNTIME_FNS: u32 = 7;

/// First user function index
const FIRST_USER_FN: u32 = NUM_IMPORTS + NUM_RUNTIME_FNS; // 9

// ---------------------------------------------------------------------------
// Well-known WASM type indices
// ---------------------------------------------------------------------------

/// Type 0: `() -> i32`
const TYPE_VOID_I32: u32 = 0;
/// Type 1: `(i32) -> ()`
const TYPE_I32_VOID: u32 = 1;
/// Type 2: `(i32, i32) -> ()`
const TYPE_I32_I32_VOID: u32 = 2;
/// Type 3: `(i32, i32) -> i32`
const TYPE_I32_I32_I32: u32 = 3;
/// Type 4: `() -> ()`
const TYPE_VOID_VOID: u32 = 4;
/// Type 5: `(i32, i32, i32, i32) -> i64`
#[allow(dead_code)]
const TYPE_CONCAT: u32 = 5;
/// Type 6: `(i32) -> i32`   (single-param unary functions)
const TYPE_I32_TO_I32: u32 = 6;

/// Number of fixed type entries in the type section.
const NUM_FIXED_TYPES: u32 = 7;

// ---------------------------------------------------------------------------
// Compilation mode (dyadic design)
// ---------------------------------------------------------------------------

/// Compilation mode for dyadic type system
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Mode {
    /// Affine mode: use ≤1 time (implicit drops allowed)
    Affine,
    /// Linear mode: use exactly 1 time (no implicit drops)
    Linear,
}

impl Default for Mode {
    fn default() -> Self {
        Mode::Linear
    }
}

// ---------------------------------------------------------------------------
// Compilation error
// ---------------------------------------------------------------------------

/// Compilation error type
#[derive(Debug, Clone)]
pub struct CodegenError(pub String);

impl std::fmt::Display for CodegenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for CodegenError {}

// ---------------------------------------------------------------------------
// Metadata for a user-defined function
// ---------------------------------------------------------------------------

/// Information about a user-defined function collected during the first pass.
#[derive(Debug, Clone)]
struct UserFnInfo {
    /// Index into the WASM function space (imports + runtime + user)
    wasm_fn_idx: u32,
    /// Index of its type in the type section
    wasm_type_idx: u32,
    /// Parameter names (in order) for local binding
    #[allow(dead_code)]
    param_names: Vec<String>,
    /// Whether each parameter is linear (must-use-once)
    #[allow(dead_code)]
    param_linear: Vec<bool>,
}

// ---------------------------------------------------------------------------
// Local variable tracker for a single function compilation
// ---------------------------------------------------------------------------

/// Tracks local variable slots within a single WASM function.
#[derive(Debug, Clone, Default)]
struct LocalTracker {
    /// Map from variable name to its local index
    name_to_idx: HashMap<String, u32>,
    /// Number of locals allocated so far (parameters first, then compiler temps)
    next_idx: u32,
    /// Which locals are linear (must be consumed before scope exit)
    linear_locals: HashMap<u32, bool>,
}

impl LocalTracker {
    fn new(num_params: u32) -> Self {
        Self {
            name_to_idx: HashMap::new(),
            next_idx: num_params,
            linear_locals: HashMap::new(),
        }
    }

    /// Bind a named variable to the next available local slot.
    fn bind(&mut self, name: &str, is_linear: bool) -> u32 {
        let idx = self.next_idx;
        self.next_idx += 1;
        self.name_to_idx.insert(name.to_string(), idx);
        if is_linear {
            self.linear_locals.insert(idx, false); // false = not yet consumed
        }
        idx
    }

    /// Allocate an anonymous temporary.
    fn temp(&mut self) -> u32 {
        let idx = self.next_idx;
        self.next_idx += 1;
        idx
    }

    /// Look up a variable by name, returning its local index.
    fn get(&self, name: &str) -> Option<u32> {
        self.name_to_idx.get(name).copied()
    }

    /// Mark a linear local as consumed.
    fn mark_consumed(&mut self, idx: u32) {
        if let Some(v) = self.linear_locals.get_mut(&idx) {
            *v = true;
        }
    }

    /// Total number of extra (non-parameter) locals needed.
    fn num_extra_locals(&self, num_params: u32) -> u32 {
        if self.next_idx > num_params {
            self.next_idx - num_params
        } else {
            0
        }
    }
}

// ---------------------------------------------------------------------------
// Code generator
// ---------------------------------------------------------------------------

/// Closure representation: (function_index, environment_ptr)
const CLOSURE_SIZE: u32 = 8; // 2 x i32

/// Code generator state.
pub struct Codegen {
    /// Current bump pointer for allocations (reserved for future interpreter use)
    #[allow(dead_code)]
    bump_ptr: u32,
    /// Region stack for tracking active regions (reserved for future interpreter use)
    #[allow(dead_code)]
    region_stack: Vec<RegionInfo>,
    /// Generated WASM module
    module: WasmModule,

    // -- Per-function state (set up before each function compilation) --------

    /// Local variable tracker for the function currently being compiled
    locals: LocalTracker,

    // -- Module-level bookkeeping -------------------------------------------

    /// String literal data section entries: (offset, bytes)
    data_entries: Vec<(u32, Vec<u8>)>,
    /// Next data offset for string literals
    data_offset: u32,

    /// User function metadata, keyed by function name
    user_fns: HashMap<String, UserFnInfo>,

    /// Dynamically added WASM type entries beyond the fixed set.
    /// Each entry is `(params, results)` as vectors of `ValType`.
    extra_types: Vec<(Vec<ValType>, Vec<ValType>)>,

    /// Lambda functions generated during compilation
    /// Each lambda gets compiled to a named function and stored here
    lambda_fns: Vec<LambdaInfo>,

    /// Compilation mode (affine or linear)
    mode: Mode,
}

/// Information about a compiled lambda
#[derive(Debug, Clone)]
struct LambdaInfo {
    /// WASM function index for the lambda body
    wasm_fn_idx: u32,
    /// WASM type index
    wasm_type_idx: u32,
    /// Variables captured from the enclosing scope
    captured_vars: Vec<String>,
    /// Lambda parameter name
    param: String,
    /// Lambda parameter type
    param_ty: Ty,
    /// Lambda body expression (cloned for later compilation)
    body: Expr,
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

impl Default for Codegen {
    fn default() -> Self {
        Self::new()
    }
}

impl Codegen {
    /// Create a new code generator in linear mode (default)
    pub fn new() -> Self {
        Self::new_with_mode(Mode::Linear)
    }

    /// Create a new code generator with specified mode
    pub fn new_with_mode(mode: Mode) -> Self {
        Self {
            bump_ptr: REGION_HEADER_SIZE,
            region_stack: Vec::new(),
            module: WasmModule::new(),
            locals: LocalTracker::default(),
            data_entries: Vec::new(),
            data_offset: 1024, // Start string data after metadata area
            user_fns: HashMap::new(),
            extra_types: Vec::new(),
            lambda_fns: Vec::new(),
            mode,
        }
    }

    /// Get the current compilation mode
    pub fn mode(&self) -> Mode {
        self.mode
    }

    /// Set the compilation mode
    pub fn set_mode(&mut self, mode: Mode) {
        self.mode = mode;
    }

    // -----------------------------------------------------------------------
    // Public entry points
    // -----------------------------------------------------------------------

    /// Generate a minimal WASM module with only the runtime (no user code).
    pub fn generate(&mut self) -> Vec<u8> {
        self.emit_types();
        self.emit_imports();

        // Build function + code sections together
        let mut func_sec = FunctionSection::new();
        let mut code_sec = CodeSection::new();
        self.append_runtime_funcs(&mut func_sec, &mut code_sec);
        self.module.section(&func_sec);

        self.emit_memory();
        self.emit_exports();

        self.module.section(&code_sec);
        self.emit_data_section();
        self.module.clone().finish()
    }

    /// Compile a single standalone expression as a `main` function.
    pub fn compile_program(&mut self, main_expr: &Expr) -> Vec<u8> {
        self.emit_types();
        self.emit_imports();

        // Build function + code sections together (runtime + main)
        let mut func_sec = FunctionSection::new();
        let mut code_sec = CodeSection::new();
        self.append_runtime_funcs(&mut func_sec, &mut code_sec);

        // Main function (index FIRST_USER_FN = 9)
        func_sec.function(TYPE_VOID_VOID);
        self.locals = LocalTracker::new(0);
        let mut main_func = Function::new(vec![(16, ValType::I32)]);
        self.compile_expr(&mut main_func, main_expr);
        main_func.instruction(&Instruction::Drop);
        main_func.instruction(&Instruction::End);
        code_sec.function(&main_func);

        self.module.section(&func_sec);
        self.emit_memory();

        // Exports
        let mut exports = ExportSection::new();
        self.add_runtime_exports(&mut exports);
        exports.export("main", ExportKind::Func, FIRST_USER_FN);
        self.module.section(&exports);

        self.module.section(&code_sec);
        self.emit_data_section();
        self.module.clone().finish()
    }

    /// Compile a module encoded as an S-expression string.
    pub fn compile_sexpr_module(&mut self, sexpr: &str) -> Result<Vec<u8>, String> {
        let module = module_from_sexpr(sexpr).map_err(|e| e.to_string())?;
        compile_module(&module).map_err(|e| e.to_string())
    }

    /// Compile a full [`AstModule`] to WASM bytes.
    ///
    /// This is the primary entry point for module-level compilation.  It:
    /// 1. Collects function signatures and assigns WASM indices.
    /// 2. Emits the type, import, memory, function, and code sections.
    /// 3. If a `main` function exists, exports it.
    pub fn compile_ast_module(&mut self, ast: &AstModule) -> Result<Vec<u8>, CodegenError> {
        // ----- Phase 1: collect function metadata --------------------------
        self.collect_user_fns(ast)?;

        // ----- Phase 2: emit sections --------------------------------------
        self.emit_types();
        self.emit_imports();

        // Build function + code sections together (runtime + user)
        let mut func_sec = FunctionSection::new();
        let mut code_sec = CodeSection::new();

        // Runtime helpers (7 functions, indices 2..8)
        self.append_runtime_funcs(&mut func_sec, &mut code_sec);

        // User functions
        self.append_user_funcs(ast, &mut func_sec, &mut code_sec)?;

        // Lambda functions (discovered during user function compilation)
        self.append_lambda_funcs(&mut func_sec, &mut code_sec)?;

        // Emit sections in WASM-required order:
        // Type, Import, Function, Table, Memory, Export, Element, Code, Data
        self.module.section(&func_sec);
        self.emit_table();
        self.emit_memory();
        self.emit_module_exports(ast);
        self.emit_elements();
        self.module.section(&code_sec);
        self.emit_data_section();

        Ok(self.module.clone().finish())
    }

    /// Compile a module that has a `main` function with a body expression.
    /// (Legacy helper retained for backward compatibility.)
    pub fn compile_module_with_main(
        &mut self,
        module: &AstModule,
        main_body: &Expr,
    ) -> Vec<u8> {
        // Try full module compilation first; fall back to expression mode.
        if let Ok(bytes) = self.compile_ast_module(module) {
            return bytes;
        }

        // Fallback: just compile the main body as a standalone expression.
        self.emit_types();
        self.emit_imports();

        let mut func_sec = FunctionSection::new();
        let mut code_sec = CodeSection::new();

        self.append_runtime_funcs(&mut func_sec, &mut code_sec);

        // Main function (index FIRST_USER_FN)
        func_sec.function(TYPE_VOID_VOID);

        self.locals = LocalTracker::new(0);
        let mut main_func = Function::new(vec![(16, ValType::I32)]);
        self.compile_expr(&mut main_func, main_body);
        main_func.instruction(&Instruction::Drop);
        main_func.instruction(&Instruction::End);
        code_sec.function(&main_func);

        // Emit in WASM order: Type, Import, Function, Memory, Export, Code, Data
        self.module.section(&func_sec);
        self.emit_memory();

        let mut exports = ExportSection::new();
        self.add_runtime_exports(&mut exports);
        exports.export("main", ExportKind::Func, FIRST_USER_FN);
        self.module.section(&exports);

        self.module.section(&code_sec);
        self.emit_data_section();
        self.module.clone().finish()
    }

    // -----------------------------------------------------------------------
    // Phase 1 -- collect user function metadata
    // -----------------------------------------------------------------------

    fn collect_user_fns(&mut self, ast: &AstModule) -> Result<(), CodegenError> {
        let mut idx = FIRST_USER_FN;
        for decl in &ast.decls {
            match decl {
                Decl::Fn {
                    name,
                    params,
                    ret_ty,
                    ..
                } => {
                    // Build WASM type for this function
                    let wasm_params: Vec<ValType> =
                        params.iter().map(|(_, ty)| ty_to_valtype(ty)).collect();
                    let wasm_results = vec![ty_to_valtype(ret_ty)];
                    let type_idx = self.register_type(wasm_params.clone(), wasm_results);

                    let param_names: Vec<String> =
                        params.iter().map(|(n, _)| n.to_string()).collect();
                    let param_linear: Vec<bool> =
                        params.iter().map(|(_, ty)| ty.is_linear()).collect();

                    self.user_fns.insert(
                        name.to_string(),
                        UserFnInfo {
                            wasm_fn_idx: idx,
                            wasm_type_idx: type_idx,
                            param_names,
                            param_linear,
                        },
                    );
                    idx += 1;
                }
                Decl::Type { .. } => { /* type aliases are erased at runtime */ }
            }
        }
        Ok(())
    }

    /// Register (or reuse) a function type, returning its type-section index.
    fn register_type(&mut self, params: Vec<ValType>, results: Vec<ValType>) -> u32 {
        // Check if this matches one of the fixed types
        if params.is_empty() && results == [ValType::I32] {
            return TYPE_VOID_I32;
        }
        if params == [ValType::I32] && results.is_empty() {
            return TYPE_I32_VOID;
        }
        if params == [ValType::I32, ValType::I32] && results.is_empty() {
            return TYPE_I32_I32_VOID;
        }
        if params == [ValType::I32, ValType::I32] && results == [ValType::I32] {
            return TYPE_I32_I32_I32;
        }
        if params.is_empty() && results.is_empty() {
            return TYPE_VOID_VOID;
        }
        if params == [ValType::I32] && results == [ValType::I32] {
            return TYPE_I32_TO_I32;
        }

        // Check existing extra types
        for (i, (p, r)) in self.extra_types.iter().enumerate() {
            if *p == params && *r == results {
                return NUM_FIXED_TYPES + i as u32;
            }
        }

        // Add new type
        let idx = NUM_FIXED_TYPES + self.extra_types.len() as u32;
        self.extra_types.push((params, results));
        idx
    }

    // -----------------------------------------------------------------------
    // Section emitters
    // -----------------------------------------------------------------------

    fn emit_types(&mut self) {
        let mut types = TypeSection::new();

        // Type 0: () -> i32
        types.ty().function(vec![], vec![ValType::I32]);
        // Type 1: (i32) -> ()
        types.ty().function(vec![ValType::I32], vec![]);
        // Type 2: (i32, i32) -> ()
        types
            .ty()
            .function(vec![ValType::I32, ValType::I32], vec![]);
        // Type 3: (i32, i32) -> i32
        types
            .ty()
            .function(vec![ValType::I32, ValType::I32], vec![ValType::I32]);
        // Type 4: () -> ()
        types.ty().function(vec![], vec![]);
        // Type 5: (i32, i32, i32, i32) -> i64
        types.ty().function(
            vec![ValType::I32, ValType::I32, ValType::I32, ValType::I32],
            vec![ValType::I64],
        );
        // Type 6: (i32) -> i32
        types
            .ty()
            .function(vec![ValType::I32], vec![ValType::I32]);

        // Dynamic extra types
        for (params, results) in &self.extra_types {
            types.ty().function(params.clone(), results.clone());
        }

        self.module.section(&types);
    }

    fn emit_imports(&mut self) {
        let mut imports = ImportSection::new();
        // Import 0: print_i32  -- (i32) -> ()
        imports.import(
            "env",
            "print_i32",
            wasm_encoder::EntityType::Function(TYPE_I32_VOID),
        );
        // Import 1: print_string  -- (i32, i32) -> ()
        imports.import(
            "env",
            "print_string",
            wasm_encoder::EntityType::Function(TYPE_I32_I32_VOID),
        );
        self.module.section(&imports);
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

    /// Emit the table section for indirect function calls (lambdas).
    /// Creates a table with funcref elements sized to fit all lambda functions.
    fn emit_table(&mut self) {
        if self.lambda_fns.is_empty() {
            return; // No lambdas, no table needed
        }

        let mut tables = TableSection::new();
        // Create a table that can hold all lambda functions plus user functions
        let table_size = (self.user_fns.len() + self.lambda_fns.len()) as u64;
        tables.table(TableType {
            element_type: RefType::FUNCREF,
            minimum: table_size,
            maximum: Some(table_size),
            table64: false,
            shared: false,
        });
        self.module.section(&tables);
    }

    /// Emit the element section to populate the function table.
    /// Maps lambda function indices into table slots for call_indirect.
    fn emit_elements(&mut self) {
        if self.lambda_fns.is_empty() {
            return; // No lambdas, no elements needed
        }

        let mut elements = ElementSection::new();

        // Collect all function indices (user functions + lambdas)
        let mut func_indices = Vec::new();

        // Add user function indices
        for info in self.user_fns.values() {
            func_indices.push(info.wasm_fn_idx);
        }

        // Add lambda function indices
        for lambda in &self.lambda_fns {
            func_indices.push(lambda.wasm_fn_idx);
        }

        // Populate table starting at offset 0
        elements.active(
            Some(0), // table index (we only have one table)
            &ConstExpr::i32_const(0), // offset in the table
            Elements::Functions(std::borrow::Cow::Borrowed(&func_indices)),
        );

        self.module.section(&elements);
    }

    /// Append the 7 runtime helper functions to the given sections.
    fn append_runtime_funcs(
        &self,
        func_sec: &mut FunctionSection,
        code_sec: &mut CodeSection,
    ) {
        // 2: bump_alloc  (i32, i32) -> i32
        func_sec.function(TYPE_I32_I32_I32);
        code_sec.function(&self.gen_bump_alloc());

        // 3: string_new  (i32, i32) -> i32
        func_sec.function(TYPE_I32_I32_I32);
        code_sec.function(&self.gen_string_new());

        // 4: string_len  (i32, i32) -> i32
        func_sec.function(TYPE_I32_I32_I32);
        code_sec.function(&self.gen_string_len());

        // 5: string_concat  (i32, i32) -> i32
        func_sec.function(TYPE_I32_I32_I32);
        code_sec.function(&self.gen_string_concat());

        // 6: string_drop  (i32) -> ()
        func_sec.function(TYPE_I32_VOID);
        code_sec.function(&self.gen_string_drop());

        // 7: region_enter  () -> ()
        func_sec.function(TYPE_VOID_VOID);
        code_sec.function(&self.gen_region_enter());

        // 8: region_exit   () -> ()
        func_sec.function(TYPE_VOID_VOID);
        code_sec.function(&self.gen_region_exit());
    }

    /// Append user-defined functions from the AST.
    ///
    /// Uses a two-pass approach per function:
    /// 1. First pass: compile body to count how many extra locals are needed.
    /// 2. Second pass: compile body again into a Function with the correct
    ///    local declarations.
    ///
    /// Side effects like `add_string_literal` are idempotent for the same
    /// strings, so running twice is safe (duplicates are harmless since each
    /// string gets its own data segment entry).
    fn append_user_funcs(
        &mut self,
        ast: &AstModule,
        func_sec: &mut FunctionSection,
        code_sec: &mut CodeSection,
    ) -> Result<(), CodegenError> {
        for decl in &ast.decls {
            match decl {
                Decl::Fn {
                    name,
                    params,
                    body,
                    ..
                } => {
                    let info = self
                        .user_fns
                        .get(name.as_str())
                        .cloned()
                        .ok_or_else(|| {
                            CodegenError(format!("BUG: function `{}` not collected", name))
                        })?;

                    func_sec.function(info.wasm_type_idx);

                    let num_params = params.len() as u32;

                    // --- Pass 1: count locals by doing a dry-run compile ----
                    self.locals = LocalTracker::new(num_params);
                    for (i, (pname, pty)) in params.iter().enumerate() {
                        self.locals
                            .name_to_idx
                            .insert(pname.to_string(), i as u32);
                        if pty.is_linear() {
                            self.locals.linear_locals.insert(i as u32, false);
                        }
                    }

                    // Save data state so pass 1 string literals don't duplicate
                    let data_snapshot = (self.data_entries.len(), self.data_offset);

                    let mut dummy_func = Function::new(vec![(64, ValType::I32)]); // generous
                    self.compile_expr(&mut dummy_func, body);
                    let extra = self.locals.num_extra_locals(num_params);

                    // Restore data state
                    self.data_entries.truncate(data_snapshot.0);
                    self.data_offset = data_snapshot.1;

                    // --- Pass 2: compile for real with correct local count --
                    self.locals = LocalTracker::new(num_params);
                    for (i, (pname, pty)) in params.iter().enumerate() {
                        self.locals
                            .name_to_idx
                            .insert(pname.to_string(), i as u32);
                        if pty.is_linear() {
                            self.locals.linear_locals.insert(i as u32, false);
                        }
                    }

                    let mut func = Function::new(if extra > 0 {
                        vec![(extra, ValType::I32)]
                    } else {
                        vec![]
                    });

                    self.compile_expr(&mut func, body);
                    func.instruction(&Instruction::End);

                    code_sec.function(&func);
                }
                Decl::Type { .. } => {}
            }
        }
        Ok(())
    }

    /// Append lambda functions to the code section.
    /// Called after user functions are compiled, since lambdas are discovered
    /// during user function compilation.
    fn append_lambda_funcs(
        &mut self,
        func_sec: &mut FunctionSection,
        code_sec: &mut CodeSection,
    ) -> Result<(), CodegenError> {
        // Clone lambda_fns to avoid borrow checker issues
        let lambdas = self.lambda_fns.clone();

        for lambda_info in lambdas {
            // Register function type in function section
            func_sec.function(lambda_info.wasm_type_idx);

            // Compile lambda body with two-pass approach (similar to user functions)
            let num_params = 1; // Lambdas always have exactly one parameter

            // --- Pass 1: count locals by doing a dry-run compile ----
            self.locals = LocalTracker::new(num_params);
            self.locals.name_to_idx.insert(lambda_info.param.clone(), 0);
            if lambda_info.param_ty.is_linear() {
                self.locals.linear_locals.insert(0, false);
            }

            // Save data state so pass 1 string literals don't duplicate
            let data_snapshot = (self.data_entries.len(), self.data_offset);

            let mut dummy_func = Function::new(vec![(64, ValType::I32)]); // generous
            self.compile_expr(&mut dummy_func, &lambda_info.body);
            let extra = self.locals.num_extra_locals(num_params);

            // Restore data state
            self.data_entries.truncate(data_snapshot.0);
            self.data_offset = data_snapshot.1;

            // --- Pass 2: compile for real with correct local count --
            self.locals = LocalTracker::new(num_params);
            self.locals.name_to_idx.insert(lambda_info.param.clone(), 0);
            if lambda_info.param_ty.is_linear() {
                self.locals.linear_locals.insert(0, false);
            }

            let mut func = Function::new(if extra > 0 {
                vec![(extra, ValType::I32)]
            } else {
                vec![]
            });

            self.compile_expr(&mut func, &lambda_info.body);
            func.instruction(&Instruction::End);

            code_sec.function(&func);
        }
        Ok(())
    }

    /// Emit runtime-only exports.
    fn emit_exports(&mut self) {
        let mut exports = ExportSection::new();
        self.add_runtime_exports(&mut exports);
        self.module.section(&exports);
    }

    /// Emit module-level exports including user functions.
    fn emit_module_exports(&mut self, ast: &AstModule) {
        let mut exports = ExportSection::new();
        self.add_runtime_exports(&mut exports);

        // Export all user functions by name
        for decl in &ast.decls {
            if let Decl::Fn { name, .. } = decl {
                if let Some(info) = self.user_fns.get(name.as_str()) {
                    exports.export(name.as_str(), ExportKind::Func, info.wasm_fn_idx);
                }
            }
        }

        self.module.section(&exports);
    }

    fn add_runtime_exports(&self, exports: &mut ExportSection) {
        exports.export("__ephapax_bump_alloc", ExportKind::Func, FN_BUMP_ALLOC);
        exports.export("__ephapax_string_new", ExportKind::Func, FN_STRING_NEW);
        exports.export("__ephapax_string_len", ExportKind::Func, FN_STRING_LEN);
        exports.export(
            "__ephapax_string_concat",
            ExportKind::Func,
            FN_STRING_CONCAT,
        );
        exports.export("__ephapax_string_drop", ExportKind::Func, FN_STRING_DROP);
        exports.export(
            "__ephapax_region_enter",
            ExportKind::Func,
            FN_REGION_ENTER,
        );
        exports.export("__ephapax_region_exit", ExportKind::Func, FN_REGION_EXIT);
        exports.export("memory", ExportKind::Memory, 0);
    }

    fn emit_data_section(&mut self) {
        if self.data_entries.is_empty() {
            return;
        }
        let mut data = wasm_encoder::DataSection::new();
        for (offset, bytes) in &self.data_entries {
            data.active(
                0,
                &wasm_encoder::ConstExpr::i32_const(*offset as i32),
                bytes.iter().copied(),
            );
        }
        self.module.section(&data);
    }

    // (Legacy emit helpers removed -- section building now done inline)

    // -----------------------------------------------------------------------
    // Runtime function generators
    // -----------------------------------------------------------------------

    /// Bump allocator: `(size: i32, _: i32) -> ptr: i32`
    fn gen_bump_alloc(&self) -> Function {
        let mut f = Function::new(vec![(1, ValType::I32)]); // local for old_ptr

        // old_ptr = mem[0]  (bump pointer lives at address 0)
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::I32Load(mem_arg(0)));
        f.instruction(&Instruction::LocalSet(2));

        // mem[0] = old_ptr + size
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::LocalGet(0)); // size parameter
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Store(mem_arg(0)));

        // return old_ptr
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::End);
        f
    }

    /// String allocation: `(ptr: i32, len: i32) -> handle: i32`
    fn gen_string_new(&self) -> Function {
        let mut f = Function::new(vec![(1, ValType::I32)]); // local for handle

        // Allocate 8-byte header
        f.instruction(&Instruction::I32Const(STRING_SIZE as i32));
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::Call(FN_BUMP_ALLOC));
        f.instruction(&Instruction::LocalSet(2));

        // Store ptr at handle+0
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::LocalGet(0));
        f.instruction(&Instruction::I32Store(mem_arg(0)));

        // Store len at handle+4
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::LocalGet(1));
        f.instruction(&Instruction::I32Store(mem_arg(4)));

        // return handle
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::End);
        f
    }

    /// Get string length: `(handle: i32, _: i32) -> len: i32`
    fn gen_string_len(&self) -> Function {
        let mut f = Function::new(vec![]);
        f.instruction(&Instruction::LocalGet(0));
        f.instruction(&Instruction::I32Load(mem_arg(4)));
        f.instruction(&Instruction::End);
        f
    }

    /// Concatenate two strings: `(h1: i32, h2: i32) -> new_handle: i32`
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
        f.instruction(&Instruction::LocalGet(0));
        f.instruction(&Instruction::I32Load(mem_arg(0)));
        f.instruction(&Instruction::LocalSet(2));

        f.instruction(&Instruction::LocalGet(0));
        f.instruction(&Instruction::I32Load(mem_arg(4)));
        f.instruction(&Instruction::LocalSet(3));

        // Load ptr2, len2 from handle2
        f.instruction(&Instruction::LocalGet(1));
        f.instruction(&Instruction::I32Load(mem_arg(0)));
        f.instruction(&Instruction::LocalSet(4));

        f.instruction(&Instruction::LocalGet(1));
        f.instruction(&Instruction::I32Load(mem_arg(4)));
        f.instruction(&Instruction::LocalSet(5));

        // Allocate buffer: len1 + len2
        f.instruction(&Instruction::LocalGet(3));
        f.instruction(&Instruction::LocalGet(5));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::Call(FN_BUMP_ALLOC));
        f.instruction(&Instruction::LocalSet(6));

        // memory.copy(new_ptr, ptr1, len1)
        f.instruction(&Instruction::LocalGet(6));
        f.instruction(&Instruction::LocalGet(2));
        f.instruction(&Instruction::LocalGet(3));
        f.instruction(&Instruction::MemoryCopy {
            src_mem: 0,
            dst_mem: 0,
        });

        // memory.copy(new_ptr + len1, ptr2, len2)
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
        f.instruction(&Instruction::Call(FN_BUMP_ALLOC));
        f.instruction(&Instruction::LocalSet(7));

        // Store ptr
        f.instruction(&Instruction::LocalGet(7));
        f.instruction(&Instruction::LocalGet(6));
        f.instruction(&Instruction::I32Store(mem_arg(0)));

        // Store total len
        f.instruction(&Instruction::LocalGet(7));
        f.instruction(&Instruction::LocalGet(3));
        f.instruction(&Instruction::LocalGet(5));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::I32Store(mem_arg(4)));

        // return new_handle
        f.instruction(&Instruction::LocalGet(7));
        f.instruction(&Instruction::End);
        f
    }

    /// Drop a string handle (no-op in bump allocator)
    fn gen_string_drop(&self) -> Function {
        let mut f = Function::new(vec![]);
        f.instruction(&Instruction::End);
        f
    }

    /// Enter a new region: save current bump pointer on the region stack.
    ///
    /// Region stack layout in linear memory:
    /// - `mem[0]`: bump pointer
    /// - `mem[8]`: region stack pointer (byte offset into the region stack area)
    fn gen_region_enter(&self) -> Function {
        // locals: 0 = new_sp
        let mut f = Function::new(vec![(1, ValType::I32)]);

        // new_sp = mem[8] + 4
        f.instruction(&Instruction::I32Const(8));
        f.instruction(&Instruction::I32Load(mem_arg(0)));
        f.instruction(&Instruction::I32Const(4));
        f.instruction(&Instruction::I32Add);
        f.instruction(&Instruction::LocalSet(0)); // new_sp

        // mem[new_sp] = mem[0]  (save bump_ptr at stack position)
        f.instruction(&Instruction::LocalGet(0));   // address = new_sp
        f.instruction(&Instruction::I32Const(0));
        f.instruction(&Instruction::I32Load(mem_arg(0))); // value = bump_ptr
        f.instruction(&Instruction::I32Store(mem_arg(0))); // mem[new_sp] = bump_ptr

        // mem[8] = new_sp  (update region stack pointer)
        f.instruction(&Instruction::I32Const(8));    // address = 8
        f.instruction(&Instruction::LocalGet(0));    // value = new_sp
        f.instruction(&Instruction::I32Store(mem_arg(0))); // mem[8] = new_sp

        f.instruction(&Instruction::End);
        f
    }

    /// Exit region: restore bump pointer from the region stack.
    fn gen_region_exit(&self) -> Function {
        // locals: 0 = sp (current region stack pointer)
        let mut f = Function::new(vec![(1, ValType::I32)]);

        // sp = mem[8]
        f.instruction(&Instruction::I32Const(8));
        f.instruction(&Instruction::I32Load(mem_arg(0)));
        f.instruction(&Instruction::LocalSet(0)); // sp

        // mem[0] = mem[sp]  (restore bump_ptr)
        f.instruction(&Instruction::I32Const(0));    // address = 0
        f.instruction(&Instruction::LocalGet(0));    // address for load = sp
        f.instruction(&Instruction::I32Load(mem_arg(0))); // value = mem[sp]
        f.instruction(&Instruction::I32Store(mem_arg(0))); // mem[0] = saved_ptr

        // mem[8] = sp - 4  (pop region stack)
        f.instruction(&Instruction::I32Const(8));    // address = 8
        f.instruction(&Instruction::LocalGet(0));    // sp
        f.instruction(&Instruction::I32Const(4));
        f.instruction(&Instruction::I32Sub);         // sp - 4
        f.instruction(&Instruction::I32Store(mem_arg(0))); // mem[8] = sp - 4

        f.instruction(&Instruction::End);
        f
    }

    // -----------------------------------------------------------------------
    // String literal handling
    // -----------------------------------------------------------------------

    /// Add a string literal to the data section, returning (ptr, len).
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

    // -----------------------------------------------------------------------
    // Expression compilation (dual-target: Function or Vec<WasmInstruction>)
    // -----------------------------------------------------------------------

    /// Compile an expression, appending instructions to a `Function`.
    pub fn compile_expr(&mut self, func: &mut Function, expr: &Expr) {
        match &expr.kind {
            ExprKind::Lit(lit) => self.compile_lit(func, lit),
            ExprKind::Var(name) => self.compile_var(func, name),
            ExprKind::StringNew { region: _, value } => self.compile_string_new(func, value),
            ExprKind::StringConcat { left, right } => {
                self.compile_string_concat(func, left, right)
            }
            ExprKind::StringLen(inner) => self.compile_string_len(func, inner),
            ExprKind::Let {
                name, value, body, ..
            } => self.compile_let(func, name, value, body, false),
            ExprKind::LetLin {
                name, value, body, ..
            } => self.compile_let(func, name, value, body, true),
            ExprKind::Lambda { param, param_ty, body } => {
                self.compile_lambda(func, param, param_ty, body)
            }
            ExprKind::App { func: fn_expr, arg } => self.compile_app(func, fn_expr, arg),
            ExprKind::Pair { left, right } => self.compile_pair(func, left, right),
            ExprKind::Fst(inner) => self.compile_fst(func, inner),
            ExprKind::Snd(inner) => self.compile_snd(func, inner),
            ExprKind::Inl { value, .. } => self.compile_inl(func, value),
            ExprKind::Inr { value, .. } => self.compile_inr(func, value),
            ExprKind::Case {
                scrutinee,
                left_var,
                left_body,
                right_var,
                right_body,
            } => self.compile_case(
                func, scrutinee, left_var, left_body, right_var, right_body,
            ),
            ExprKind::If {
                cond,
                then_branch,
                else_branch,
            } => self.compile_if(func, cond, then_branch, else_branch),
            ExprKind::Region { name: _, body } => self.compile_region(func, body),
            ExprKind::Borrow(inner) | ExprKind::Deref(inner) => {
                // Borrow/deref are identity at the WASM level
                self.compile_expr(func, inner);
            }
            ExprKind::Drop(inner) => {
                self.compile_expr(func, inner);
                // Mark the local as consumed if it's a variable
                if let ExprKind::Var(name) = &inner.kind {
                    if let Some(idx) = self.locals.get(name) {
                        self.locals.mark_consumed(idx);
                    }
                }
                func.instruction(&Instruction::Drop);
                func.instruction(&Instruction::I32Const(0)); // Unit
            }
            ExprKind::Copy(inner) => self.compile_copy(func, inner),
            ExprKind::Block(exprs) => self.compile_block(func, exprs),
            ExprKind::BinOp { op, left, right } => {
                self.compile_binop(func, *op, left, right)
            }
            ExprKind::UnaryOp { op, operand } => {
                self.compile_unaryop(func, *op, operand)
            }
        }
    }

    // (compile_expr_to_vec removed -- two-pass now uses dry-run + re-compile)

    // -----------------------------------------------------------------------
    // Individual expression compilers
    // -----------------------------------------------------------------------

    fn compile_lit(&self, func: &mut Function, lit: &Literal) {
        match lit {
            Literal::Unit => {
                func.instruction(&Instruction::I32Const(0));
            }
            Literal::Bool(b) => {
                func.instruction(&Instruction::I32Const(if *b { 1 } else { 0 }));
            }
            Literal::I32(n) => {
                func.instruction(&Instruction::I32Const(*n));
            }
            Literal::I64(n) => {
                func.instruction(&Instruction::I64Const(*n));
            }
            Literal::F32(n) => {
                func.instruction(&Instruction::F32Const(*n));
            }
            Literal::F64(n) => {
                func.instruction(&Instruction::F64Const(*n));
            }
            Literal::String(_) => {
                // String literals should use StringNew; emit 0 as fallback.
                func.instruction(&Instruction::I32Const(0));
            }
        };
    }

    fn compile_var(&mut self, func: &mut Function, name: &str) {
        if let Some(idx) = self.locals.get(name) {
            func.instruction(&Instruction::LocalGet(idx));
            // Mark linear local as consumed
            self.locals.mark_consumed(idx);
        } else {
            // Unknown variable -- should have been caught by type checker.
            func.instruction(&Instruction::Unreachable);
        }
    }

    fn compile_string_new(&mut self, func: &mut Function, value: &str) {
        let (ptr, len) = self.add_string_literal(value);
        func.instruction(&Instruction::I32Const(ptr as i32));
        func.instruction(&Instruction::I32Const(len as i32));
        func.instruction(&Instruction::Call(FN_STRING_NEW));
    }

    fn compile_string_concat(
        &mut self,
        func: &mut Function,
        left: &Expr,
        right: &Expr,
    ) {
        self.compile_expr(func, left);
        self.compile_expr(func, right);
        func.instruction(&Instruction::Call(FN_STRING_CONCAT));
    }

    fn compile_string_len(&mut self, func: &mut Function, inner: &Expr) {
        self.compile_expr(func, inner);
        func.instruction(&Instruction::Call(FN_STRING_LEN));
    }

    fn compile_let(
        &mut self,
        func: &mut Function,
        name: &str,
        value: &Expr,
        body: &Expr,
        is_linear: bool,
    ) {
        // Compile the value expression
        self.compile_expr(func, value);

        // Bind it to a local
        let local_idx = self.locals.bind(name, is_linear);
        func.instruction(&Instruction::LocalSet(local_idx));

        // Compile the body
        self.compile_expr(func, body);

        // Handle unconsumed linear locals (mode-aware):
        // - Linear mode: Type checker already validated consumption, no action needed
        // - Affine mode: Could emit implicit drop, but type checker allows it
        //
        // In both modes, the type checker has already validated correctness,
        // so we don't need runtime enforcement here. This is a static property.
        if is_linear && self.mode == Mode::Affine {
            if let Some(&consumed) = self.locals.linear_locals.get(&local_idx) {
                if !consumed {
                    // In affine mode, unconsumed linear values are allowed.
                    // The WASM runtime will handle cleanup via region exit.
                }
            }
        }
    }

    /// Find free variables in an expression.
    /// A free variable is one that is referenced but not bound in the current scope.
    fn find_free_vars(&self, expr: &Expr, bound_vars: &std::collections::HashSet<String>) -> Vec<String> {
        use std::collections::HashSet;
        let mut free_vars = Vec::new();
        let mut seen = HashSet::new();

        fn collect(
            expr: &Expr,
            bound: &HashSet<String>,
            free: &mut Vec<String>,
            seen: &mut HashSet<String>,
        ) {
            match &expr.kind {
                ExprKind::Var(name) => {
                    if !bound.contains(name.as_str()) && !seen.contains(name.as_str()) {
                        free.push(name.to_string());
                        seen.insert(name.to_string());
                    }
                }
                ExprKind::Let { name, value, body, .. } | ExprKind::LetLin { name, value, body, .. } => {
                    collect(value, bound, free, seen);
                    let mut new_bound = bound.clone();
                    new_bound.insert(name.to_string());
                    collect(body, &new_bound, free, seen);
                }
                ExprKind::Lambda { param, body, .. } => {
                    let mut new_bound = bound.clone();
                    new_bound.insert(param.to_string());
                    collect(body, &new_bound, free, seen);
                }
                ExprKind::App { func, arg } => {
                    collect(func, bound, free, seen);
                    collect(arg, bound, free, seen);
                }
                ExprKind::If { cond, then_branch, else_branch } => {
                    collect(cond, bound, free, seen);
                    collect(then_branch, bound, free, seen);
                    collect(else_branch, bound, free, seen);
                }
                ExprKind::Pair { left, right } => {
                    collect(left, bound, free, seen);
                    collect(right, bound, free, seen);
                }
                ExprKind::Fst(inner) | ExprKind::Snd(inner) | ExprKind::Inl { value: inner, .. } | ExprKind::Inr { value: inner, .. } => {
                    collect(inner, bound, free, seen);
                }
                ExprKind::Case { scrutinee, left_var, left_body, right_var, right_body } => {
                    collect(scrutinee, bound, free, seen);
                    let mut left_bound = bound.clone();
                    left_bound.insert(left_var.to_string());
                    collect(left_body, &left_bound, free, seen);
                    let mut right_bound = bound.clone();
                    right_bound.insert(right_var.to_string());
                    collect(right_body, &right_bound, free, seen);
                }
                ExprKind::BinOp { left, right, .. } => {
                    collect(left, bound, free, seen);
                    collect(right, bound, free, seen);
                }
                ExprKind::UnaryOp { operand, .. } => {
                    collect(operand, bound, free, seen);
                }
                ExprKind::Region { body, .. } => {
                    collect(body, bound, free, seen);
                }
                ExprKind::Borrow(inner) | ExprKind::Deref(inner) | ExprKind::Drop(inner) => {
                    collect(inner, bound, free, seen);
                }
                ExprKind::StringConcat { left, right } => {
                    collect(left, bound, free, seen);
                    collect(right, bound, free, seen);
                }
                ExprKind::StringLen(inner) => {
                    collect(inner, bound, free, seen);
                }
                ExprKind::Copy(inner) => {
                    collect(inner, bound, free, seen);
                }
                ExprKind::Block(exprs) => {
                    for expr in exprs {
                        collect(expr, bound, free, seen);
                    }
                }
                ExprKind::Lit(_) | ExprKind::StringNew { .. } => {}
            }
        }

        collect(expr, bound_vars, &mut free_vars, &mut seen);
        free_vars
    }

    fn compile_lambda(
        &mut self,
        func: &mut Function,
        param: &str,
        param_ty: &Ty,
        body: &Expr,
    ) {
        // 1. Find free variables in the lambda body
        let mut bound_vars = std::collections::HashSet::new();
        bound_vars.insert(param.to_string());
        let captured_vars = self.find_free_vars(body, &bound_vars);

        // 2. Determine the lambda's WASM type
        // For simplicity, assume all lambdas take i32 and return i32
        let lambda_type_idx = TYPE_I32_TO_I32; // Type 6 is (i32) -> i32

        // 3. Calculate function index for this lambda
        // Function indices: imports (2) + runtime helpers (7) + user functions + lambdas
        let lambda_fn_idx = NUM_IMPORTS + NUM_RUNTIME_FNS + self.user_fns.len() as u32 + self.lambda_fns.len() as u32;

        // 4. Record this lambda for later emission
        self.lambda_fns.push(LambdaInfo {
            wasm_fn_idx: lambda_fn_idx,
            wasm_type_idx: lambda_type_idx,
            captured_vars,
            param: param.to_string(),
            param_ty: param_ty.clone(),
            body: body.clone(),
        });

        // 5. Emit the closure representation (just the function index for now)
        // Full closure support would allocate environment and emit (fn_idx, env_ptr) pair
        func.instruction(&Instruction::I32Const(lambda_fn_idx as i32));
    }

    fn compile_app(
        &mut self,
        func: &mut Function,
        fn_expr: &Expr,
        arg: &Expr,
    ) {
        // Check if the function expression is a named function we know about.
        if let ExprKind::Var(name) = &fn_expr.kind {
            if let Some(info) = self.user_fns.get(name.as_str()).cloned() {
                // Direct call to a known function
                self.compile_expr(func, arg);
                func.instruction(&Instruction::Call(info.wasm_fn_idx));
                return;
            }
        }

        // Indirect call via function table (for lambdas and first-class functions)
        // Stack layout: [fn_index] [arg] -> call_indirect -> [result]
        self.compile_expr(func, arg);       // Push argument
        self.compile_expr(func, fn_expr);   // Push function index

        // Use call_indirect with type signature (i32) -> i32
        // Type 6 is TYPE_I32_TO_I32 defined at the top
        func.instruction(&Instruction::CallIndirect {
            type_index: TYPE_I32_TO_I32,
            table_index: 0, // We only have one table (index 0)
        });
    }

    fn compile_pair(
        &mut self,
        func: &mut Function,
        left: &Expr,
        right: &Expr,
    ) {
        // Allocate 8 bytes for pair (2 x i32)
        func.instruction(&Instruction::I32Const(8));
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::Call(FN_BUMP_ALLOC));

        let pair_local = self.locals.temp();
        func.instruction(&Instruction::LocalTee(pair_local));

        // Store left at offset 0
        self.compile_expr(func, left);
        func.instruction(&Instruction::I32Store(mem_arg(0)));

        // Store right at offset 4
        func.instruction(&Instruction::LocalGet(pair_local));
        self.compile_expr(func, right);
        func.instruction(&Instruction::I32Store(mem_arg(4)));

        // Return pair pointer
        func.instruction(&Instruction::LocalGet(pair_local));
    }

    fn compile_fst(&mut self, func: &mut Function, inner: &Expr) {
        self.compile_expr(func, inner);
        func.instruction(&Instruction::I32Load(mem_arg(0)));
    }

    fn compile_snd(&mut self, func: &mut Function, inner: &Expr) {
        self.compile_expr(func, inner);
        func.instruction(&Instruction::I32Load(mem_arg(4)));
    }

    fn compile_inl(&mut self, func: &mut Function, value: &Expr) {
        // Sum types: tag (i32) + value (i32) = 8 bytes
        func.instruction(&Instruction::I32Const(8));
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::Call(FN_BUMP_ALLOC));

        let sum_local = self.locals.temp();
        func.instruction(&Instruction::LocalTee(sum_local));

        // Store tag 0 (left)
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::I32Store(mem_arg(0)));

        // Store value at offset 4
        func.instruction(&Instruction::LocalGet(sum_local));
        self.compile_expr(func, value);
        func.instruction(&Instruction::I32Store(mem_arg(4)));

        func.instruction(&Instruction::LocalGet(sum_local));
    }

    fn compile_inr(&mut self, func: &mut Function, value: &Expr) {
        func.instruction(&Instruction::I32Const(8));
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::Call(FN_BUMP_ALLOC));

        let sum_local = self.locals.temp();
        func.instruction(&Instruction::LocalTee(sum_local));

        // Store tag 1 (right)
        func.instruction(&Instruction::I32Const(1));
        func.instruction(&Instruction::I32Store(mem_arg(0)));

        // Store value at offset 4
        func.instruction(&Instruction::LocalGet(sum_local));
        self.compile_expr(func, value);
        func.instruction(&Instruction::I32Store(mem_arg(4)));

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

        let scrutinee_local = self.locals.temp();
        func.instruction(&Instruction::LocalTee(scrutinee_local));

        // Load tag
        func.instruction(&Instruction::I32Load(mem_arg(0)));

        // if tag != 0 (right branch) else (left branch)
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Result(
            ValType::I32,
        )));

        // Right branch (tag == 1)
        func.instruction(&Instruction::LocalGet(scrutinee_local));
        func.instruction(&Instruction::I32Load(mem_arg(4)));
        let right_local = self.locals.bind(right_var, false);
        func.instruction(&Instruction::LocalSet(right_local));
        self.compile_expr(func, right_body);

        func.instruction(&Instruction::Else);

        // Left branch (tag == 0)
        func.instruction(&Instruction::LocalGet(scrutinee_local));
        func.instruction(&Instruction::I32Load(mem_arg(4)));
        let left_local = self.locals.bind(left_var, false);
        func.instruction(&Instruction::LocalSet(left_local));
        self.compile_expr(func, left_body);

        func.instruction(&Instruction::End);
    }

    fn compile_if(
        &mut self,
        func: &mut Function,
        cond: &Expr,
        then_branch: &Expr,
        else_branch: &Expr,
    ) {
        self.compile_expr(func, cond);
        func.instruction(&Instruction::If(wasm_encoder::BlockType::Result(
            ValType::I32,
        )));
        self.compile_expr(func, then_branch);
        func.instruction(&Instruction::Else);
        self.compile_expr(func, else_branch);
        func.instruction(&Instruction::End);
    }

    fn compile_region(&mut self, func: &mut Function, body: &Expr) {
        func.instruction(&Instruction::Call(FN_REGION_ENTER));
        self.compile_expr(func, body);
        func.instruction(&Instruction::Call(FN_REGION_EXIT));
    }

    fn compile_copy(&mut self, func: &mut Function, inner: &Expr) {
        let tmp = self.locals.temp();
        self.compile_expr(func, inner);
        func.instruction(&Instruction::LocalSet(tmp)); // save value, consume from stack

        // Allocate pair (8 bytes) and store value twice
        func.instruction(&Instruction::I32Const(8));
        func.instruction(&Instruction::I32Const(0));
        func.instruction(&Instruction::Call(FN_BUMP_ALLOC));

        let pair_local = self.locals.temp();
        func.instruction(&Instruction::LocalSet(pair_local)); // save pair ptr

        // Store value at pair+0
        func.instruction(&Instruction::LocalGet(pair_local));
        func.instruction(&Instruction::LocalGet(tmp));
        func.instruction(&Instruction::I32Store(mem_arg(0)));

        // Store value at pair+4
        func.instruction(&Instruction::LocalGet(pair_local));
        func.instruction(&Instruction::LocalGet(tmp));
        func.instruction(&Instruction::I32Store(mem_arg(4)));

        // Return pair pointer
        func.instruction(&Instruction::LocalGet(pair_local));
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

    fn compile_binop(
        &mut self,
        func: &mut Function,
        op: BinOp,
        left: &Expr,
        right: &Expr,
    ) {
        self.compile_expr(func, left);
        self.compile_expr(func, right);

        let instr = match op {
            BinOp::Add => Instruction::I32Add,
            BinOp::Sub => Instruction::I32Sub,
            BinOp::Mul => Instruction::I32Mul,
            BinOp::Div => Instruction::I32DivS,
            BinOp::Mod => Instruction::I32RemS,
            BinOp::Lt => Instruction::I32LtS,
            BinOp::Le => Instruction::I32LeS,
            BinOp::Gt => Instruction::I32GtS,
            BinOp::Ge => Instruction::I32GeS,
            BinOp::Eq => Instruction::I32Eq,
            BinOp::Ne => Instruction::I32Ne,
            BinOp::And => Instruction::I32And,
            BinOp::Or => Instruction::I32Or,
        };
        func.instruction(&instr);
    }

    fn compile_unaryop(
        &mut self,
        func: &mut Function,
        op: UnaryOp,
        operand: &Expr,
    ) {
        match op {
            UnaryOp::Not => {
                self.compile_expr(func, operand);
                func.instruction(&Instruction::I32Eqz);
            }
            UnaryOp::Neg => {
                func.instruction(&Instruction::I32Const(0));
                self.compile_expr(func, operand);
                func.instruction(&Instruction::I32Sub);
            }
        }
    }

    // -----------------------------------------------------------------------
    // Legacy: compile_hello_world
    // -----------------------------------------------------------------------

    /// Compile a "Hello World" program that prints a string.
    pub fn compile_hello_world(&mut self, message: &str) -> Vec<u8> {
        self.emit_types();
        self.emit_imports();

        let mut func_sec = FunctionSection::new();
        let mut code_sec = CodeSection::new();

        self.append_runtime_funcs(&mut func_sec, &mut code_sec);

        // Main function (index FIRST_USER_FN = 9)
        func_sec.function(TYPE_VOID_VOID);

        let (ptr, len) = self.add_string_literal(message);
        let mut main_func = Function::new(vec![]);
        main_func.instruction(&Instruction::I32Const(ptr as i32));
        main_func.instruction(&Instruction::I32Const(len as i32));
        // Import index 1 = print_string
        main_func.instruction(&Instruction::Call(1));
        main_func.instruction(&Instruction::End);
        code_sec.function(&main_func);

        // Emit in WASM order: Type, Import, Function, Memory, Export, Code, Data
        self.module.section(&func_sec);
        self.emit_memory();

        let mut exports = ExportSection::new();
        self.add_runtime_exports(&mut exports);
        exports.export("main", ExportKind::Func, FIRST_USER_FN);
        self.module.section(&exports);

        self.module.section(&code_sec);
        self.emit_data_section();
        self.module.clone().finish()
    }
}

// ---------------------------------------------------------------------------
// Helper: memory argument shorthand
// ---------------------------------------------------------------------------

fn mem_arg(offset: u64) -> wasm_encoder::MemArg {
    wasm_encoder::MemArg {
        offset,
        align: 2,
        memory_index: 0,
    }
}

// ---------------------------------------------------------------------------
// Type mapping: Ephapax Ty -> WASM ValType
// ---------------------------------------------------------------------------

/// Map an Ephapax type to the WASM value type used at runtime.
///
/// In the current lowering strategy, all values are represented as `i32`
/// (pointers, booleans, integers).  64-bit integers use `i64`, and floats
/// use `f32`/`f64`.
fn ty_to_valtype(ty: &Ty) -> ValType {
    match ty {
        Ty::Base(BaseTy::I64) => ValType::I64,
        Ty::Base(BaseTy::F32) => ValType::F32,
        Ty::Base(BaseTy::F64) => ValType::F64,
        // Everything else (I32, Bool, Unit, String handles, pointers) => i32
        _ => ValType::I32,
    }
}

// ---------------------------------------------------------------------------
// Public convenience API
// ---------------------------------------------------------------------------

/// Compile an S-expression encoded module directly to WASM bytes.
pub fn compile_sexpr_module(sexpr: &str) -> Result<Vec<u8>, String> {
    let mut codegen = Codegen::new();
    codegen.compile_sexpr_module(sexpr)
}

/// Compile an entire Ephapax [`AstModule`] to WebAssembly with specified mode.
pub fn compile_module_with_mode(module: &AstModule, mode: Mode) -> Result<Vec<u8>, CodegenError> {
    let mut codegen = Codegen::new_with_mode(mode);
    codegen.compile_ast_module(module)
}

/// Compile an entire Ephapax [`AstModule`] to WebAssembly (defaults to Linear mode).
pub fn compile_module(module: &AstModule) -> Result<Vec<u8>, CodegenError> {
    compile_module_with_mode(module, Mode::Linear)
}

// ===========================================================================
// Tests
// ===========================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use ephapax_syntax::{BaseTy, Span, Ty};

    // -----------------------------------------------------------------------
    // WASM validation helper
    // -----------------------------------------------------------------------

    /// Validate that the given bytes form a valid WASM module.
    fn validate_wasm(wasm: &[u8]) {
        use wasmparser::Validator;
        let mut validator = Validator::new();
        validator.validate_all(wasm).expect("invalid WASM module");
    }

    /// Assert WASM magic number and version.
    fn assert_wasm_header(wasm: &[u8]) {
        assert!(wasm.len() >= 8, "WASM too small: {} bytes", wasm.len());
        assert_eq!(&wasm[0..4], b"\x00asm", "bad WASM magic");
        assert_eq!(&wasm[4..8], &[1, 0, 0, 0], "bad WASM version");
    }

    /// Shorthand for creating a dummy expression.
    fn e(kind: ExprKind) -> Expr {
        Expr::new(kind, Span::dummy())
    }

    // -----------------------------------------------------------------------
    // Basic generation
    // -----------------------------------------------------------------------

    #[test]
    fn generates_valid_wasm() {
        let mut codegen = Codegen::new();
        let wasm = codegen.generate();
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn hello_world_generates_valid_wasm() {
        let mut codegen = Codegen::new();
        let wasm = codegen.compile_hello_world("Hello, Ephapax!");
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
        assert!(wasm.len() > 100, "WASM too small: {} bytes", wasm.len());
    }

    // -----------------------------------------------------------------------
    // Literal compilation
    // -----------------------------------------------------------------------

    #[test]
    fn compile_literal_i32() {
        let mut codegen = Codegen::new();
        let wasm = codegen.compile_program(&e(ExprKind::Lit(Literal::I32(42))));
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_literal_bool_true() {
        let mut codegen = Codegen::new();
        let wasm = codegen.compile_program(&e(ExprKind::Lit(Literal::Bool(true))));
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_literal_bool_false() {
        let mut codegen = Codegen::new();
        let wasm = codegen.compile_program(&e(ExprKind::Lit(Literal::Bool(false))));
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_literal_unit() {
        let mut codegen = Codegen::new();
        let wasm = codegen.compile_program(&e(ExprKind::Lit(Literal::Unit)));
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    // -----------------------------------------------------------------------
    // Arithmetic & comparison
    // -----------------------------------------------------------------------

    #[test]
    fn compile_add() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::BinOp {
            op: BinOp::Add,
            left: Box::new(e(ExprKind::Lit(Literal::I32(1)))),
            right: Box::new(e(ExprKind::Lit(Literal::I32(2)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_sub() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::BinOp {
            op: BinOp::Sub,
            left: Box::new(e(ExprKind::Lit(Literal::I32(10)))),
            right: Box::new(e(ExprKind::Lit(Literal::I32(3)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_mul() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::BinOp {
            op: BinOp::Mul,
            left: Box::new(e(ExprKind::Lit(Literal::I32(6)))),
            right: Box::new(e(ExprKind::Lit(Literal::I32(7)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_div() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::BinOp {
            op: BinOp::Div,
            left: Box::new(e(ExprKind::Lit(Literal::I32(100)))),
            right: Box::new(e(ExprKind::Lit(Literal::I32(5)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_mod() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::BinOp {
            op: BinOp::Mod,
            left: Box::new(e(ExprKind::Lit(Literal::I32(17)))),
            right: Box::new(e(ExprKind::Lit(Literal::I32(5)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_comparison_lt() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::BinOp {
            op: BinOp::Lt,
            left: Box::new(e(ExprKind::Lit(Literal::I32(1)))),
            right: Box::new(e(ExprKind::Lit(Literal::I32(2)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_comparison_eq() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::BinOp {
            op: BinOp::Eq,
            left: Box::new(e(ExprKind::Lit(Literal::I32(5)))),
            right: Box::new(e(ExprKind::Lit(Literal::I32(5)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_logical_and() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::BinOp {
            op: BinOp::And,
            left: Box::new(e(ExprKind::Lit(Literal::Bool(true)))),
            right: Box::new(e(ExprKind::Lit(Literal::Bool(false)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_logical_or() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::BinOp {
            op: BinOp::Or,
            left: Box::new(e(ExprKind::Lit(Literal::Bool(false)))),
            right: Box::new(e(ExprKind::Lit(Literal::Bool(true)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    // -----------------------------------------------------------------------
    // Unary operations
    // -----------------------------------------------------------------------

    #[test]
    fn compile_not() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::UnaryOp {
            op: UnaryOp::Not,
            operand: Box::new(e(ExprKind::Lit(Literal::Bool(true)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_neg() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::UnaryOp {
            op: UnaryOp::Neg,
            operand: Box::new(e(ExprKind::Lit(Literal::I32(42)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    // -----------------------------------------------------------------------
    // Control flow
    // -----------------------------------------------------------------------

    #[test]
    fn compile_if_true_then_1_else_2() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::If {
            cond: Box::new(e(ExprKind::Lit(Literal::Bool(true)))),
            then_branch: Box::new(e(ExprKind::Lit(Literal::I32(1)))),
            else_branch: Box::new(e(ExprKind::Lit(Literal::I32(2)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_nested_if() {
        let mut codegen = Codegen::new();
        // if true then (if false then 10 else 20) else 30
        let expr = e(ExprKind::If {
            cond: Box::new(e(ExprKind::Lit(Literal::Bool(true)))),
            then_branch: Box::new(e(ExprKind::If {
                cond: Box::new(e(ExprKind::Lit(Literal::Bool(false)))),
                then_branch: Box::new(e(ExprKind::Lit(Literal::I32(10)))),
                else_branch: Box::new(e(ExprKind::Lit(Literal::I32(20)))),
            })),
            else_branch: Box::new(e(ExprKind::Lit(Literal::I32(30)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_if_with_arithmetic() {
        let mut codegen = Codegen::new();
        // if (1 < 2) then (10 + 20) else (100 - 50)
        let expr = e(ExprKind::If {
            cond: Box::new(e(ExprKind::BinOp {
                op: BinOp::Lt,
                left: Box::new(e(ExprKind::Lit(Literal::I32(1)))),
                right: Box::new(e(ExprKind::Lit(Literal::I32(2)))),
            })),
            then_branch: Box::new(e(ExprKind::BinOp {
                op: BinOp::Add,
                left: Box::new(e(ExprKind::Lit(Literal::I32(10)))),
                right: Box::new(e(ExprKind::Lit(Literal::I32(20)))),
            })),
            else_branch: Box::new(e(ExprKind::BinOp {
                op: BinOp::Sub,
                left: Box::new(e(ExprKind::Lit(Literal::I32(100)))),
                right: Box::new(e(ExprKind::Lit(Literal::I32(50)))),
            })),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    // -----------------------------------------------------------------------
    // Let bindings
    // -----------------------------------------------------------------------

    #[test]
    fn compile_let_x_42_in_x() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::Let {
            name: "x".into(),
            ty: None,
            value: Box::new(e(ExprKind::Lit(Literal::I32(42)))),
            body: Box::new(e(ExprKind::Var("x".into()))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_nested_let() {
        let mut codegen = Codegen::new();
        // let x = 10 in let y = 20 in x + y
        let expr = e(ExprKind::Let {
            name: "x".into(),
            ty: None,
            value: Box::new(e(ExprKind::Lit(Literal::I32(10)))),
            body: Box::new(e(ExprKind::Let {
                name: "y".into(),
                ty: None,
                value: Box::new(e(ExprKind::Lit(Literal::I32(20)))),
                body: Box::new(e(ExprKind::BinOp {
                    op: BinOp::Add,
                    left: Box::new(e(ExprKind::Var("x".into()))),
                    right: Box::new(e(ExprKind::Var("y".into()))),
                })),
            })),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_let_with_if() {
        let mut codegen = Codegen::new();
        // let x = 5 in if (x < 10) then x else 0
        let expr = e(ExprKind::Let {
            name: "x".into(),
            ty: None,
            value: Box::new(e(ExprKind::Lit(Literal::I32(5)))),
            body: Box::new(e(ExprKind::If {
                cond: Box::new(e(ExprKind::BinOp {
                    op: BinOp::Lt,
                    left: Box::new(e(ExprKind::Var("x".into()))),
                    right: Box::new(e(ExprKind::Lit(Literal::I32(10)))),
                })),
                then_branch: Box::new(e(ExprKind::Var("x".into()))),
                else_branch: Box::new(e(ExprKind::Lit(Literal::I32(0)))),
            })),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    // -----------------------------------------------------------------------
    // Pair / product types
    // -----------------------------------------------------------------------

    #[test]
    fn compile_pair_construction() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::Pair {
            left: Box::new(e(ExprKind::Lit(Literal::I32(1)))),
            right: Box::new(e(ExprKind::Lit(Literal::I32(2)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_fst_of_pair() {
        let mut codegen = Codegen::new();
        // fst (10, 20)
        let expr = e(ExprKind::Fst(Box::new(e(ExprKind::Pair {
            left: Box::new(e(ExprKind::Lit(Literal::I32(10)))),
            right: Box::new(e(ExprKind::Lit(Literal::I32(20)))),
        }))));
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_snd_of_pair() {
        let mut codegen = Codegen::new();
        // snd (10, 20)
        let expr = e(ExprKind::Snd(Box::new(e(ExprKind::Pair {
            left: Box::new(e(ExprKind::Lit(Literal::I32(10)))),
            right: Box::new(e(ExprKind::Lit(Literal::I32(20)))),
        }))));
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    // -----------------------------------------------------------------------
    // Sum types
    // -----------------------------------------------------------------------

    #[test]
    fn compile_inl() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::Inl {
            ty: Ty::Base(BaseTy::Bool),
            value: Box::new(e(ExprKind::Lit(Literal::I32(42)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_inr() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::Inr {
            ty: Ty::Base(BaseTy::I32),
            value: Box::new(e(ExprKind::Lit(Literal::Bool(true)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_case_analysis() {
        let mut codegen = Codegen::new();
        // case (inl[Bool] 42) of { x => x, y => 0 }
        let expr = e(ExprKind::Case {
            scrutinee: Box::new(e(ExprKind::Inl {
                ty: Ty::Base(BaseTy::Bool),
                value: Box::new(e(ExprKind::Lit(Literal::I32(42)))),
            })),
            left_var: "x".into(),
            left_body: Box::new(e(ExprKind::Var("x".into()))),
            right_var: "y".into(),
            right_body: Box::new(e(ExprKind::Lit(Literal::I32(0)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    // -----------------------------------------------------------------------
    // Copy
    // -----------------------------------------------------------------------

    #[test]
    fn compile_copy() {
        let mut codegen = Codegen::new();
        // copy(42)
        let expr = e(ExprKind::Copy(Box::new(e(ExprKind::Lit(
            Literal::I32(42),
        )))));
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    // -----------------------------------------------------------------------
    // Block
    // -----------------------------------------------------------------------

    #[test]
    fn compile_empty_block() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::Block(vec![]));
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_multi_expr_block() {
        let mut codegen = Codegen::new();
        // { 1; 2; 3 }
        let expr = e(ExprKind::Block(vec![
            e(ExprKind::Lit(Literal::I32(1))),
            e(ExprKind::Lit(Literal::I32(2))),
            e(ExprKind::Lit(Literal::I32(3))),
        ]));
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    // -----------------------------------------------------------------------
    // Region management
    // -----------------------------------------------------------------------

    #[test]
    fn compile_region_scope() {
        let mut codegen = Codegen::new();
        // region r { 42 }
        let expr = e(ExprKind::Region {
            name: "r".into(),
            body: Box::new(e(ExprKind::Lit(Literal::I32(42)))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    // -----------------------------------------------------------------------
    // Borrow / deref (identity at WASM level)
    // -----------------------------------------------------------------------

    #[test]
    fn compile_borrow_deref() {
        let mut codegen = Codegen::new();
        // *(&42)
        let expr = e(ExprKind::Deref(Box::new(e(ExprKind::Borrow(Box::new(
            e(ExprKind::Lit(Literal::I32(42))),
        ))))));
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    // -----------------------------------------------------------------------
    // Module-level: compile named functions
    // -----------------------------------------------------------------------

    #[test]
    fn compile_module_identity_function() {
        // fn identity(x: I32) -> I32 = x
        let module = AstModule {
            name: "test".into(),
            decls: vec![Decl::Fn {
                name: "identity".into(),
                params: vec![("x".into(), Ty::Base(BaseTy::I32))],
                ret_ty: Ty::Base(BaseTy::I32),
                body: e(ExprKind::Var("x".into())),
            }],
        };
        let wasm = compile_module(&module).expect("compilation failed");
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_module_add_function() {
        // fn add(a: I32, b: I32) -> I32 = a + b
        let module = AstModule {
            name: "test".into(),
            decls: vec![Decl::Fn {
                name: "add".into(),
                params: vec![
                    ("a".into(), Ty::Base(BaseTy::I32)),
                    ("b".into(), Ty::Base(BaseTy::I32)),
                ],
                ret_ty: Ty::Base(BaseTy::I32),
                body: e(ExprKind::BinOp {
                    op: BinOp::Add,
                    left: Box::new(e(ExprKind::Var("a".into()))),
                    right: Box::new(e(ExprKind::Var("b".into()))),
                }),
            }],
        };
        let wasm = compile_module(&module).expect("compilation failed");
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_module_with_main_fn() {
        // fn main() -> I32 = 42
        let module = AstModule {
            name: "test".into(),
            decls: vec![Decl::Fn {
                name: "main".into(),
                params: vec![],
                ret_ty: Ty::Base(BaseTy::I32),
                body: e(ExprKind::Lit(Literal::I32(42))),
            }],
        };
        let wasm = compile_module(&module).expect("compilation failed");
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_module_multiple_functions() {
        // fn double(x: I32) -> I32 = x + x
        // fn main() -> I32 = 21
        let module = AstModule {
            name: "test".into(),
            decls: vec![
                Decl::Fn {
                    name: "double".into(),
                    params: vec![("x".into(), Ty::Base(BaseTy::I32))],
                    ret_ty: Ty::Base(BaseTy::I32),
                    body: e(ExprKind::BinOp {
                        op: BinOp::Add,
                        left: Box::new(e(ExprKind::Var("x".into()))),
                        right: Box::new(e(ExprKind::Var("x".into()))),
                    }),
                },
                Decl::Fn {
                    name: "main".into(),
                    params: vec![],
                    ret_ty: Ty::Base(BaseTy::I32),
                    body: e(ExprKind::Lit(Literal::I32(21))),
                },
            ],
        };
        let wasm = compile_module(&module).expect("compilation failed");
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_module_function_with_if() {
        // fn abs(x: I32) -> I32 = if (x < 0) then (0 - x) else x
        let module = AstModule {
            name: "test".into(),
            decls: vec![Decl::Fn {
                name: "abs".into(),
                params: vec![("x".into(), Ty::Base(BaseTy::I32))],
                ret_ty: Ty::Base(BaseTy::I32),
                body: e(ExprKind::If {
                    cond: Box::new(e(ExprKind::BinOp {
                        op: BinOp::Lt,
                        left: Box::new(e(ExprKind::Var("x".into()))),
                        right: Box::new(e(ExprKind::Lit(Literal::I32(0)))),
                    })),
                    then_branch: Box::new(e(ExprKind::BinOp {
                        op: BinOp::Sub,
                        left: Box::new(e(ExprKind::Lit(Literal::I32(0)))),
                        right: Box::new(e(ExprKind::Var("x".into()))),
                    })),
                    else_branch: Box::new(e(ExprKind::Var("x".into()))),
                }),
            }],
        };
        let wasm = compile_module(&module).expect("compilation failed");
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_module_function_with_let() {
        // fn compute(a: I32) -> I32 = let b = a * 2 in b + 1
        let module = AstModule {
            name: "test".into(),
            decls: vec![Decl::Fn {
                name: "compute".into(),
                params: vec![("a".into(), Ty::Base(BaseTy::I32))],
                ret_ty: Ty::Base(BaseTy::I32),
                body: e(ExprKind::Let {
                    name: "b".into(),
                    ty: None,
                    value: Box::new(e(ExprKind::BinOp {
                        op: BinOp::Mul,
                        left: Box::new(e(ExprKind::Var("a".into()))),
                        right: Box::new(e(ExprKind::Lit(Literal::I32(2)))),
                    })),
                    body: Box::new(e(ExprKind::BinOp {
                        op: BinOp::Add,
                        left: Box::new(e(ExprKind::Var("b".into()))),
                        right: Box::new(e(ExprKind::Lit(Literal::I32(1)))),
                    })),
                }),
            }],
        };
        let wasm = compile_module(&module).expect("compilation failed");
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_module_function_calling_function() {
        // fn double(x: I32) -> I32 = x + x
        // fn main() -> I32 = double(21)
        let module = AstModule {
            name: "test".into(),
            decls: vec![
                Decl::Fn {
                    name: "double".into(),
                    params: vec![("x".into(), Ty::Base(BaseTy::I32))],
                    ret_ty: Ty::Base(BaseTy::I32),
                    body: e(ExprKind::BinOp {
                        op: BinOp::Add,
                        left: Box::new(e(ExprKind::Var("x".into()))),
                        right: Box::new(e(ExprKind::Var("x".into()))),
                    }),
                },
                Decl::Fn {
                    name: "main".into(),
                    params: vec![],
                    ret_ty: Ty::Base(BaseTy::I32),
                    body: e(ExprKind::App {
                        func: Box::new(e(ExprKind::Var("double".into()))),
                        arg: Box::new(e(ExprKind::Lit(Literal::I32(21)))),
                    }),
                },
            ],
        };
        let wasm = compile_module(&module).expect("compilation failed");
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_module_bool_function() {
        // fn is_positive(x: I32) -> Bool = x > 0
        let module = AstModule {
            name: "test".into(),
            decls: vec![Decl::Fn {
                name: "is_positive".into(),
                params: vec![("x".into(), Ty::Base(BaseTy::I32))],
                ret_ty: Ty::Base(BaseTy::Bool),
                body: e(ExprKind::BinOp {
                    op: BinOp::Gt,
                    left: Box::new(e(ExprKind::Var("x".into()))),
                    right: Box::new(e(ExprKind::Lit(Literal::I32(0)))),
                }),
            }],
        };
        let wasm = compile_module(&module).expect("compilation failed");
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_module_empty() {
        let module = AstModule {
            name: "empty".into(),
            decls: vec![],
        };
        let wasm = compile_module(&module).expect("compilation failed");
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    // -----------------------------------------------------------------------
    // Linear type lowering
    // -----------------------------------------------------------------------

    #[test]
    fn compile_drop_expression() {
        let mut codegen = Codegen::new();
        // let x = 42 in drop(x)  -- simplified: drop returns unit
        let expr = e(ExprKind::Let {
            name: "x".into(),
            ty: None,
            value: Box::new(e(ExprKind::Lit(Literal::I32(42)))),
            body: Box::new(e(ExprKind::Drop(Box::new(e(ExprKind::Var(
                "x".into(),
            )))))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_linear_let_binding() {
        let mut codegen = Codegen::new();
        // let! x = 42 in x  (linear let)
        let expr = e(ExprKind::LetLin {
            name: "x".into(),
            ty: None,
            value: Box::new(e(ExprKind::Lit(Literal::I32(42)))),
            body: Box::new(e(ExprKind::Var("x".into()))),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    // -----------------------------------------------------------------------
    // Complex expression combinations
    // -----------------------------------------------------------------------

    #[test]
    fn compile_complex_nested_expression() {
        let mut codegen = Codegen::new();
        // let a = 3 in
        //   let b = 4 in
        //     if (a < b)
        //       then (a * a + b * b)
        //       else 0
        let expr = e(ExprKind::Let {
            name: "a".into(),
            ty: None,
            value: Box::new(e(ExprKind::Lit(Literal::I32(3)))),
            body: Box::new(e(ExprKind::Let {
                name: "b".into(),
                ty: None,
                value: Box::new(e(ExprKind::Lit(Literal::I32(4)))),
                body: Box::new(e(ExprKind::If {
                    cond: Box::new(e(ExprKind::BinOp {
                        op: BinOp::Lt,
                        left: Box::new(e(ExprKind::Var("a".into()))),
                        right: Box::new(e(ExprKind::Var("b".into()))),
                    })),
                    then_branch: Box::new(e(ExprKind::BinOp {
                        op: BinOp::Add,
                        left: Box::new(e(ExprKind::BinOp {
                            op: BinOp::Mul,
                            left: Box::new(e(ExprKind::Var("a".into()))),
                            right: Box::new(e(ExprKind::Var("a".into()))),
                        })),
                        right: Box::new(e(ExprKind::BinOp {
                            op: BinOp::Mul,
                            left: Box::new(e(ExprKind::Var("b".into()))),
                            right: Box::new(e(ExprKind::Var("b".into()))),
                        })),
                    })),
                    else_branch: Box::new(e(ExprKind::Lit(Literal::I32(0)))),
                })),
            })),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_block_with_let_and_arithmetic() {
        let mut codegen = Codegen::new();
        // { let x = 10 in x; let y = 20 in y + 1 }
        let expr = e(ExprKind::Block(vec![
            e(ExprKind::Let {
                name: "x".into(),
                ty: None,
                value: Box::new(e(ExprKind::Lit(Literal::I32(10)))),
                body: Box::new(e(ExprKind::Var("x".into()))),
            }),
            e(ExprKind::Let {
                name: "y".into(),
                ty: None,
                value: Box::new(e(ExprKind::Lit(Literal::I32(20)))),
                body: Box::new(e(ExprKind::BinOp {
                    op: BinOp::Add,
                    left: Box::new(e(ExprKind::Var("y".into()))),
                    right: Box::new(e(ExprKind::Lit(Literal::I32(1)))),
                })),
            }),
        ]));
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    // -----------------------------------------------------------------------
    // String operations
    // -----------------------------------------------------------------------

    #[test]
    fn compile_string_new() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::StringNew {
            region: "r".into(),
            value: "hello".to_string(),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_string_concat() {
        let mut codegen = Codegen::new();
        let expr = e(ExprKind::StringConcat {
            left: Box::new(e(ExprKind::StringNew {
                region: "r".into(),
                value: "hello ".to_string(),
            })),
            right: Box::new(e(ExprKind::StringNew {
                region: "r".into(),
                value: "world".to_string(),
            })),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    #[test]
    fn compile_string_in_region() {
        let mut codegen = Codegen::new();
        // region r { String.new@r("test") }
        let expr = e(ExprKind::Region {
            name: "r".into(),
            body: Box::new(e(ExprKind::StringNew {
                region: "r".into(),
                value: "test".to_string(),
            })),
        });
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);
    }

    // -----------------------------------------------------------------------
    // Lambda compilation
    // -----------------------------------------------------------------------

    #[test]
    fn compile_simple_lambda() {
        // Test: (lambda (x : I32) (+ x 1))
        let mut codegen = Codegen::new();
        let expr = Expr {
            kind: ExprKind::Lambda {
                param: "x".into(),
                param_ty: Ty::Base(BaseTy::I32),
                body: Box::new(Expr {
                    kind: ExprKind::BinOp {
                        op: BinOp::Add,
                        left: Box::new(Expr {
                            kind: ExprKind::Var("x".into()),
                            span: Span::dummy(),
                        }),
                        right: Box::new(Expr {
                            kind: ExprKind::Lit(Literal::I32(1)),
                            span: Span::dummy(),
                        }),
                    },
                    span: Span::dummy(),
                }),
            },
            span: Span::dummy(),
        };
        let wasm = codegen.compile_program(&expr);
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);

        // Verify that a lambda was registered
        assert_eq!(codegen.lambda_fns.len(), 1);
        assert_eq!(codegen.lambda_fns[0].param, "x");
    }

    #[test]
    fn compile_lambda_application() {
        // Test: ((lambda (x : I32) (+ x 1)) 5)
        // Expected result: 6
        let module = AstModule {
            name: "test".into(),
            decls: vec![Decl::Fn {
                name: "main".into(),
                params: vec![],
                ret_ty: Ty::Base(BaseTy::I32),
                body: e(ExprKind::App {
                    func: Box::new(e(ExprKind::Lambda {
                        param: "x".into(),
                        param_ty: Ty::Base(BaseTy::I32),
                        body: Box::new(e(ExprKind::BinOp {
                            op: BinOp::Add,
                            left: Box::new(e(ExprKind::Var("x".into()))),
                            right: Box::new(e(ExprKind::Lit(Literal::I32(1)))),
                        })),
                    })),
                    arg: Box::new(e(ExprKind::Lit(Literal::I32(5)))),
                }),
            }],
        };
        let wasm = compile_module(&module).expect("compilation failed");
        assert_wasm_header(&wasm);
        validate_wasm(&wasm);

        // The WASM module should be valid and contain a lambda function
        // (The validation above checks that the WASM is well-formed)
    }

    // -----------------------------------------------------------------------
    // Type mapping
    // -----------------------------------------------------------------------

    #[test]
    fn ty_to_valtype_i32() {
        assert_eq!(ty_to_valtype(&Ty::Base(BaseTy::I32)), ValType::I32);
    }

    #[test]
    fn ty_to_valtype_i64() {
        assert_eq!(ty_to_valtype(&Ty::Base(BaseTy::I64)), ValType::I64);
    }

    #[test]
    fn ty_to_valtype_f32() {
        assert_eq!(ty_to_valtype(&Ty::Base(BaseTy::F32)), ValType::F32);
    }

    #[test]
    fn ty_to_valtype_f64() {
        assert_eq!(ty_to_valtype(&Ty::Base(BaseTy::F64)), ValType::F64);
    }

    #[test]
    fn ty_to_valtype_bool() {
        assert_eq!(ty_to_valtype(&Ty::Base(BaseTy::Bool)), ValType::I32);
    }

    #[test]
    fn ty_to_valtype_unit() {
        assert_eq!(ty_to_valtype(&Ty::Base(BaseTy::Unit)), ValType::I32);
    }

    #[test]
    fn ty_to_valtype_string() {
        assert_eq!(
            ty_to_valtype(&Ty::String("r".into())),
            ValType::I32
        );
    }
}
