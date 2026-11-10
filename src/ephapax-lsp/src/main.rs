#![forbid(unsafe_code)]
// SPDX-License-Identifier: MPL-2.0
// Owner: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Language Server Protocol (LSP) implementation
//!
//! Provides IDE support for Ephapax including:
//! - Syntax and type checking diagnostics
//! - Hover information with resolved types
//! - Go to definition
//! - Document symbols
//! - Keyword and declaration completions

use ephapax_driver::DriverError;
use ephapax_syntax::{Decl, Expr, ExprKind, ExternItem, Module, Span, Ty};
use std::collections::HashMap;
use std::sync::Mutex;
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

// ============================================================================
// Document state — cached parse results for each open file
// ============================================================================

/// Cached analysis of a single document.
#[derive(Debug)]
struct DocumentState {
    /// The raw source text.
    text: String,
    /// Parsed AST module (if parsing succeeded).
    module: Option<Module>,
    /// Declared symbols: name -> (span, type description).
    declarations: Vec<DeclInfo>,
}

/// Information about a top-level declaration.
#[derive(Debug, Clone)]
struct DeclInfo {
    name: String,
    kind: DeclKind,
    span: Span,
    /// Human-readable type signature.
    signature: String,
    /// Parameter names and types (for functions).
    params: Vec<(String, String)>,
    /// Return type (for functions).
    return_type: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DeclKind {
    Function,
    TypeAlias,
    /// `extern "abi" { ... }` item — `Fn` or `Type` extern.
    ExternFn,
    ExternType,
    /// `data` declaration (the parent type).
    Data,
    /// A constructor inside a `data` declaration.
    Constructor,
}

// ============================================================================
// LSP Backend
// ============================================================================

#[derive(Debug)]
struct Backend {
    client: Client,
    documents: Mutex<HashMap<Url, DocumentState>>,
    /// Number of the latest analysis started for each document. An
    /// analysis runs on the blocking pool, so an older one can finish
    /// after a newer one; only the latest may commit its result.
    generations: Mutex<HashMap<Url, u64>>,
}

impl Backend {
    fn new(client: Client) -> Self {
        Self {
            client,
            documents: Mutex::new(HashMap::new()),
            generations: Mutex::new(HashMap::new()),
        }
    }

    /// Parse, type-check, and cache analysis for a document. `None`: a
    /// newer analysis of the same document started meanwhile, so this
    /// result is stale and nothing was cached; do not publish it.
    async fn analyze_document(&self, uri: &Url, text: &str) -> Option<Vec<Diagnostic>> {
        let generation = {
            let mut generations = self.generations.lock().ok()?;
            let latest = generations.entry(uri.clone()).or_insert(0);
            *latest += 1;
            *latest
        };
        // The analysis reads imported files from disk, so it runs on the
        // blocking pool, not on the async worker that serves requests.
        let (owned_uri, owned_text) = (uri.clone(), text.to_string());
        let (diagnostics, module_opt) =
            match tokio::task::spawn_blocking(move || analyze(&owned_uri, &owned_text)).await {
                Ok(result) => result,
                Err(e) => (
                    vec![Diagnostic {
                        severity: Some(DiagnosticSeverity::ERROR),
                        source: Some("ephapax".to_string()),
                        message: format!("analysis failed: {e}"),
                        ..Diagnostic::default()
                    }],
                    None,
                ),
            };
        if self.generations.lock().ok()?.get(uri) != Some(&generation) {
            return None;
        }
        let declarations = module_opt
            .as_ref()
            .map(|m| extract_declarations(m, text))
            .unwrap_or_default();

        // Cache the state
        if let Ok(mut docs) = self.documents.lock() {
            docs.insert(
                uri.clone(),
                DocumentState {
                    text: text.to_string(),
                    module: module_opt,
                    declarations,
                },
            );
        }

        Some(diagnostics)
    }

    /// Find the declaration at a given position (for go-to-definition).
    fn find_declaration_at(&self, uri: &Url, position: Position) -> Option<(Url, Range)> {
        let docs = self.documents.lock().ok()?;
        let state = docs.get(uri)?;

        // Convert position to byte offset
        let offset = position_to_offset(&state.text, position)?;

        // Find the identifier at this position
        let word = word_at_offset(&state.text, offset)?;

        // Search declarations for a match
        for decl in &state.declarations {
            if decl.name == word {
                let range = span_to_range(&state.text, decl.span);
                return Some((uri.clone(), range));
            }
        }

        // Check if the word is a variable reference — walk the AST
        if let Some(module) = &state.module {
            for d in &module.decls {
                if let Decl::Fn {
                    name, body, params, ..
                } = d
                {
                    // Check if word matches a parameter
                    for (pname, _) in params {
                        if pname.as_str() == word {
                            // Parameter — defined at the function's own span
                            for decl_info in &state.declarations {
                                if decl_info.name == name.as_str() {
                                    return Some((
                                        uri.clone(),
                                        span_to_range(&state.text, decl_info.span),
                                    ));
                                }
                            }
                        }
                    }

                    // Check for let-bound variables in the body
                    if let Some(span) = find_let_binding_span(body, word) {
                        return Some((uri.clone(), span_to_range(&state.text, span)));
                    }
                }
            }
        }

        None
    }

    /// Get hover information at a position.
    fn hover_at(&self, uri: &Url, position: Position) -> Option<String> {
        let docs = self.documents.lock().ok()?;
        let state = docs.get(uri)?;

        let offset = position_to_offset(&state.text, position)?;
        let word = word_at_offset(&state.text, offset)?;

        // Check top-level declarations
        for decl in &state.declarations {
            if decl.name == word {
                let mut info = format!("**{}**\n\n", decl.name);
                info.push_str(&format!("`{}`\n\n", decl.signature));

                match decl.kind {
                    DeclKind::Function | DeclKind::ExternFn => {
                        if !decl.params.is_empty() {
                            info.push_str("**Parameters:**\n");
                            for (name, ty) in &decl.params {
                                info.push_str(&format!("- `{}`: `{}`\n", name, ty));
                            }
                        }
                        if let Some(ret) = &decl.return_type {
                            info.push_str(&format!("\n**Returns:** `{}`\n", ret));
                        }
                        if matches!(decl.kind, DeclKind::ExternFn) {
                            info.push_str("\n*Foreign function (extern)*\n");
                        }
                    }
                    DeclKind::TypeAlias => {
                        info.push_str("*Type alias*\n");
                    }
                    DeclKind::ExternType => {
                        info.push_str("*Foreign opaque type (extern)*\n");
                    }
                    DeclKind::Data => {
                        info.push_str("*Data type*\n");
                    }
                    DeclKind::Constructor => {
                        info.push_str("*Constructor*\n");
                    }
                }

                return Some(info);
            }
        }

        // Check for keywords
        let keyword_info = match word {
            "fn" => Some("**fn** — Function declaration\n\n`fn name(params): ReturnType = body`"),
            "let" => Some("**let** — Let binding (standard mode)\n\n`let x = expr in body`"),
            "let!" => Some("**let!** — Linear let binding\n\n`let! x = expr in body`\n\nThe bound value must be consumed exactly once."),
            "region" => Some("**region** — Region scope\n\n`region r { body }`\n\nAllocations within the region are freed when the region exits."),
            "if" => Some("**if** — Conditional expression\n\n`if cond then expr else expr`\n\nBoth branches must consume linear variables identically."),
            "case" => Some("**case** — Sum type elimination\n\n`case expr of inl x => body, inr y => body end`"),
            "__ffi" => Some("**__ffi** — Foreign function interface\n\n`__ffi(\"symbol\", arg1, arg2, ...)`\n\nCalls a native function loaded via dlopen."),
            "I32" | "I64" | "F32" | "F64" | "Bool" | "Unit" => Some("**Base type** — Primitive Ephapax type"),
            "String" => Some("**String** — Region-allocated string\n\n`String@r` — a string allocated in region `r`"),
            "linear" => Some("**linear** — Linearity marker\n\nMarks a value that must be consumed exactly once."),
            _ => None,
        };

        keyword_info.map(|s| s.to_string())
    }

    /// Get document symbols.
    fn document_symbols(&self, uri: &Url) -> Vec<DocumentSymbol> {
        let docs = match self.documents.lock() {
            Ok(d) => d,
            Err(_) => return Vec::new(),
        };
        let state = match docs.get(uri) {
            Some(s) => s,
            None => return Vec::new(),
        };

        state
            .declarations
            .iter()
            .map(|decl| {
                let range = span_to_range(&state.text, decl.span);
                let kind = match decl.kind {
                    DeclKind::Function | DeclKind::ExternFn => SymbolKind::FUNCTION,
                    DeclKind::TypeAlias | DeclKind::ExternType => SymbolKind::TYPE_PARAMETER,
                    DeclKind::Data => SymbolKind::ENUM,
                    DeclKind::Constructor => SymbolKind::ENUM_MEMBER,
                };

                #[allow(deprecated)] // DocumentSymbol::deprecated is itself deprecated
                DocumentSymbol {
                    name: decl.name.clone(),
                    detail: Some(decl.signature.clone()),
                    kind,
                    tags: None,
                    deprecated: None,
                    range,
                    selection_range: range,
                    children: None,
                }
            })
            .collect()
    }
}

// ============================================================================
// LSP trait implementation
// ============================================================================

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                completion_provider: Some(CompletionOptions {
                    resolve_provider: Some(false),
                    trigger_characters: Some(vec![".".to_string(), "@".to_string()]),
                    work_done_progress_options: WorkDoneProgressOptions::default(),
                    all_commit_characters: None,
                    completion_item: None,
                }),
                definition_provider: Some(OneOf::Left(true)),
                document_symbol_provider: Some(OneOf::Left(true)),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: "ephapax-lsp".to_string(),
                version: Some(env!("CARGO_PKG_VERSION").to_string()),
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "Ephapax LSP server initialized")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = params.text_document.text;

        if let Some(diagnostics) = self.analyze_document(&uri, &text).await {
            self.client
                .publish_diagnostics(uri, diagnostics, None)
                .await;
        }
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = &params.content_changes[0].text;

        if let Some(diagnostics) = self.analyze_document(&uri, text).await {
            self.client
                .publish_diagnostics(uri, diagnostics, None)
                .await;
        }
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        if let Some(text) = params.text {
            if let Some(diagnostics) = self
                .analyze_document(&params.text_document.uri, &text)
                .await
            {
                self.client
                    .publish_diagnostics(params.text_document.uri, diagnostics, None)
                    .await;
            }
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        // An analysis still in flight is now stale: it must not cache
        // state or publish diagnostics for a closed document.
        if let Ok(mut generations) = self.generations.lock() {
            *generations
                .entry(params.text_document.uri.clone())
                .or_insert(0) += 1;
        }
        // Clear diagnostics and cached state
        if let Ok(mut docs) = self.documents.lock() {
            docs.remove(&params.text_document.uri);
        }
        self.client
            .publish_diagnostics(params.text_document.uri, Vec::new(), None)
            .await;
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        if let Some(info) = self.hover_at(uri, position) {
            Ok(Some(Hover {
                contents: HoverContents::Markup(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value: info,
                }),
                range: None,
            }))
        } else {
            Ok(None)
        }
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let uri = &params.text_document_position_params.text_document.uri;
        let position = params.text_document_position_params.position;

        if let Some((target_uri, range)) = self.find_declaration_at(uri, position) {
            Ok(Some(GotoDefinitionResponse::Scalar(Location {
                uri: target_uri,
                range,
            })))
        } else {
            Ok(None)
        }
    }

    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> Result<Option<DocumentSymbolResponse>> {
        let symbols = self.document_symbols(&params.text_document.uri);
        if symbols.is_empty() {
            Ok(None)
        } else {
            Ok(Some(DocumentSymbolResponse::Nested(symbols)))
        }
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let uri = &params.text_document_position.text_document.uri;
        let mut completions = Vec::new();

        // Keyword completions
        let keywords = [
            ("fn", "Function declaration", "fn $1($2): $3 = $0"),
            ("let", "Let binding", "let $1 = $2 in $0"),
            ("let!", "Linear let binding", "let! $1 = $2 in $0"),
            ("if", "Conditional", "if $1 then $2 else $3"),
            (
                "case",
                "Case analysis",
                "case $1 of inl $2 => $3, inr $4 => $5 end",
            ),
            ("region", "Region scope", "region $1 { $0 }"),
            ("__ffi", "FFI call", "__ffi(\"$1\", $0)"),
        ];

        for (label, detail, snippet) in keywords {
            completions.push(CompletionItem {
                label: label.to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some(detail.to_string()),
                insert_text: Some(snippet.to_string()),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                ..Default::default()
            });
        }

        // Type completions
        for ty in &["I32", "I64", "F32", "F64", "Bool", "Unit", "String"] {
            completions.push(CompletionItem {
                label: ty.to_string(),
                kind: Some(CompletionItemKind::TYPE_PARAMETER),
                detail: Some("Base type".to_string()),
                ..Default::default()
            });
        }

        // Declaration completions from the current document
        if let Ok(docs) = self.documents.lock() {
            if let Some(state) = docs.get(uri) {
                for decl in &state.declarations {
                    let kind = match decl.kind {
                        DeclKind::Function | DeclKind::ExternFn => CompletionItemKind::FUNCTION,
                        DeclKind::TypeAlias | DeclKind::ExternType | DeclKind::Data => {
                            CompletionItemKind::TYPE_PARAMETER
                        }
                        DeclKind::Constructor => CompletionItemKind::ENUM_MEMBER,
                    };
                    completions.push(CompletionItem {
                        label: decl.name.clone(),
                        kind: Some(kind),
                        detail: Some(decl.signature.clone()),
                        ..Default::default()
                    });
                }
            }
        }

        Ok(Some(CompletionResponse::Array(completions)))
    }
}

// ============================================================================
// Helper functions
// ============================================================================

/// Extract declaration info from a parsed module. Each top-level
/// `Decl` may yield one or more `DeclInfo` entries: extern blocks
/// expand into one entry per item; data decls expand into one entry
/// for the parent type plus one per constructor.
fn extract_declarations(module: &Module, _source: &str) -> Vec<DeclInfo> {
    let mut out: Vec<DeclInfo> = Vec::new();
    for decl in &module.decls {
        match decl {
            Decl::Fn {
                name,
                params,
                ret_ty,
                body,
                visibility: _,
                type_params: _,
            } => {
                let param_strs: Vec<(String, String)> = params
                    .iter()
                    .map(|(n, t)| (n.to_string(), format_ty(t)))
                    .collect();

                let sig = format!(
                    "fn {}({}) -> {}",
                    name,
                    param_strs
                        .iter()
                        .map(|(n, t)| format!("{}: {}", n, t))
                        .collect::<Vec<_>>()
                        .join(", "),
                    format_ty(ret_ty)
                );

                out.push(DeclInfo {
                    name: name.to_string(),
                    kind: DeclKind::Function,
                    span: body.span,
                    signature: sig,
                    params: param_strs,
                    return_type: Some(format_ty(ret_ty)),
                });
            }
            Decl::Type {
                name,
                visibility: _,
                ty,
            } => out.push(DeclInfo {
                name: name.to_string(),
                kind: DeclKind::TypeAlias,
                span: Span::dummy(),
                signature: format!("type {} = {}", name, format_ty(ty)),
                params: Vec::new(),
                return_type: None,
            }),
            Decl::Const { name, ty, value } => out.push(DeclInfo {
                name: name.to_string(),
                kind: DeclKind::TypeAlias, // closest existing variant
                span: value.span,
                signature: format!(
                    "let {} {}= ...",
                    name,
                    ty.as_ref()
                        .map(|t| format!(": {} ", format_ty(t)))
                        .unwrap_or_default()
                ),
                params: Vec::new(),
                return_type: ty.as_ref().map(format_ty),
            }),
            Decl::Extern { abi, items } => {
                for item in items {
                    match item {
                        ExternItem::Fn {
                            name,
                            params,
                            ret_ty,
                        } => {
                            let param_strs: Vec<(String, String)> = params
                                .iter()
                                .map(|(n, t)| (n.to_string(), format_ty(t)))
                                .collect();
                            let sig = format!(
                                "extern \"{}\" fn {}({}) -> {}",
                                abi,
                                name,
                                param_strs
                                    .iter()
                                    .map(|(n, t)| format!("{}: {}", n, t))
                                    .collect::<Vec<_>>()
                                    .join(", "),
                                format_ty(ret_ty)
                            );
                            out.push(DeclInfo {
                                name: name.to_string(),
                                kind: DeclKind::ExternFn,
                                span: Span::dummy(),
                                signature: sig,
                                params: param_strs,
                                return_type: Some(format_ty(ret_ty)),
                            });
                        }
                        ExternItem::Type { name } => {
                            out.push(DeclInfo {
                                name: name.to_string(),
                                kind: DeclKind::ExternType,
                                span: Span::dummy(),
                                signature: format!("extern \"{}\" type {}", abi, name),
                                params: Vec::new(),
                                return_type: None,
                            });
                        }
                    }
                }
            }
            Decl::Data {
                name,
                type_params,
                constructors,
            } => {
                let header = if type_params.is_empty() {
                    format!("data {}", name)
                } else {
                    let tps = type_params
                        .iter()
                        .map(|tp| tp.to_string())
                        .collect::<Vec<_>>()
                        .join(", ");
                    format!("data {}({})", name, tps)
                };
                let ctor_summary = constructors
                    .iter()
                    .map(|c| {
                        if c.fields.is_empty() {
                            c.name.to_string()
                        } else {
                            let fs = c
                                .fields
                                .iter()
                                .map(format_ty)
                                .collect::<Vec<_>>()
                                .join(", ");
                            format!("{}({})", c.name, fs)
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(" | ");
                out.push(DeclInfo {
                    name: name.to_string(),
                    kind: DeclKind::Data,
                    span: Span::dummy(),
                    signature: format!("{} = {}", header, ctor_summary),
                    params: Vec::new(),
                    return_type: None,
                });

                for ctor in constructors {
                    let sig = if ctor.fields.is_empty() {
                        format!("{}: {}", ctor.name, name)
                    } else {
                        let fs = ctor
                            .fields
                            .iter()
                            .map(format_ty)
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("{}({}): {}", ctor.name, fs, name)
                    };
                    out.push(DeclInfo {
                        name: ctor.name.to_string(),
                        kind: DeclKind::Constructor,
                        span: Span::dummy(),
                        signature: sig,
                        params: ctor
                            .fields
                            .iter()
                            .enumerate()
                            .map(|(i, t)| (format!("f{}", i), format_ty(t)))
                            .collect(),
                        return_type: Some(name.to_string()),
                    });
                }
            }
        }
    }
    out
}

/// Format a type for display.
fn format_ty(ty: &Ty) -> String {
    use ephapax_syntax::BaseTy;
    match ty {
        Ty::Base(b) => match b {
            BaseTy::Unit => "()".to_string(),
            BaseTy::Bool => "Bool".to_string(),
            BaseTy::I32 => "I32".to_string(),
            BaseTy::I64 => "I64".to_string(),
            BaseTy::F32 => "F32".to_string(),
            BaseTy::F64 => "F64".to_string(),
        },
        Ty::Fun { param, ret } => format!("{} -> {}", format_ty(param), format_ty(ret)),
        Ty::Prod { left, right } => format!("({}, {})", format_ty(left), format_ty(right)),
        Ty::Sum { left, right } => format!("{} + {}", format_ty(left), format_ty(right)),
        Ty::Ref { inner, .. } => format!("Ref({})", format_ty(inner)),
        Ty::String(region) => format!("String@{}", region),
        Ty::Region { name, inner } => format!("Region({}, {})", name, format_ty(inner)),
        Ty::Borrow { inner, mutable } => format!(
            "&{}{}",
            if *mutable { "mut " } else { "" },
            format_ty(inner)
        ),
        Ty::Var(name) => name.to_string(),
        Ty::ForAll { var, body } => format!("forall {}. {}", var, format_ty(body)),
        Ty::Unif(id) => format!("?{}", id),
        Ty::List(inner) => format!("[{}]", format_ty(inner)),
        Ty::Tuple(elems) => {
            let parts: Vec<_> = elems.iter().map(format_ty).collect();
            format!("({})", parts.join(", "))
        }
        Ty::Effectful {
            param,
            ret,
            effects,
        } => {
            let effs = effects.join(" + ");
            format!("{} -> {} with {}", format_ty(param), format_ty(ret), effs)
        }
    }
}

/// Convert byte offset span to LSP range.
/// Load a document through the one front end (`ephapax-driver`, the same
/// pipeline `ephapax check` runs) and turn the outcome into diagnostics.
/// Imports resolve next to the document's file, then in the stdlib.
/// Returns the document's own core module when it parses.
fn analyze(uri: &Url, text: &str) -> (Vec<Diagnostic>, Option<Module>) {
    fn diagnostic(range: Range, source: &str, message: String) -> Diagnostic {
        Diagnostic {
            range,
            severity: Some(DiagnosticSeverity::ERROR),
            source: Some(source.to_string()),
            message,
            ..Diagnostic::default()
        }
    }

    let base_dir = uri
        .to_file_path()
        .ok()
        .and_then(|p| p.parent().map(|d| d.to_path_buf()));
    let stdlib = ephapax_driver::stdlib_dir(None);
    let program = match ephapax_driver::parse_source(
        text,
        "document",
        base_dir.as_deref(),
        stdlib.as_deref(),
    ) {
        Ok(program) => program,
        Err(e) => {
            return (
                vec![diagnostic(Range::default(), "ephapax", e.to_string())],
                None,
            )
        }
    };
    let diagnostics = match ephapax_driver::check_program(&program) {
        Ok(()) => Vec::new(),
        Err(e) => {
            // A type error in this document has a position. Any other
            // failure, or one in an imported module, goes at the top.
            let range = match &e {
                DriverError::Type { path, error, .. } if *path == program.root().file_path => {
                    span_to_range(text, error.span)
                }
                _ => Range::default(),
            };
            vec![diagnostic(range, "ephapax-typing", e.to_string())]
        }
    };
    (diagnostics, Some(program.root().core.clone()))
}

fn span_to_range(text: &str, span: Span) -> Range {
    let start = offset_to_position(text, span.start);
    let end = offset_to_position(text, span.end);
    Range { start, end }
}

/// Convert a byte offset to an LSP Position (line, character).
fn offset_to_position(text: &str, offset: usize) -> Position {
    let offset = offset.min(text.len());
    let before = &text[..offset];
    let line = before.matches('\n').count() as u32;
    let last_newline = before.rfind('\n').map(|i| i + 1).unwrap_or(0);
    let character = (offset - last_newline) as u32;
    Position { line, character }
}

/// Convert an LSP Position to a byte offset.
fn position_to_offset(text: &str, position: Position) -> Option<usize> {
    let mut line = 0u32;
    let mut offset = 0usize;

    for (i, ch) in text.char_indices() {
        if line == position.line {
            let col = (i - offset) as u32;
            if col == position.character {
                return Some(i);
            }
        }
        if ch == '\n' {
            if line == position.line {
                // Position is past end of line
                return Some(i);
            }
            line += 1;
            offset = i + 1;
        }
    }

    // Position at end of text
    if line == position.line {
        Some(text.len().min(offset + position.character as usize))
    } else {
        None
    }
}

/// Find the word (identifier) at a byte offset.
fn word_at_offset(text: &str, offset: usize) -> Option<&str> {
    if offset >= text.len() {
        return None;
    }

    // Find word boundaries
    let bytes = text.as_bytes();
    let mut start = offset;
    let mut end = offset;

    // Scan backwards to find word start
    while start > 0 && is_ident_char(bytes[start - 1]) {
        start -= 1;
    }

    // Scan forwards to find word end
    while end < bytes.len() && is_ident_char(bytes[end]) {
        end += 1;
    }

    if start == end {
        return None;
    }

    Some(&text[start..end])
}

/// Check if a byte is part of an identifier.
fn is_ident_char(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

/// Search an expression tree for a let binding with the given name.
/// Returns the span of the value expression (where the binding is defined).
fn find_let_binding_span(expr: &Expr, target: &str) -> Option<Span> {
    match &expr.kind {
        ExprKind::Let {
            name, value, body, ..
        }
        | ExprKind::LetLin {
            name, value, body, ..
        } => {
            if name.as_str() == target {
                return Some(value.span);
            }
            find_let_binding_span(value, target).or_else(|| find_let_binding_span(body, target))
        }
        ExprKind::Lambda { body, .. } => find_let_binding_span(body, target),
        ExprKind::App { func, arg } => {
            find_let_binding_span(func, target).or_else(|| find_let_binding_span(arg, target))
        }
        ExprKind::If {
            cond,
            then_branch,
            else_branch,
        } => find_let_binding_span(cond, target)
            .or_else(|| find_let_binding_span(then_branch, target))
            .or_else(|| find_let_binding_span(else_branch, target)),
        ExprKind::Case {
            scrutinee,
            left_body,
            right_body,
            ..
        } => find_let_binding_span(scrutinee, target)
            .or_else(|| find_let_binding_span(left_body, target))
            .or_else(|| find_let_binding_span(right_body, target)),
        ExprKind::Pair { left, right } | ExprKind::StringConcat { left, right } => {
            find_let_binding_span(left, target).or_else(|| find_let_binding_span(right, target))
        }
        ExprKind::BinOp { left, right, .. } => {
            find_let_binding_span(left, target).or_else(|| find_let_binding_span(right, target))
        }
        ExprKind::Fst(inner)
        | ExprKind::Snd(inner)
        | ExprKind::Inl { value: inner, .. }
        | ExprKind::Inr { value: inner, .. }
        | ExprKind::Drop(inner)
        | ExprKind::Copy(inner)
        | ExprKind::Borrow { inner, .. }
        | ExprKind::Deref(inner)
        | ExprKind::UnaryOp { operand: inner, .. }
        | ExprKind::StringLen(inner) => find_let_binding_span(inner, target),
        ExprKind::Region { body, .. } => find_let_binding_span(body, target),
        ExprKind::Block(exprs) | ExprKind::ListLit(exprs) | ExprKind::TupleLit(exprs) => {
            exprs.iter().find_map(|e| find_let_binding_span(e, target))
        }
        ExprKind::ListIndex { list, index } => {
            find_let_binding_span(list, target).or_else(|| find_let_binding_span(index, target))
        }
        ExprKind::TupleIndex { tuple, .. } => find_let_binding_span(tuple, target),
        ExprKind::FFI { args, .. } => args.iter().find_map(|a| find_let_binding_span(a, target)),
        ExprKind::Perform { args, .. } => {
            args.iter().find_map(|a| find_let_binding_span(a, target))
        }
        ExprKind::Handle { body, clauses } => find_let_binding_span(body, target).or_else(|| {
            clauses
                .iter()
                .find_map(|c| find_let_binding_span(&c.body, target))
        }),
        ExprKind::Match { scrutinee, arms } => {
            find_let_binding_span(scrutinee, target).or_else(|| {
                arms.iter().find_map(|arm| {
                    arm.guard
                        .as_deref()
                        .and_then(|g| find_let_binding_span(g, target))
                        .or_else(|| find_let_binding_span(&arm.body, target))
                })
            })
        }
        ExprKind::Var(_)
        | ExprKind::TypeApp { .. }
        | ExprKind::Lit(_)
        | ExprKind::StringNew { .. } => None,
    }
}

// extract_error_span removed — SpannedTypeError carries its own span.

// ============================================================================
// Entry point
// ============================================================================

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(Backend::new);
    Server::new(stdin, stdout, socket).serve(service).await;
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::{Path, PathBuf};

    /// Each `.eph` file below `dir`.
    fn eph_files(dir: &Path, out: &mut Vec<PathBuf>) {
        for entry in std::fs::read_dir(dir).into_iter().flatten().flatten() {
            let path = entry.path();
            let name = entry.file_name().to_string_lossy().into_owned();
            if path.is_dir() {
                if !matches!(
                    name.as_str(),
                    "target" | ".git" | ".claude" | "node_modules"
                ) {
                    eph_files(&path, out);
                }
            } else if name.ends_with(".eph") {
                out.push(path);
            }
        }
    }

    /// v2 plan rung E3: the LSP reports no diagnostic exactly when
    /// `ephapax-driver` loads the file, on every .eph file in the repo
    /// (LSP twin of src/ephapax-cli/tests/driver_agreement.rs).
    #[test]
    fn diagnostics_agree_with_the_driver_on_every_corpus_file() {
        let root = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .canonicalize()
            .expect("repo root");
        let stdlib = ephapax_driver::stdlib_dir(None);
        let mut files = Vec::new();
        eph_files(&root, &mut files);
        assert!(files.len() > 100, "corpus walk found too few files");

        let mut clean = 0;
        for path in &files {
            let text = std::fs::read_to_string(path).expect("read corpus file");
            let uri = Url::from_file_path(path).expect("file URL");
            let lsp_ok = analyze(&uri, &text).0.is_empty();
            let driver_ok = ephapax_driver::load_program(path, stdlib.as_deref()).is_ok();
            assert_eq!(lsp_ok, driver_ok, "{}", path.display());
            clean += usize::from(lsp_ok);
        }
        assert!(clean > 0, "no corpus file is clean: gate misconfigured");
    }
}
