#![forbid(unsafe_code)]
// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Language Server Protocol (LSP) implementation
//!
//! Provides IDE support for Ephapax including:
//! - Syntax and type checking diagnostics
//! - Hover information with resolved types
//! - Go to definition
//! - Document symbols
//! - Keyword and declaration completions

use ephapax_parser::parse_module;
use ephapax_syntax::{Decl, Expr, ExprKind, Module, Span, Ty};
use ephapax_typing::type_check_module;
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
}

// ============================================================================
// LSP Backend
// ============================================================================

#[derive(Debug)]
struct Backend {
    client: Client,
    documents: Mutex<HashMap<Url, DocumentState>>,
}

impl Backend {
    fn new(client: Client) -> Self {
        Self {
            client,
            documents: Mutex::new(HashMap::new()),
        }
    }

    /// Parse, type-check, and cache analysis for a document.
    async fn analyze_document(&self, uri: &Url, text: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut declarations = Vec::new();
        let mut module_opt = None;

        // Parse the document
        match parse_module(text, "document") {
            Ok(module) => {
                // Extract declarations
                declarations = extract_declarations(&module, text);
                module_opt = Some(module.clone());

                // Type-check
                if let Err(err) = type_check_module(&module) {
                    diagnostics.push(Diagnostic {
                        range: span_to_range(text, err.span),
                        severity: Some(DiagnosticSeverity::ERROR),
                        code: None,
                        source: Some("ephapax-typing".to_string()),
                        message: format!("Type error: {}", err),
                        related_information: None,
                        tags: None,
                        code_description: None,
                        data: None,
                    });
                }
            }
            Err(errors) => {
                for err in errors {
                    diagnostics.push(Diagnostic {
                        range: Range {
                            start: Position {
                                line: 0,
                                character: 0,
                            },
                            end: Position {
                                line: 0,
                                character: 0,
                            },
                        },
                        severity: Some(DiagnosticSeverity::ERROR),
                        code: None,
                        source: Some("ephapax".to_string()),
                        message: format!("Parse error: {:?}", err),
                        related_information: None,
                        tags: None,
                        code_description: None,
                        data: None,
                    });
                }
            }
        }

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

        diagnostics
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
                    name, body, params, type_params: _, ..
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
                    DeclKind::Function => {
                        if !decl.params.is_empty() {
                            info.push_str("**Parameters:**\n");
                            for (name, ty) in &decl.params {
                                info.push_str(&format!("- `{}`: `{}`\n", name, ty));
                            }
                        }
                        if let Some(ret) = &decl.return_type {
                            info.push_str(&format!("\n**Returns:** `{}`\n", ret));
                        }
                    }
                    DeclKind::TypeAlias => {
                        info.push_str("*Type alias*\n");
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
                    DeclKind::Function => SymbolKind::FUNCTION,
                    DeclKind::TypeAlias => SymbolKind::TYPE_PARAMETER,
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

        let diagnostics = self.analyze_document(&uri, &text).await;
        self.client
            .publish_diagnostics(uri, diagnostics, None)
            .await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = &params.content_changes[0].text;

        let diagnostics = self.analyze_document(&uri, text).await;
        self.client
            .publish_diagnostics(uri, diagnostics, None)
            .await;
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        if let Some(text) = params.text {
            let diagnostics = self
                .analyze_document(&params.text_document.uri, &text)
                .await;
            self.client
                .publish_diagnostics(params.text_document.uri, diagnostics, None)
                .await;
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
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
                        DeclKind::Function => CompletionItemKind::FUNCTION,
                        DeclKind::TypeAlias => CompletionItemKind::TYPE_PARAMETER,
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

/// Extract declaration info from a parsed module.
fn extract_declarations(module: &Module, _source: &str) -> Vec<DeclInfo> {
    module
        .decls
        .iter()
        .map(|decl| match decl {
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

                DeclInfo {
                    name: name.to_string(),
                    kind: DeclKind::Function,
                    span: body.span,
                    signature: sig,
                    params: param_strs,
                    return_type: Some(format_ty(ret_ty)),
                }
            }
            Decl::Type { name, visibility: _, ty } => DeclInfo {
                name: name.to_string(),
                kind: DeclKind::TypeAlias,
                span: Span::dummy(),
                signature: format!("type {} = {}", name, format_ty(ty)),
                params: Vec::new(),
                return_type: None,
            },
            Decl::Const { name, ty, value } => DeclInfo {
                name: name.to_string(),
                kind: DeclKind::TypeAlias, // closest existing variant
                span: value.span,
                signature: format!(
                    "let {} {}= ...",
                    name,
                    ty.as_ref().map(|t| format!(": {} ", format_ty(t))).unwrap_or_default()
                ),
                params: Vec::new(),
                return_type: ty.as_ref().map(|t| format_ty(t)),
            },
        })
        .collect()
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
        Ty::Borrow(inner) => format!("&{}", format_ty(inner)),
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
        | ExprKind::Borrow(inner)
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
        ExprKind::Var(_) | ExprKind::Lit(_) | ExprKind::StringNew { .. } => None,
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
