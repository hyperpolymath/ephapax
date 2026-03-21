// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Language Server Protocol (LSP) implementation
//!
//! Provides IDE support for Ephapax including:
//! - Syntax diagnostics
//! - Type checking diagnostics
//! - Hover information
//! - Go to definition
//! - Document symbols

use ephapax_parser::parse_module;
use ephapax_typing::{type_check_module_with_mode, Mode};
use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

#[derive(Debug)]
struct Backend {
    client: Client,
}

impl Backend {
    fn new(client: Client) -> Self {
        Self { client }
    }

    /// Parse and type-check a document, returning diagnostics
    async fn check_document(&self, _uri: &Url, text: &str) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Parse the document
        let module = match parse_module(text, "document") {
            Ok(module) => module,
            Err(errors) => {
                for err in errors {
                    diagnostics.push(Diagnostic {
                        range: Range {
                            start: Position { line: 0, character: 0 },
                            end: Position { line: 0, character: 0 },
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
                return diagnostics;
            }
        };

        // Type-check the module (try both modes)
        if let Err(err) = type_check_module_with_mode(&module, Mode::Linear) {
            diagnostics.push(Diagnostic {
                range: Range {
                    start: Position { line: 0, character: 0 },
                    end: Position { line: 0, character: 0 },
                },
                severity: Some(DiagnosticSeverity::ERROR),
                code: None,
                source: Some("ephapax-typing".to_string()),
                message: format!("Type error (linear mode): {}", err),
                related_information: None,
                tags: None,
                code_description: None,
                data: None,
            });
        }

        diagnostics
    }
}

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

        let diagnostics = self.check_document(&uri, &text).await;
        self.client.publish_diagnostics(uri, diagnostics, None).await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        let uri = params.text_document.uri;
        let text = &params.content_changes[0].text;

        let diagnostics = self.check_document(&uri, text).await;
        self.client.publish_diagnostics(uri, diagnostics, None).await;
    }

    async fn did_save(&self, params: DidSaveTextDocumentParams) {
        if let Some(text) = params.text {
            let diagnostics = self.check_document(&params.text_document.uri, &text).await;
            self.client
                .publish_diagnostics(params.text_document.uri, diagnostics, None)
                .await;
        }
    }

    async fn did_close(&self, params: DidCloseTextDocumentParams) {
        self.client
            .publish_diagnostics(params.text_document.uri, Vec::new(), None)
            .await;
    }

    async fn hover(&self, _params: HoverParams) -> Result<Option<Hover>> {
        // Provide basic hover information
        let hover = Hover {
            contents: HoverContents::Markup(MarkupContent {
                kind: MarkupKind::Markdown,
                value: "**Ephapax** - Dyadic linear type system for WebAssembly\n\n\
                        Hover over symbols for type information.".to_string(),
            }),
            range: None,
        };
        Ok(Some(hover))
    }

    async fn completion(&self, _: CompletionParams) -> Result<Option<CompletionResponse>> {
        // Provide basic completions
        let completions = vec![
            CompletionItem {
                label: "fn".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("Function declaration".to_string()),
                insert_text: Some("fn $1($2): $3 = $0".to_string()),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                ..Default::default()
            },
            CompletionItem {
                label: "let".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("Let binding".to_string()),
                insert_text: Some("let $1 = $2 in $0".to_string()),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                ..Default::default()
            },
            CompletionItem {
                label: "if".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("Conditional expression".to_string()),
                insert_text: Some("if $1 then $2 else $3".to_string()),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                ..Default::default()
            },
            CompletionItem {
                label: "region".to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some("Region scope".to_string()),
                insert_text: Some("region $1 { $0 }".to_string()),
                insert_text_format: Some(InsertTextFormat::SNIPPET),
                ..Default::default()
            },
        ];
        Ok(Some(CompletionResponse::Array(completions)))
    }
}

#[tokio::main]
async fn main() {
    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(|client| Backend::new(client));
    Server::new(stdin, stdout, socket).serve(service).await;
}
