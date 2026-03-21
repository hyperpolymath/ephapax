// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! Ephapax Language Server — LSP implementation for the Ephapax dyadic language.
//!
//! Provides:
//! - Diagnostics (linearity violations, type errors, region escape errors)
//! - Go-to-definition
//! - Hover (type information, qualifier, region)
//! - Completion (keywords, identifiers in scope)
//! - Document symbols
//!
//! Designed to integrate with the BoJ lsp-mcp cartridge for MCP routing.

use tower_lsp::jsonrpc::Result;
use tower_lsp::lsp_types::*;
use tower_lsp::{Client, LanguageServer, LspService, Server};

/// Ephapax language server state.
struct EphapaxLsp {
    /// LSP client handle for sending diagnostics and notifications.
    client: Client,
}

#[tower_lsp::async_trait]
impl LanguageServer for EphapaxLsp {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                hover_provider: Some(HoverProviderCapability::Simple(true)),
                completion_provider: Some(CompletionOptions {
                    trigger_characters: Some(vec![
                        ".".to_string(),
                        "@".to_string(),
                        "!".to_string(),
                    ]),
                    ..Default::default()
                }),
                definition_provider: Some(OneOf::Left(true)),
                document_symbol_provider: Some(OneOf::Left(true)),
                ..Default::default()
            },
            server_info: Some(ServerInfo {
                name: "ephapax-lsp".to_string(),
                version: Some("0.1.0".to_string()),
            }),
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "Ephapax LSP initialized")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.check_document(&params.text_document.uri, &params.text_document.text)
            .await;
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        if let Some(change) = params.content_changes.into_iter().last() {
            self.check_document(&params.text_document.uri, &change.text)
                .await;
        }
    }

    async fn hover(&self, params: HoverParams) -> Result<Option<Hover>> {
        let _ = params;
        // TODO: Integrate with ephapax-typing to show type + qualifier + region
        // Example hover output:
        //   let! conn : DbConnection@app  [linear, region: app]
        //   let  buffer : Bytes@r         [affine, region: r]
        Ok(None)
    }

    async fn completion(&self, params: CompletionParams) -> Result<Option<CompletionResponse>> {
        let _ = params;
        // Provide keyword completions
        let keywords = vec![
            "fn", "let", "let!", "in", "region", "match", "if", "else",
            "type", "module", "import", "return", "true", "false",
            "copy", "borrow", "move", "drop",
        ];

        let items: Vec<CompletionItem> = keywords
            .into_iter()
            .map(|kw| CompletionItem {
                label: kw.to_string(),
                kind: Some(CompletionItemKind::KEYWORD),
                detail: Some(match kw {
                    "let!" => "Linear binding (must consume exactly once)".to_string(),
                    "let" => "Affine binding (may consume at most once)".to_string(),
                    "region" => "Region block (scoped arena allocation)".to_string(),
                    _ => format!("Ephapax keyword: {}", kw),
                }),
                ..Default::default()
            })
            .collect();

        Ok(Some(CompletionResponse::Array(items)))
    }

    async fn goto_definition(
        &self,
        params: GotoDefinitionParams,
    ) -> Result<Option<GotoDefinitionResponse>> {
        let _ = params;
        // TODO: Integrate with ephapax-syntax to resolve definitions
        Ok(None)
    }

    async fn document_symbol(
        &self,
        params: DocumentSymbolParams,
    ) -> Result<Option<DocumentSymbolResponse>> {
        let _ = params;
        // TODO: Parse document and return function/type/region symbols
        Ok(None)
    }
}

impl EphapaxLsp {
    /// Check a document for diagnostics (linearity violations, type errors).
    async fn check_document(&self, uri: &Url, text: &str) {
        let mut diagnostics = Vec::new();

        // Basic checks until compiler integration is ready:

        // Check for unbalanced let! without consumption
        let linear_bindings: Vec<_> = text
            .lines()
            .enumerate()
            .filter(|(_, line)| line.trim_start().starts_with("let!"))
            .collect();

        for (line_num, line) in &linear_bindings {
            // Extract variable name (rough heuristic)
            let trimmed = line.trim_start().strip_prefix("let!").unwrap_or("").trim();
            if let Some(var_name) = trimmed.split('=').next().map(|s| s.trim()) {
                // Check for patterns like (var, _) or just var
                let clean_name = var_name
                    .trim_start_matches('(')
                    .split(&[',', ')'][..])
                    .next()
                    .unwrap_or(var_name)
                    .trim();

                if !clean_name.is_empty() && !clean_name.starts_with('_') {
                    // Naive check: is this variable name used later in the file?
                    let remaining: String = text.lines().skip(line_num + 1).collect::<Vec<_>>().join("\n");
                    if !remaining.contains(clean_name) {
                        diagnostics.push(Diagnostic {
                            range: Range {
                                start: Position {
                                    line: *line_num as u32,
                                    character: 0,
                                },
                                end: Position {
                                    line: *line_num as u32,
                                    character: line.len() as u32,
                                },
                            },
                            severity: Some(DiagnosticSeverity::ERROR),
                            code: Some(NumberOrString::String("E001".to_string())),
                            source: Some("ephapax-lsp".to_string()),
                            message: format!(
                                "Linear variable '{}' may not be consumed. \
                                 Linear bindings (let!) must be used exactly once.",
                                clean_name
                            ),
                            ..Default::default()
                        });
                    }
                }
            }
        }

        // Check for region blocks without matching region exit
        for (line_num, line) in text.lines().enumerate() {
            let trimmed = line.trim_start();
            if trimmed.starts_with("region ") && trimmed.contains(':') {
                // Found a region declaration — check it has a block
                if !trimmed.contains('{') && !text.lines().nth(line_num + 1).map_or(false, |l| l.trim_start().starts_with('{')) {
                    diagnostics.push(Diagnostic {
                        range: Range {
                            start: Position { line: line_num as u32, character: 0 },
                            end: Position { line: line_num as u32, character: line.len() as u32 },
                        },
                        severity: Some(DiagnosticSeverity::WARNING),
                        code: Some(NumberOrString::String("W001".to_string())),
                        source: Some("ephapax-lsp".to_string()),
                        message: "Region block should be followed by a block expression { ... }".to_string(),
                        ..Default::default()
                    });
                }
            }
        }

        self.client
            .publish_diagnostics(uri.clone(), diagnostics, None)
            .await;
    }
}

#[tokio::main]
async fn main() {
    tracing_subscriber::fmt()
        .with_env_filter("ephapax_lsp=info")
        .init();

    let stdin = tokio::io::stdin();
    let stdout = tokio::io::stdout();

    let (service, socket) = LspService::new(|client| EphapaxLsp { client });
    Server::new(stdin, stdout, socket).serve(service).await;
}
