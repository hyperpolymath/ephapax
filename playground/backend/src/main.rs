// SPDX-License-Identifier: AGPL-3.0-or-later
//! Ephapax Playground API Server
//!
//! Provides HTTP API for compiling Ephapax code to WebAssembly
//! Supports both affine and linear type checking modes

use axum::{
    extract::Json,
    http::StatusCode,
    response::{IntoResponse, Response},
    routing::{get, post},
    Router,
};
use serde::{Deserialize, Serialize};
use std::process::Command;
use tower_http::cors::CorsLayer;
use tracing::info;

/// Compilation request from client
#[derive(Debug, Deserialize)]
struct CompileRequest {
    /// Ephapax source code
    code: String,
    /// Type checking mode: "affine" or "linear"
    mode: CompileMode,
}

/// Type checking mode
#[derive(Debug, Deserialize, Clone, Copy)]
#[serde(rename_all = "lowercase")]
enum CompileMode {
    Affine,
    Linear,
}

/// Compilation result sent to client
#[derive(Debug, Serialize)]
struct CompileResponse {
    /// Compilation succeeded
    success: bool,
    /// WebAssembly binary (base64 encoded)
    #[serde(skip_serializing_if = "Option::is_none")]
    wasm: Option<String>,
    /// S-expression IR (for debugging)
    #[serde(skip_serializing_if = "Option::is_none")]
    sexpr: Option<String>,
    /// Compilation errors
    #[serde(skip_serializing_if = "Option::is_none")]
    errors: Option<Vec<String>>,
    /// Compilation warnings
    #[serde(skip_serializing_if = "Option::is_none")]
    warnings: Option<Vec<String>>,
}

/// API error response
#[derive(Debug, Serialize)]
struct ErrorResponse {
    error: String,
}

impl IntoResponse for ErrorResponse {
    fn into_response(self) -> Response {
        (StatusCode::INTERNAL_SERVER_ERROR, Json(self)).into_response()
    }
}

/// Health check endpoint
async fn health() -> &'static str {
    "Ephapax Playground API is running"
}

/// Compile Ephapax code to WebAssembly
async fn compile(
    Json(req): Json<CompileRequest>,
) -> Result<Json<CompileResponse>, ErrorResponse> {
    info!("Compile request: mode={:?}, code_len={}", req.mode, req.code.len());

    // Create temporary files for compilation
    let temp_dir = tempfile::TempDir::new()
        .map_err(|e| ErrorResponse { error: format!("Failed to create temp dir: {}", e) })?;

    let input_path = temp_dir.path().join("input.eph");
    let sexpr_path = temp_dir.path().join("output.sexpr");
    let wasm_path = temp_dir.path().join("output.wasm");

    // Write source code to temp file
    std::fs::write(&input_path, &req.code)
        .map_err(|e| ErrorResponse { error: format!("Failed to write input file: {}", e) })?;

    // Step 1: Compile to S-expression using ephapax-affine
    // TODO: When ephapax-linear is ready, route based on req.mode
    let compiler_path = "/var/mnt/eclipse/repos/ephapax/idris2/build/exec/ephapax-affine";

    let compile_output = Command::new(compiler_path)
        .arg(&input_path)
        .arg("-o")
        .arg(&sexpr_path)
        .output()
        .map_err(|e| ErrorResponse { error: format!("Failed to run compiler: {}", e) })?;

    // Check for compilation errors
    if !compile_output.status.success() {
        let stderr = String::from_utf8_lossy(&compile_output.stderr);
        let errors: Vec<String> = stderr
            .lines()
            .filter(|line| !line.trim().is_empty())
            .map(String::from)
            .collect();

        return Ok(Json(CompileResponse {
            success: false,
            wasm: None,
            sexpr: None,
            errors: Some(errors),
            warnings: None,
        }));
    }

    // Read S-expression IR
    let sexpr_content = std::fs::read_to_string(&sexpr_path)
        .map_err(|e| ErrorResponse { error: format!("Failed to read S-expr: {}", e) })?;

    // Step 2: Compile S-expression to WASM using Rust backend
    let backend_path = "/var/mnt/eclipse/repos/ephapax/rust/target/debug/ephapax-cli";

    let backend_output = Command::new(backend_path)
        .arg("compile")
        .arg(&sexpr_path)
        .arg("-o")
        .arg(&wasm_path)
        .output()
        .map_err(|e| ErrorResponse { error: format!("Failed to run backend: {}", e) })?;

    if !backend_output.status.success() {
        let stderr = String::from_utf8_lossy(&backend_output.stderr);
        return Ok(Json(CompileResponse {
            success: false,
            wasm: None,
            sexpr: Some(sexpr_content),
            errors: Some(vec![stderr.to_string()]),
            warnings: None,
        }));
    }

    // Read WASM binary and encode as base64
    let wasm_bytes = std::fs::read(&wasm_path)
        .map_err(|e| ErrorResponse { error: format!("Failed to read WASM: {}", e) })?;

    let wasm_base64 = base64::engine::general_purpose::STANDARD.encode(&wasm_bytes);

    // Parse warnings from stdout
    let stdout = String::from_utf8_lossy(&compile_output.stdout);
    let warnings: Vec<String> = stdout
        .lines()
        .filter(|line| line.contains("warning:") || line.contains("Warning:"))
        .map(String::from)
        .collect();

    Ok(Json(CompileResponse {
        success: true,
        wasm: Some(wasm_base64),
        sexpr: Some(sexpr_content),
        errors: None,
        warnings: if warnings.is_empty() { None } else { Some(warnings) },
    }))
}

#[tokio::main]
async fn main() {
    // Initialize tracing
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::from_default_env()
                .add_directive("ephapax_playground_api=debug".parse().unwrap()),
        )
        .init();

    info!("Starting Ephapax Playground API server");

    // Build router
    let app = Router::new()
        .route("/", get(health))
        .route("/api/compile", post(compile))
        .layer(CorsLayer::permissive()); // TODO: Restrict CORS in production

    // Start server
    let listener = tokio::net::TcpListener::bind("127.0.0.1:3000")
        .await
        .unwrap();

    info!("Listening on http://127.0.0.1:3000");

    axum::serve(listener, app).await.unwrap();
}
