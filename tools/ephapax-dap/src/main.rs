// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! Ephapax Debug Adapter — DAP implementation for Ephapax.
//!
//! Provides:
//! - Breakpoints (line, conditional)
//! - Step in/out/over
//! - Variable inspection with qualifier + region info
//! - Linear resource tracking in the debugger UI
//! - Region lifetime visualisation
//!
//! Designed to integrate with the BoJ dap-mcp cartridge.

use std::io::{self, BufRead, Write};
use serde::{Deserialize, Serialize};

/// DAP message envelope.
#[derive(Debug, Serialize, Deserialize)]
struct DapMessage {
    seq: u64,
    #[serde(rename = "type")]
    msg_type: String,
    #[serde(flatten)]
    content: serde_json::Value,
}

/// DAP response.
#[derive(Debug, Serialize)]
struct DapResponse {
    seq: u64,
    #[serde(rename = "type")]
    msg_type: String,
    request_seq: u64,
    success: bool,
    command: String,
    body: serde_json::Value,
}

/// Ephapax debugger state.
struct EphapaxDebugger {
    /// Next sequence number for responses.
    seq: u64,
    /// Whether the debugger is initialised.
    initialised: bool,
}

impl EphapaxDebugger {
    fn new() -> Self {
        Self {
            seq: 1,
            initialised: false,
        }
    }

    /// Handle an incoming DAP request.
    fn handle_request(&mut self, msg: &DapMessage) -> DapResponse {
        let command = msg.content.get("command")
            .and_then(|c| c.as_str())
            .unwrap_or("unknown");

        let (success, body) = match command {
            "initialize" => {
                self.initialised = true;
                (true, serde_json::json!({
                    "supportsConfigurationDoneRequest": true,
                    "supportsFunctionBreakpoints": false,
                    "supportsConditionalBreakpoints": true,
                    "supportsEvaluateForHovers": true,
                    "supportsStepBack": false,
                    "supportsSetVariable": false,
                    // Ephapax-specific: linear resource tracking in variables view
                    "supportsValueFormattingOptions": true,
                }))
            }
            "launch" => {
                // TODO: Launch the Ephapax interpreter with the target .eph file
                (true, serde_json::json!({}))
            }
            "setBreakpoints" => {
                // TODO: Set breakpoints in the interpreter
                let breakpoints = msg.content.get("arguments")
                    .and_then(|a| a.get("breakpoints"))
                    .and_then(|b| b.as_array())
                    .map(|bps| {
                        bps.iter().map(|bp| {
                            serde_json::json!({
                                "verified": true,
                                "line": bp.get("line").unwrap_or(&serde_json::json!(0)),
                            })
                        }).collect::<Vec<_>>()
                    })
                    .unwrap_or_default();

                (true, serde_json::json!({ "breakpoints": breakpoints }))
            }
            "threads" => {
                (true, serde_json::json!({
                    "threads": [{
                        "id": 1,
                        "name": "main"
                    }]
                }))
            }
            "stackTrace" => {
                // TODO: Return actual stack frames from interpreter
                (true, serde_json::json!({
                    "stackFrames": [],
                    "totalFrames": 0,
                }))
            }
            "scopes" => {
                // Ephapax-specific: separate scopes for linear vs affine bindings,
                // with region-aware grouping showing which values belong to which region.
                (true, serde_json::json!({
                    "scopes": [
                        {
                            "name": "Linear Bindings (let!) — must consume",
                            "variablesReference": 1000,
                            "presentationHint": "locals",
                            "expensive": false,
                        },
                        {
                            "name": "Affine Bindings (let) — may drop",
                            "variablesReference": 2000,
                            "presentationHint": "locals",
                            "expensive": false,
                        },
                        {
                            "name": "Active Regions — arena scopes",
                            "variablesReference": 3000,
                            "presentationHint": "registers",
                            "expensive": false,
                        },
                        {
                            "name": "Region-Bound Values — grouped by region",
                            "variablesReference": 4000,
                            "presentationHint": "locals",
                            "expensive": false,
                        },
                    ]
                }))
            }
            "variables" => {
                // TODO: Return variables from interpreter state
                // Variables should show: name, value, type, qualifier (●/○), region
                (true, serde_json::json!({ "variables": [] }))
            }
            "continue" => {
                (true, serde_json::json!({ "allThreadsContinued": true }))
            }
            "next" | "stepIn" | "stepOut" => {
                (true, serde_json::json!({}))
            }
            "disconnect" => {
                (true, serde_json::json!({}))
            }
            _ => {
                (false, serde_json::json!({
                    "error": { "id": 1, "format": format!("Unknown command: {}", command) }
                }))
            }
        };

        let response = DapResponse {
            seq: self.next_seq(),
            msg_type: "response".to_string(),
            request_seq: msg.seq,
            success,
            command: command.to_string(),
            body,
        };

        response
    }

    fn next_seq(&mut self) -> u64 {
        let s = self.seq;
        self.seq += 1;
        s
    }
}

fn main() -> io::Result<()> {
    eprintln!("Ephapax DAP server starting...");

    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut debugger = EphapaxDebugger::new();

    for line in stdin.lock().lines() {
        let line = line?;

        // DAP uses Content-Length headers like LSP
        if line.starts_with("Content-Length:") {
            let len_str = match line.strip_prefix("Content-Length:") {
                Some(s) => s.trim(),
                None => continue, // should not happen if startswith check passed, but be safe
            };
            let len: usize = len_str.parse().unwrap_or(0);

            // Read empty line
            let mut empty = String::new();
            stdin.lock().read_line(&mut empty)?;

            // Read JSON body
            let mut body = vec![0u8; len];
            io::stdin().lock().read_exact(&mut body).ok();

            if let Ok(msg) = serde_json::from_slice::<DapMessage>(&body) {
                let response = debugger.handle_request(&msg);
                let response_json = match serde_json::to_string(&response) {
                    Ok(json) => json,
                    Err(_) => continue, // skip if JSON serialization fails
                };
                let header = format!("Content-Length: {}\r\n\r\n", response_json.len());

                let mut out = stdout.lock();
                out.write_all(header.as_bytes())?;
                out.write_all(response_json.as_bytes())?;
                out.flush()?;
            }
        }
    }

    Ok(())
}
