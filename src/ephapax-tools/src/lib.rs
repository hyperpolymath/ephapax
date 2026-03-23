// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! Ephapax developer tools — linter, formatter, and documenter.
//!
//! These tools work in two modes:
//! - **Heuristic mode** (text-based): Fast, no compiler dependency beyond lexing.
//!   Used by the standalone LSP and BoJ cartridges.
//! - **AST mode**: Full precision, requires parsed AST from ephapax-parser.
//!   Used by the CLI and compiler-integrated LSP.

pub mod formatter;
pub mod linter;
pub mod documenter;
