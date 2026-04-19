// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Fuzz testing infrastructure for Ephapax
//! 
//! This crate provides fuzz targets for cargo-fuzz to test:
//! - Parser robustness
//! - Type checker correctness
//! - WASM code generation safety