// SPDX-License-Identifier: MPL-2.0
// SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell

//! Fuzz testing infrastructure for Ephapax
//! 
//! This crate provides fuzz targets for cargo-fuzz to test:
//! - Parser robustness
//! - Type checker correctness
//! - WASM code generation safety