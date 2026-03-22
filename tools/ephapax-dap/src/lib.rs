#![forbid(unsafe_code)]
// SPDX-License-Identifier: PMPL-1.0-or-later
// Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
//
//! Ephapax DAP library — Debug Adapter Protocol core types and logic.
//!
//! Separates DAP protocol handling from the Ephapax interpreter integration,
//! so the debugger can be tested independently.

/// Re-export main module for library consumers.
pub mod dap {
    /// DAP capability flags for Ephapax.
    pub const SUPPORTS_CONDITIONAL_BREAKPOINTS: bool = true;
    pub const SUPPORTS_EVALUATE_FOR_HOVERS: bool = true;
    pub const SUPPORTS_STEP_BACK: bool = false;

    /// Ephapax-specific: variable display includes qualifier and region.
    ///
    /// In the debugger UI, each variable shows:
    /// - Name
    /// - Value
    /// - Type
    /// - Qualifier: ● (linear) or ○ (affine)
    /// - Region: which region owns this value's memory
    /// - State: owned | borrowed | consumed
    pub struct VariableDisplay {
        pub name: String,
        pub value: String,
        pub type_name: String,
        pub qualifier: Qualifier,
        pub region: Option<String>,
        pub state: OwnershipState,
    }

    pub enum Qualifier {
        Linear,
        Affine,
    }

    pub enum OwnershipState {
        Owned,
        Borrowed,
        Consumed,
    }

    impl std::fmt::Display for Qualifier {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            match self {
                Qualifier::Linear => write!(f, "● linear"),
                Qualifier::Affine => write!(f, "○ affine"),
            }
        }
    }

    impl std::fmt::Display for OwnershipState {
        fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
            match self {
                OwnershipState::Owned => write!(f, "owned"),
                OwnershipState::Borrowed => write!(f, "borrowed"),
                OwnershipState::Consumed => write!(f, "consumed"),
            }
        }
    }
}
