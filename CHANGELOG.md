<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
# Changelog

All notable changes to Ephapax are documented here.

## [Unreleased]

### Changed
- Parser hardened: 80 production unwraps eliminated, proper ParseError propagation
- License headers: 13 files migrated from EUPL-1.2 to PMPL-1.0-or-later
- Test unwraps replaced with `.expect()` for better diagnostics

## [0.8.0] - 2026-03-16
- 80 examples across 8 categories
- Region-linear fusion type system
- `__ffi()` intrinsic for foreign function interface
- 15 compiler crates

## [0.7.0] - 2026-02-15
- Initial public release
- Linear type system with region annotations
- Pattern matching, modules, error handling
- REPL and interpreter

[Unreleased]: https://github.com/hyperpolymath/ephapax/compare/v0.8.0...HEAD
[0.8.0]: https://github.com/hyperpolymath/ephapax/compare/v0.7.0...v0.8.0
[0.7.0]: https://github.com/hyperpolymath/ephapax/releases/tag/v0.7.0
