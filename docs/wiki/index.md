# Ephapax Documentation

Welcome to the Ephapax documentation. Ephapax is a programming language with a linear type system for safe memory management targeting WebAssembly.

## Quick Links

- [Getting Started](getting-started/installation.md)
- [Language Guide](language/syntax.md)
- [Reference](reference/keywords.md)
- [Tooling](tooling/cli.md)

## What is Ephapax?

Ephapax (from Greek ἐφάπαξ, "once for all") enforces that every linear resource is used exactly once, preventing:

- **Use-after-free**: Cannot access consumed resources
- **Memory leaks**: Must consume all linear resources
- **Double-free**: Cannot consume twice

## Core Concepts

| Concept | Description |
|---------|-------------|
| **Linearity** | Values used exactly once |
| **Regions** | Scoped bulk allocation |
| **Borrows** | Temporary non-consuming access |

## Documentation Sections

### Getting Started

- [Installation](getting-started/installation.md)
- [Hello World](getting-started/hello-world.md)
- [Tutorial](getting-started/tutorial.md)

### Language Guide

- [Syntax](language/syntax.md)
- [Types](language/types.md)
- [Linearity](language/linearity.md)
- [Regions](language/regions.md)
- [Borrowing](language/borrowing.md)

### Reference

- [Keywords](reference/keywords.md)
- [Operators](reference/operators.md)
- [Standard Library](reference/stdlib/index.md)

### Tooling

- [CLI](tooling/cli.md)
- [REPL](tooling/repl.md)
- [Language Server](tooling/lsp.md)

### Internals

- [Architecture](internals/architecture.md)
- [Type Checker](internals/type-checker.md)
- [Code Generation](internals/codegen.md)

### Contributing

- [Development Setup](contributing/development.md)
- [Testing](contributing/testing.md)
- [Style Guide](contributing/style-guide.md)
