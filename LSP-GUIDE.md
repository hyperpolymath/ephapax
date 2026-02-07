# Ephapax Language Server Protocol Guide

## Overview

The Ephapax Language Server (`ephapax-lsp`) provides IDE integration for Ephapax, offering real-time diagnostics, code completion, and hover information. It implements the [Language Server Protocol (LSP)](https://microsoft.github.io/language-server-protocol/), making it compatible with any LSP-capable editor.

## Features

### ✅ Implemented Features

- **Syntax Diagnostics**: Real-time parsing error detection and reporting
- **Type Checking Diagnostics**: Linear type checking in both affine and linear modes
- **Hover Information**: Type information and documentation on hover
- **Code Completion**: Context-aware keyword and snippet completion
- **Document Synchronization**: Automatic updates on file open, edit, and save

### 🚧 Planned Features

- Go to definition
- Find references
- Rename symbol
- Document symbols
- Workspace symbols
- Code actions (quick fixes)

## Installation

### Build from Source

```bash
cd ephapax
cargo build -p ephapax-lsp --release
```

The LSP server binary will be at `target/release/ephapax-lsp` (4.5MB).

### System-wide Installation

```bash
cargo install --path src/ephapax-lsp
```

## Editor Integration

### VS Code

Create `.vscode/settings.json`:

```json
{
  "ephapax.languageServer.command": "/path/to/ephapax-lsp",
  "ephapax.trace.server": "verbose"
}
```

Or install the Ephapax VS Code extension (coming soon).

### Neovim

Using `nvim-lspconfig`:

```lua
local lspconfig = require('lspconfig')
local configs = require('lspconfig.configs')

if not configs.ephapax then
  configs.ephapax = {
    default_config = {
      cmd = {'/path/to/ephapax-lsp'},
      filetypes = {'ephapax'},
      root_dir = lspconfig.util.root_pattern('.git', 'Cargo.toml'),
      settings = {},
    },
  }
end

lspconfig.ephapax.setup{}
```

### Emacs (LSP Mode)

Add to your `init.el`:

```elisp
(require 'lsp-mode)

(add-to-list 'lsp-language-id-configuration '(ephapax-mode . "ephapax"))

(lsp-register-client
 (make-lsp-client :new-connection (lsp-stdio-connection "/path/to/ephapax-lsp")
                  :activation-fn (lsp-activate-on "ephapax")
                  :server-id 'ephapax-lsp))

(add-hook 'ephapax-mode-hook #'lsp)
```

### Helix

Add to `~/.config/helix/languages.toml`:

```toml
[[language]]
name = "ephapax"
scope = "source.ephapax"
injection-regex = "ephapax"
file-types = ["eph"]
roots = [".git", "Cargo.toml"]
comment-token = "//"

[language.language-server]
command = "/path/to/ephapax-lsp"
```

## Usage

### Real-time Diagnostics

The LSP server provides diagnostics for:

**Syntax Errors:**
```ephapax
fn broken(x: I32: I32 = x
//               ^ Parse error: expected ')'
```

**Type Errors (Linear Mode):**
```ephapax
fn main(_unit: ()): I32 =
    region r {
        let s = String.new@r("hello") in
        42
        // ^ Type error (linear mode): unused linear value 's'
    }
```

### Code Completion

The LSP provides snippet-based completions for:

- `fn` → Function declaration template
- `let` → Let binding template
- `if` → Conditional expression template
- `region` → Region scope template

**Example:**

Type `fn` then Tab to expand to:
```ephapax
fn $1($2): $3 = $0
```

### Hover Information

Hover over any symbol to see:
- Type information
- Documentation
- Mode-specific behavior

## Configuration

### Mode Selection

The LSP server uses **linear mode** by default. To change modes, set environment variables:

```bash
EPHAPAX_MODE=affine ephapax-lsp
```

Or configure in your editor settings.

### Logging

Enable verbose logging for debugging:

```bash
RUST_LOG=ephapax_lsp=debug ephapax-lsp
```

Logs will appear in your editor's LSP output panel.

## Architecture

The LSP server is built on:

- **tower-lsp**: LSP framework for Rust
- **tokio**: Async runtime
- **ephapax-parser**: Syntax analysis
- **ephapax-typing**: Type checking with dyadic mode support

### Request Flow

```
Editor → LSP Server → ephapax-parser → AST
                   → ephapax-typing → Diagnostics
                   ← Response ← Editor
```

### Document Lifecycle

1. **didOpen**: Parse and type-check, publish diagnostics
2. **didChange**: Re-parse and re-check, update diagnostics
3. **didSave**: Optional re-validation
4. **didClose**: Clear diagnostics

## Troubleshooting

### LSP Server Not Starting

**Check binary path:**
```bash
which ephapax-lsp
/path/to/ephapax-lsp --version
```

**Check logs:**
- VS Code: Output → Ephapax Language Server
- Neovim: `:LspLog`
- Emacs: `*lsp-log*` buffer

### No Diagnostics

**Verify file extension:**
- File must have `.eph` extension
- Check editor's file type detection

**Check LSP connection:**
- Look for "Ephapax LSP server initialized" in logs
- Verify server is running: `ps aux | grep ephapax-lsp`

### Incorrect Diagnostics

**Mode mismatch:**
- Ensure LSP mode matches your code's intent
- Linear mode is stricter than affine mode

## Development

### Building in Development Mode

```bash
cargo build -p ephapax-lsp
./target/debug/ephapax-lsp
```

### Testing

```bash
cargo test -p ephapax-lsp
```

### Adding Features

The LSP server is structured for easy extension:

1. Add capability in `initialize()` (main.rs:82)
2. Implement handler method
3. Register handler in `LanguageServer` trait impl

## Contributing

Contributions welcome! See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines.

### High-Priority Features

- [ ] Go to definition support
- [ ] Find references
- [ ] Document symbols
- [ ] Semantic highlighting
- [ ] Inlay hints for types

## License

PMPL-1.0-or-later (Palimpsest License)

## Links

- **Repository**: https://github.com/hyperpolymath/ephapax
- **LSP Specification**: https://microsoft.github.io/language-server-protocol/
- **tower-lsp**: https://github.com/ebkalderon/tower-lsp
