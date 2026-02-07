# Ephapax VS Code Extension

Official VS Code extension for the [Ephapax](https://github.com/hyperpolymath/ephapax) programming language.

## Features

### Syntax Highlighting

Full syntax highlighting for `.eph` files including:
- Keywords: `fn`, `let`, `let!`, `drop`, `if`, `then`, `else`, `case`, `region`
- Types: `I32`, `I64`, `F32`, `F64`, `Bool`, `String`, `Unit`, `Never`
- Operators: `->`, `*`, `+`, lambda (`λ` or `\`)
- Comments: `//` line comments and `/* */` block comments

### Language Server Integration

Powered by `ephapax-lsp`, providing:
- **Real-time diagnostics** - Syntax and type errors as you type
- **Hover information** - Type signatures and documentation
- **Code completion** - Context-aware suggestions
- **Go to definition** - Navigate to function/type definitions
- **Find references** - Find all usages of a symbol

### Mode Switcher

Ephapax supports two type system modes:

- **Linear Mode** 🔒 - Values must be used exactly once (strict)
- **Affine Mode** 🔓 - Values can be used at most once (allows dropping)

Switch between modes via:
- Click the status bar indicator
- Command Palette: `Ephapax: Switch Type System Mode`
- Keyboard shortcut (configurable)

The status bar shows the current mode: `🔒 Ephapax [LINEAR]` or `🔓 Ephapax [AFFINE]`

## Requirements

- **Ephapax compiler** must be installed and in your PATH
- **ephapax-lsp** language server (included with Ephapax)

Install Ephapax:
```bash
git clone https://github.com/hyperpolymath/ephapax
cd ephapax
cargo install --path src/ephapax-cli
cargo install --path src/ephapax-lsp
```

## Extension Settings

This extension contributes the following settings:

- `ephapax.mode`: Type system mode (`"linear"` or `"affine"`)
- `ephapax.lsp.path`: Path to ephapax-lsp executable (default: `"ephapax-lsp"`)
- `ephapax.lsp.trace`: LSP trace level (`"off"`, `"messages"`, or `"verbose"`)

## Commands

- `Ephapax: Switch Type System Mode` - Toggle between linear and affine modes
- `Ephapax: Restart Language Server` - Restart the LSP server
- `Ephapax: Show Current Mode` - Display current type system mode

## Usage

1. Open any `.eph` file
2. Syntax highlighting activates automatically
3. LSP provides diagnostics and IntelliSense
4. Click the status bar to switch modes
5. Enjoy type-safe linear/affine programming!

## Example Code

```ephapax
// Fibonacci in linear mode
fn fib(n: I32): I32 =
    if n <= 1 then
        n
    else
        fib(n - 1) + fib(n - 2)

fn main(): I32 =
    fib(30)
```

## Known Issues

- Debugger integration pending (tracked in Enhancement #1 Phase 4)
- Module import syntax not yet supported (tracked in Enhancement #2)

## Release Notes

### 0.1.0

Initial release:
- Syntax highlighting for Ephapax
- LSP client integration
- Mode switcher (linear/affine)
- Status bar mode indicator

## Contributing

Contributions welcome! See [CONTRIBUTING.md](https://github.com/hyperpolymath/ephapax/blob/main/CONTRIBUTING.md)

## License

PMPL-1.0-or-later

## More Information

- [Ephapax Repository](https://github.com/hyperpolymath/ephapax)
- [Report Issues](https://github.com/hyperpolymath/ephapax/issues)
- [Documentation](https://github.com/hyperpolymath/ephapax/tree/main/docs)
