# Installation

## Prerequisites

- **Rust** 1.83 or later
- **wasm32-unknown-unknown** target (for WASM compilation)
- **Coq** 8.18+ (optional, for formal proofs)

## From Source

### 1. Clone the Repository

```bash
git clone https://github.com/hyperpolymath/ephapax.git
cd ephapax
```

### 2. Install Rust WASM Target

```bash
rustup target add wasm32-unknown-unknown
```

### 3. Build

```bash
# Build all crates
cargo build --release

# Build for WASM
cargo build --release --target wasm32-unknown-unknown
```

### 4. Run Tests

```bash
cargo test --all-features
```

### 5. Install CLI (Optional)

```bash
cargo install --path .
```

## Verifying Installation

```bash
# Check version
ephapax --version

# Run REPL
ephapax repl
```

## Building Coq Proofs

```bash
cd formal
make depend
make
```

## Editor Setup

### VS Code

1. Install the Ephapax extension (coming soon)
2. Or use generic syntax highlighting

### Vim/Neovim

Add to your config:

```vim
" Ephapax file type
au BufRead,BufNewFile *.epx set filetype=ephapax
```

## Troubleshooting

### WASM Target Not Found

```bash
rustup target add wasm32-unknown-unknown
```

### Coq Not Found

Install Coq via your package manager:

```bash
# Ubuntu/Debian
sudo apt install coq

# macOS
brew install coq

# Nix
nix-env -iA nixpkgs.coq
```
