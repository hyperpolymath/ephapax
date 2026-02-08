# Ephapax Playground - Development Guide

**Status**: MVP Implementation In Progress (Week 1)
**Date**: 2026-01-23

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│  Frontend (ReScript + Deno + Vite)                          │
│  - Code editor (textarea, will upgrade to CodeMirror)       │
│  - Mode toggle (Affine / Linear)                            │
│  - Example selector                                          │
│  - Output display                                            │
└─────────────────────────────────────────────────────────────┘
                            │
                            │ HTTP POST /api/compile
                            │
┌─────────────────────────────────────────────────────────────┐
│  Backend API (Rust + Axum)                                   │
│  - Receives code + mode                                      │
│  - Calls ephapax-affine compiler                            │
│  - Calls ephapax-cli for WASM generation                    │
│  - Returns WASM binary + errors                              │
└─────────────────────────────────────────────────────────────┘
                            │
                            │ Subprocess calls
                            │
┌─────────────────────────────────────────────────────────────┐
│  Ephapax Toolchain                                           │
│  - ephapax-affine (Idris2): .eph → .sexpr                   │
│  - ephapax-cli (Rust): .sexpr → .wasm                       │
└─────────────────────────────────────────────────────────────┘
```

## Current Implementation Status

### Backend ✅ (Complete)
- [x] Rust API server with Axum
- [x] `/api/compile` endpoint
- [x] Integration with ephapax-affine
- [x] Integration with ephapax-cli
- [x] Error handling
- [x] CORS support

**Location**: `backend/src/main.rs`
**Dependencies**: See `backend/Cargo.toml`

### Examples ✅ (Complete)
- [x] 5 example programs created
- [x] README for examples
- [x] Covers affine, linear, and comparison

**Location**: `examples/`
**Files**:
- `01-hello-world.eph`
- `10-affine-drop.eph`
- `20-linear-demo.eph`
- `21-linear-explicit.eph`
- `30-comparison.eph`

### Frontend ✅ (MVP Complete)
- [x] ReScript project structure
- [x] Deno + Vite configuration
- [x] Main App component
- [x] Mode toggle UI
- [x] Code editor (basic textarea)
- [x] Example selector
- [x] Output display with tabs
- [x] API integration

**Location**: `frontend/`
**Entry point**: `frontend/src/App.res`

### Not Yet Implemented ⏳
- [ ] CodeMirror integration (using textarea for now)
- [ ] Syntax highlighting for Ephapax
- [ ] Type information on hover
- [ ] Share functionality (URL encoding)
- [ ] WASM execution in browser
- [ ] Example file serving (static or API)

## Running the Playground

### Prerequisites

1. **Ephapax toolchain built**:
   ```bash
   # From main ephapax repo
   cd /var/mnt/eclipse/repos/ephapax
   just build-affine  # Builds ephapax-affine
   cd rust && cargo build  # Builds ephapax-cli
   ```

2. **Deno installed** (for frontend):
   ```bash
   curl -fsSL https://deno.land/install.sh | sh
   ```

3. **Rust installed** (for backend):
   ```bash
   curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
   ```

4. **ReScript installed** (for frontend):
   ```bash
   npm install -g rescript
   # Or via Deno: deno install -A npm:rescript
   ```

### Backend Setup

```bash
cd backend

# Build and run
cargo run

# Server starts on http://localhost:3000
# Endpoints:
#   GET  /           - Health check
#   POST /api/compile - Compile Ephapax code
```

**Test the API**:
```bash
curl -X POST http://localhost:3000/api/compile \
  -H "Content-Type: application/json" \
  -d '{
    "code": "fn main() -> i32 { 42 }",
    "mode": "affine"
  }'
```

### Frontend Setup

```bash
cd frontend

# Compile ReScript to JavaScript
rescript build

# Start development server
deno task dev

# Open browser to http://localhost:5173
```

**Development workflow**:
1. Edit `.res` files in `frontend/src/`
2. Run `rescript build -w` for auto-recompilation
3. Vite will hot-reload the browser

### Full Stack Run

**Terminal 1 (Backend)**:
```bash
cd backend
cargo run
```

**Terminal 2 (ReScript Compiler)**:
```bash
cd frontend
rescript build -w
```

**Terminal 3 (Frontend Dev Server)**:
```bash
cd frontend
deno task dev
```

Then open http://localhost:5173 in your browser.

## Project Structure

```
ephapax-playground/
├── backend/                 # Rust API server
│   ├── src/
│   │   └── main.rs         # Axum server with /api/compile
│   └── Cargo.toml
│
├── frontend/                # ReScript + Deno frontend
│   ├── src/
│   │   ├── App.res         # Main application component
│   │   └── styles.css      # Global styles
│   ├── index.html          # Entry point
│   ├── vite.config.js      # Vite bundler config
│   ├── deno.json           # Deno package config
│   └── rescript.json       # ReScript compiler config
│
├── examples/                # Example Ephapax programs
│   ├── 01-hello-world.eph
│   ├── 10-affine-drop.eph
│   ├── 20-linear-demo.eph
│   ├── 21-linear-explicit.eph
│   ├── 30-comparison.eph
│   └── README.md
│
└── docs/
    ├── PLAYGROUND-REQUIREMENTS.md  # Original spec
    └── PLAYGROUND-STATUS.md        # Current status assessment
```

## API Reference

### POST /api/compile

**Request**:
```json
{
  "code": "fn main() -> i32 { 42 }",
  "mode": "affine"  // or "linear"
}
```

**Success Response**:
```json
{
  "success": true,
  "wasm": "<base64-encoded-wasm>",
  "sexpr": "(module ...)",
  "warnings": ["warning: unused variable"]  // optional
}
```

**Error Response**:
```json
{
  "success": false,
  "errors": [
    "type error: expected i32, got i64",
    "line 5: variable x not consumed"
  ],
  "warnings": null
}
```

## Development Roadmap

### Week 1 (Jan 23-29) ✅
- [x] Backend API implementation
- [x] Example programs
- [x] Frontend MVP with basic UI
- [x] Mode toggle
- [x] API integration

### Week 2 (Jan 30-Feb 5) 🚧
- [ ] Upgrade editor to CodeMirror
- [ ] Syntax highlighting for Ephapax
- [ ] Example file serving (fetch from `/examples/`)
- [ ] Share functionality (base64 URL encoding)
- [ ] Better error display with line numbers

### Week 3 (Feb 6-12)
- [ ] Type visualization on hover
- [ ] WASM execution in browser
- [ ] Execution output display
- [ ] Performance metrics
- [ ] Mobile responsive design

### Week 4 (Feb 13-19)
- [ ] Deploy frontend (Cloudflare Pages)
- [ ] Deploy backend (Fly.io)
- [ ] Custom domain setup
- [ ] Documentation
- [ ] User testing

## Testing

### Backend Tests
```bash
cd backend
cargo test
```

### Frontend Tests
```bash
cd frontend
# TODO: Add ReScript tests
```

### Integration Tests
```bash
# Test full compilation pipeline
cd backend
cargo run &
sleep 2

curl -X POST http://localhost:3000/api/compile \
  -H "Content-Type: application/json" \
  -d '{"code": "fn main() -> i32 { 42 }", "mode": "affine"}' \
  | jq .

kill %1
```

## Troubleshooting

### Backend fails to start
- Check that ephapax-affine binary exists at `/var/mnt/eclipse/repos/ephapax/idris2/build/exec/ephapax-affine`
- Check that ephapax-cli binary exists at `/var/mnt/eclipse/repos/ephapax/rust/target/debug/ephapax-cli`

### Frontend compilation errors
- Run `rescript clean && rescript build`
- Check that `@rescript/core` is installed: `npm install @rescript/core`

### API CORS errors
- Backend uses `CorsLayer::permissive()` for development
- For production, restrict CORS to playground domain

### ReScript not found
- Install globally: `npm install -g rescript`
- Or use Deno: `deno install -A npm:rescript`

## Next Steps

1. **Immediate** (this week):
   - Test backend with all example files
   - Implement example file serving endpoint
   - Upgrade editor to CodeMirror

2. **Short-term** (next 2 weeks):
   - Add syntax highlighting
   - Implement share functionality
   - Deploy MVP to test domain

3. **Long-term** (month 2):
   - Add linear compiler integration when ready
   - Implement educational mode
   - Add type visualization
   - Performance optimization

## Contributing

See main repo's `CONTRIBUTING.adoc` for contribution guidelines.

## License

SPDX-License-Identifier: PMPL-1.0-or-later-or-later
