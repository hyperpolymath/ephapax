# Ephapax Playground Requirements

## Vision

An interactive web playground for Ephapax, similar to the Quantum Computing Playground, but for exploring linear and affine type systems.

**Key Differentiator**: **Mode Toggle** - Switch between affine (permissive) and linear (strict) modes to see the difference in type checking behavior.

## Core Features

### 1. Code Editor

**Requirements**:
- Syntax highlighting for Ephapax
- Line numbers
- Auto-indentation
- Error underlining
- Type hints on hover

**Technology Options**:
- Monaco Editor (VS Code engine) - Rich, heavy (~2MB)
- CodeMirror 6 - Lighter, extensible (~500KB)
- **Recommendation**: CodeMirror 6 (better WASM integration)

**Implementation**:
```typescript
// ReScript wrapper for CodeMirror
module Editor = {
  type t
  @module("@codemirror/basic-setup")
  external basicSetup: array<extension> = "basicSetup"

  @module("./ephapax-mode")
  external ephapaxMode: unit => extension = "ephapaxMode"
}
```

### 2. Mode Toggle

**UI**:
```
[Affine Mode] / [Linear Mode]
 └─ Tooltip: "Affine allows implicit drops, Linear requires explicit consumption"
```

**Behavior**:
- Toggle sends different `--mode` flag to compiler
- Shows different error messages
- Highlights mode-specific issues

**Examples**:
```ephapax
let x = 42;
// ↓ compiles

// Affine: ✅ OK (implicit drop)
// Linear: ❌ ERROR: x not consumed
```

### 3. Compilation & Execution

**Workflow**:
```
User Code → Compile (affine/linear) → WASM → Execute → Display Result
```

**Components**:
- Compile button (F9)
- Progress indicator
- Result display (stdout, return value)
- Error display (type errors, runtime errors)

**Backend Options**:

#### Option A: Client-Side (WASM compiler)
Compile ephapax-affine to WASM, run in browser:
- ✅ No server needed
- ✅ Works offline
- ✅ Fast (no network latency)
- ❌ Large initial download (~2-5MB)
- ❌ Requires WASM-compatible compiler

#### Option B: Server-Side API
Backend service compiles code:
- ✅ Smaller client bundle
- ✅ Can use native compiler
- ✅ Easier updates
- ❌ Requires server/backend
- ❌ Network latency
- ❌ Rate limiting needed

**Recommendation**: Start with Option B, migrate to Option A later

### 4. Example Programs

**Categories**:
1. **Basics**: Hello world, arithmetic, functions
2. **Affine**: Implicit drops, ownership transfer
3. **Linear**: Explicit drops, exact-once usage
4. **Comparison**: Same program in both modes
5. **Advanced**: Regions, borrows, products/sums

**Example List**:
```
examples/
├── 01-hello-world.eph
├── 02-arithmetic.eph
├── 03-functions.eph
├── 10-affine-drop.eph       # Affine specific
├── 11-affine-transfer.eph
├── 20-linear-explicit.eph    # Linear specific
├── 21-linear-error.eph       # Shows error
├── 22-linear-fix.eph         # Fixed version
├── 30-comparison-drop.eph    # Both modes
├── 31-comparison-use.eph
├── 40-regions.eph            # Advanced
└── 41-borrows.eph
```

**UI**: Dropdown or sidebar with categories

### 5. Output Display

**Sections**:
1. **Compilation Output**:
   - Success: "Compiled successfully (629 bytes)"
   - Errors: Type errors with line numbers
   - Warnings: Unused variables

2. **Execution Output**:
   - stdout/stderr
   - Return value
   - Execution time
   - Memory usage

3. **Generated Code**:
   - Show S-expr IR (collapsible)
   - Show WASM (hex dump or wat format)

**Layout**:
```
┌─────────────────────────┬──────────────────┐
│                         │                  │
│  Code Editor            │  Examples        │
│  (Monaco/CodeMirror)    │  ├─ Basics       │
│                         │  ├─ Affine       │
│                         │  ├─ Linear       │
│  [Affine] / [Linear]    │  └─ Advanced     │
│  [Compile] [Run]        │                  │
│                         │                  │
├─────────────────────────┴──────────────────┤
│  Output                                    │
│  ├─ Compilation                            │
│  ├─ Execution                              │
│  └─ Generated Code                         │
└────────────────────────────────────────────┘
```

### 6. Share Functionality

**Features**:
- Generate shareable URL with code embedded
- Support for base64-encoded code in URL
- "Share" button copies URL to clipboard

**URL Format**:
```
https://ephapax.org/playground?mode=linear&code=<base64>
```

**Implementation**:
```typescript
// Encode code to URL
let shareUrl = (code: string, mode: Mode.t): string => {
  let encoded = Base64.encode(code)
  `${baseUrl}?mode=${Mode.toString(mode)}&code=${encoded}`
}
```

### 7. Type Visualization

**Interactive Features**:
- Hover over variable → show inferred type
- Click variable → highlight all uses
- Show linear/affine annotations
- Visualize context threading

**Example**:
```ephapax
let! x = 42;
     ^
     Type: i32 (linear)
     Status: not consumed
```

### 8. Educational Mode

**Features**:
- Step-by-step execution
- Show type checker decisions
- Highlight where linear check fails
- Explain why error occurred

**Example Flow**:
```
Step 1: Parse program ✅
Step 2: Type check function ✅
Step 3: Check let! binding...
  → Variable 'x' has linear type i32
  → Must be consumed exactly once
  → Reaching end of scope...
  → ❌ ERROR: 'x' not consumed

Suggestion: Add `drop(x)` before end of scope
```

## Technology Stack

### Frontend (ReScript + Deno)

**Core**:
- ReScript (type-safe, compiles to JS)
- Deno (runtime, no Node.js)
- Vite (bundler, dev server)

**Libraries**:
- CodeMirror 6 (editor)
- @codemirror/lang-rust (adapt for Ephapax)
- Base64 (URL encoding)
- Local storage (save code)

### Backend (Rust + Axum)

**API**:
```rust
POST /api/compile
{
  "code": "fn main() -> i32 { 42 }",
  "mode": "affine" | "linear"
}

Response:
{
  "success": true,
  "wasm": "<base64>",
  "ir": "(module ...)",
  "errors": []
}
```

**Endpoints**:
- `POST /api/compile` - Compile code
- `POST /api/execute` - Execute WASM
- `GET /api/examples` - List examples
- `GET /api/examples/:id` - Get example code

### Deployment

**Options**:

1. **Static + API** (Recommended):
   - Frontend: Cloudflare Pages / Netlify
   - Backend: Fly.io / Railway

2. **All-in-One**:
   - Frontend + Backend: Fly.io
   - Single container

3. **Local**:
   - `just playground` runs both

## MVP Scope

### Phase 1: Basic Playground (1-2 weeks)
- [ ] Code editor (CodeMirror)
- [ ] Mode toggle (affine/linear)
- [ ] Compile button
- [ ] Basic output display
- [ ] 5 example programs
- [ ] Local dev environment

### Phase 2: Polish (1 week)
- [ ] Share functionality
- [ ] Better error messages
- [ ] Syntax highlighting
- [ ] Example categories
- [ ] Responsive design

### Phase 3: Advanced (2 weeks)
- [ ] Type visualization
- [ ] Step-by-step execution
- [ ] Educational mode
- [ ] Performance metrics
- [ ] WASM inspection

### Phase 4: Production (1 week)
- [ ] Deploy frontend
- [ ] Deploy backend
- [ ] Custom domain
- [ ] Analytics
- [ ] Documentation

## File Structure

```
playground/
├── frontend/               # ReScript + Vite
│   ├── src/
│   │   ├── Editor.res      # CodeMirror wrapper
│   │   ├── ModeToggle.res  # Affine/Linear toggle
│   │   ├── Compiler.res    # API client
│   │   ├── Output.res      # Result display
│   │   ├── Examples.res    # Example loader
│   │   └── App.res         # Main component
│   ├── public/
│   │   └── examples/       # Example .eph files
│   ├── package.json        # Actually deno.json
│   └── vite.config.ts
├── backend/                # Rust + Axum
│   ├── src/
│   │   ├── main.rs         # API server
│   │   ├── compiler.rs     # Ephapax integration
│   │   ├── executor.rs     # WASM runner
│   │   └── examples.rs     # Example manager
│   └── Cargo.toml
├── docs/
│   └── API.md              # API documentation
└── README.md
```

## Example Code Snippets

### Affine vs Linear Comparison

```ephapax
// example: 30-comparison-drop.eph
// Try this in both modes to see the difference!

fn main() -> i32 {
    let x = 42;
    // Variable 'x' is not used after this point

    // In AFFINE mode:
    //   ✅ Compiles successfully
    //   📝 'x' is implicitly dropped

    // In LINEAR mode:
    //   ❌ Type error: variable 'x' not consumed
    //   💡 Fix: Add 'drop(x)' or use 'x'

    0
}
```

### Linear Explicit Drop

```ephapax
// example: 22-linear-fix.eph
// This works in both modes

fn main() -> i32 {
    let! x = 42;  // Linear binding
    drop(x);       // Explicit consumption
    0              // ✅ Compiles!
}
```

## Inspiration & References

### Similar Playgrounds

1. **Rust Playground** (play.rust-lang.org)
   - Clean UI
   - Mode toggle (edition)
   - Share button
   - Examples dropdown

2. **Quantum Computing Playground**
   - 3D visualization
   - Interactive
   - Educational focus

3. **TypeScript Playground**
   - Inline errors
   - Type information
   - Config options

**Ephapax Unique Angle**:
- Affine/Linear toggle (no other playground has this)
- Educational focus on resource management
- Compare same code in both modes
- Visualize linear type checking

## Success Metrics

**Adoption**:
- [ ] 100+ unique visitors/month
- [ ] 500+ compilations/month
- [ ] 10+ shared programs

**Educational**:
- [ ] Used in 3+ university courses
- [ ] Referenced in papers/blogs
- [ ] Community examples submitted

**Technical**:
- [ ] <2s compile time (p95)
- [ ] <100ms editor lag
- [ ] 95%+ uptime

## Next Steps

1. **Set up project structure**:
   ```bash
   mkdir -p playground/{frontend,backend}
   cd playground/frontend && deno init
   cd playground/backend && cargo init
   ```

2. **Implement basic editor**: CodeMirror + ReScript

3. **Create backend API**: Rust + Axum

4. **Add 5 examples**: hello, affine, linear, comparison, advanced

5. **Deploy MVP**: Fly.io + Cloudflare Pages

6. **Iterate based on feedback**

---

**Goal**: Launch playground within 2-4 weeks, coinciding with arXiv paper submission.
