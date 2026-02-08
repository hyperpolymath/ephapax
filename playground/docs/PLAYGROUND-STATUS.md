# Ephapax Playground - Current Status

**Date**: 2026-01-23
**Overall Completion**: 15%

## Assessment

The ephapax-playground repository currently exists as **scaffolding only**:

### What Exists
- ✅ Repository structure (RSR-compliant)
- ✅ README.adoc with concept documentation
- ✅ License files (PMPL-1.0)
- ✅ Metadata files (STATE.scm, META.scm, ECOSYSTEM.scm)
- ✅ CI/CD templates (.github/, .gitlab-ci.yml)

### What Does NOT Exist
- ❌ No web interface implementation
- ❌ No code editor component
- ❌ No compiler backend/API
- ❌ No example programs
- ❌ No frontend code (ReScript, HTML, CSS)
- ❌ No backend code (Rust API server)
- ❌ No build system configured

**STATE.scm shows**:
```scheme
(overall-completion . 15)
(components
  ((specification . 40)
   (linear-checker . 0)
   (parser . 0)
   (ephemeral-runtime . 0)))
```

## Comparison to Requirements

Based on `/var/mnt/eclipse/repos/ephapax/docs/PLAYGROUND-REQUIREMENTS.md`:

| Feature | Required | Current Status |
|---------|----------|----------------|
| Code Editor | CodeMirror 6 | ❌ Not implemented |
| Mode Toggle | Affine/Linear switch | ❌ Not implemented |
| Compiler Backend | Rust + Axum API | ❌ Not implemented |
| Example Programs | 5+ examples | ❌ No examples/ dir |
| Output Display | Compile + execution results | ❌ Not implemented |
| Share Functionality | Base64 URL encoding | ❌ Not implemented |
| Syntax Highlighting | Ephapax mode | ❌ Not implemented |

## Implementation Strategy

Given that no web interface exists, we need to build from scratch:

### Phase 1: MVP Backend (Week 1)
1. **API Server** (Rust + Axum)
   - POST /api/compile - Takes code + mode (affine/linear)
   - Returns: success/failure, WASM binary, errors
   - Integration: Calls ephapax-affine binary

2. **Example Files**
   - Create examples/ directory
   - Port examples from main repo:
     - hello.eph
     - linear-demo.eph
     - Affine vs linear comparison
     - HTTP server design snippet

### Phase 2: MVP Frontend (Week 2)
1. **ReScript + Deno Setup**
   - Initialize ReScript project
   - Configure Deno for runtime
   - Set up Vite for bundling

2. **Core UI Components**
   - CodeEditor.res (CodeMirror wrapper)
   - ModeToggle.res (Affine/Linear switch)
   - OutputPanel.res (Display results)
   - ExampleSelector.res (Load examples)

3. **Integration**
   - API client to backend
   - State management
   - Error handling

### Phase 3: Polish (Week 3)
1. Type visualization
2. Share functionality
3. Better error messages
4. Responsive design

## Immediate Next Actions

1. ✅ Create backend/ directory structure
2. ✅ Implement Rust API with /api/compile endpoint
3. ✅ Create examples/ directory with 5+ programs
4. ✅ Create frontend/ directory with ReScript setup
5. ✅ Implement basic editor + mode toggle
6. Deploy MVP to test domain

## Integration Points

### With Main Ephapax Repo
- **Compiler Binary**: Use `/var/mnt/eclipse/repos/ephapax/idris2/build/exec/ephapax-affine`
- **Rust Backend**: Use `/var/mnt/eclipse/repos/ephapax/rust/` crates
- **Examples**: Port from `/var/mnt/eclipse/repos/ephapax/examples/`

### Expected API Flow
```
User Code (in browser)
  ↓ POST /api/compile
Backend (Rust/Axum)
  ↓ Calls ephapax-affine
Compiler (Idris2)
  ↓ Outputs .sexpr
Backend (Rust)
  ↓ Calls ephapax-cli (Rust)
WASM Binary
  ↓ Returns to browser
Execute in browser WASM runtime
```

## Technology Stack Decisions

### Backend
- **Rust + Axum** (not Actix-web, per user preference)
- **WASM runtime**: wasmtime or wasmer for server-side execution
- **Process isolation**: Spawn ephapax-affine as subprocess

### Frontend
- **ReScript** (not TypeScript, per RSR policy)
- **Deno** (not Node.js, per RSR policy)
- **CodeMirror 6** (lighter than Monaco)
- **Vite** (bundler + dev server)

### Deployment
- **Frontend**: Cloudflare Pages or Netlify
- **Backend**: Fly.io or Railway
- **Domain**: playground.ephapax.org (or similar)

## Revised Timeline

Given current state (15% = scaffolding only):

- **Week 1 (Jan 23-29)**: Backend API + examples
- **Week 2 (Jan 30-Feb 5)**: Frontend UI + integration
- **Week 3 (Feb 6-12)**: Polish + deployment
- **Week 4 (Feb 13-19)**: Testing + documentation

**MVP Target**: February 12, 2026
**Full Launch**: February 26, 2026 (with arXiv paper)

## Decision: Build vs Wait

**Question**: Should we wait for ephapax-linear to be complete?

**Answer**: No - proceed with affine-only playground now:

### Rationale
1. Affine compiler already works (verified)
2. Mode toggle can be UI-only initially (both modes use affine compiler)
3. True linear support can be added when ephapax-linear is ready
4. Playground validates affine compiler and provides educational value immediately

### Mode Toggle Implementation
- **Phase 1 (Now)**: UI toggle, but both modes use ephapax-affine
- **Phase 2 (Later)**: When ephapax-linear exists, route to appropriate compiler
- **User Education**: Clearly indicate linear mode is "simulated" until full implementation

## Comparison to Referenced Playgrounds

### Rust Playground (play.rust-lang.org)
- ✅ Clean UI - **We need this**
- ✅ Examples dropdown - **We need this**
- ✅ Share button - **We need this**
- ✅ Edition toggle - **Our mode toggle equivalent**

### TypeScript Playground
- ✅ Inline errors - **We need this**
- ✅ Type information on hover - **We need this**
- ✅ Config options - **Our mode toggle**

### Quantum Computing Playground
- ⚠️ 3D visualization - **Not applicable**
- ✅ Educational focus - **We need this**
- ✅ Interactive - **We need this**

**Unique to Ephapax Playground**:
- Affine/Linear comparison side-by-side
- Linear type checking visualization
- Context threading explanation

## Success Metrics

### Technical
- [ ] Compile latency <2s (p95)
- [ ] Editor lag <100ms
- [ ] Uptime 95%+
- [ ] Mobile responsive

### Adoption
- [ ] 100+ unique visitors/month
- [ ] 500+ compilations/month
- [ ] 10+ shared programs
- [ ] Referenced in 1+ course

## Conclusion

**Current State**: Repository scaffold only (15%)
**Next Step**: Build backend API + examples directory
**Blocker**: None - affine compiler works, can start immediately
**Estimated Time to MVP**: 3 weeks (backend + frontend + polish)
