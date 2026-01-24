# Ephapax: Academic & Practical Requirements for a Developed Language

## I. Theoretical Requirements (Academic Rigor)

### Current Status

**Already Complete** ✅:
- Formal semantics in Coq (`formal/*.v`)
- Progress theorem
- Preservation theorem
- Type safety proofs
- Linear/affine type system specification

**Still Needed** ⏳:

#### A. Core Theory Documents

1. **Language Specification** 🚧 Partial (`spec/SPEC.md`)
   - [ ] Complete syntax grammar (BNF/EBNF)
   - [ ] Typing rules (all constructs)
   - [ ] Operational semantics (small-step, big-step)
   - [ ] Type soundness theorem statements
   - [ ] Totality/termination conditions
   - **Format**: Technical report (LaTeX)
   - **Target Length**: 40-60 pages

2. **Metatheory Document** ⏳ Missing
   - [ ] Decidability proofs (type checking is decidable)
   - [ ] Complexity bounds (polynomial time type checking)
   - [ ] Principality (most general types)
   - [ ] Canonical forms lemmas
   - [ ] Substitution lemmas
   - **Format**: Supplementary technical appendix
   - **Target Length**: 20-30 pages

3. **Formal Semantics Paper** ⏳ Missing
   - [ ] Comparison with Linear Logic (Girard)
   - [ ] Relationship to Rust ownership
   - [ ] Connection to separation logic
   - [ ] Differences from Affine Haskell
   - [ ] Novel contributions (what's new)
   - **Format**: POPL/ICFP-style paper
   - **Target Length**: 12-15 pages
   - **Venue**: POPL, ICFP, ESOP, or OOPSLA

#### B. Type System Theory

4. **Subtyping & Polymorphism** ⏳ Missing
   - [ ] Region polymorphism (∀r. T@r)
   - [ ] Subtyping rules (if any)
   - [ ] Parametric polymorphism
   - [ ] Existential types (if planned)
   - **Format**: Section in spec or separate paper

5. **Effect System** ⏳ Future
   - [ ] Purity tracking
   - [ ] Exception effects
   - [ ] IO effects
   - [ ] Region effects
   - **Format**: Extension paper

#### C. Compilation Theory

6. **Compilation Correctness** ⏳ Missing
   - [ ] Source-to-IR correctness
   - [ ] IR-to-WASM correctness
   - [ ] End-to-end preservation
   - [ ] Behavioral equivalence proofs
   - **Format**: Extended technical report
   - **Target Length**: 30-40 pages
   - **Potential Venue**: JFP (Journal of Functional Programming)

7. **Optimization Theory** ⏳ Future
   - [ ] Safe optimizations (what can be done)
   - [ ] Region inference algorithm
   - [ ] Closure conversion correctness
   - [ ] Dead code elimination proofs
   - **Format**: Compiler theory paper

#### D. Foundations Documents

8. **Logical Relations** ⏳ Future (Advanced)
   - [ ] Step-indexed logical relations
   - [ ] Parametricity
   - [ ] Representation independence
   - **Format**: LICS or CSL paper
   - **Audience**: PL theory experts

9. **Mechanization Report** ⏳ Missing
   - [ ] Document Coq formalization choices
   - [ ] Admitted lemmas (if any)
   - [ ] Proof techniques used
   - [ ] Lines of proof code
   - [ ] Effort metrics
   - **Format**: CPP (Certified Programs and Proofs) paper
   - **Target**: CPP or ITP conference

### Priority Order (Theoretical)

1. **CRITICAL**: Complete language specification
2. **HIGH**: Compilation correctness
3. **HIGH**: Formal semantics paper
4. **MEDIUM**: Mechanization report
5. **MEDIUM**: Metatheory document
6. **LOW**: Logical relations (advanced theory)

---

## II. Practical Requirements (Demonstrating Worth)

### Current Status

**Already Complete** ✅:
- Working affine compiler
- End-to-end WASM generation
- Basic examples
- CI pipeline

**Still Needed** ⏳:

#### A. Language Tools

1. **Standard Library** 🚧 Minimal (`library/`)
   - [ ] String operations
   - [ ] Collections (List, Array, HashMap)
   - [ ] Option/Result types
   - [ ] File I/O
   - [ ] Network I/O (WASI)
   - **Target**: 50+ functions
   - **Documentation**: API docs

2. **Package Manager** ⏳ Missing
   - [ ] Package format (ephapax.toml)
   - [ ] Dependency resolution
   - [ ] Version management
   - [ ] Registry integration (JSR)
   - **Inspiration**: Cargo, Deno

3. **Build System** ⏳ Missing
   - [ ] Project scaffolding
   - [ ] Multi-file compilation
   - [ ] Incremental builds
   - [ ] Cross-compilation
   - **Inspiration**: Cargo

4. **REPL** 🚧 Exists (`src/ephapax-repl/`)
   - [ ] Interactive type checking
   - [ ] Multi-line input
   - [ ] History
   - [ ] Tab completion
   - **Target**: Usable for exploration

5. **Language Server (LSP)** ⏳ Missing
   - [ ] Diagnostics
   - [ ] Hover (type info)
   - [ ] Go-to-definition
   - [ ] Auto-completion
   - [ ] Refactoring support
   - **Target**: VS Code integration

6. **Formatter** ⏳ Missing
   - [ ] Consistent style
   - [ ] Configurable
   - [ ] Fast (<100ms)
   - **Inspiration**: rustfmt, prettier

7. **Documentation Generator** ⏳ Missing
   - [ ] API docs from comments
   - [ ] Type signatures
   - [ ] Examples
   - [ ] Cross-references
   - **Format**: HTML + search

#### B. Practical Demonstrations

8. **Benchmark Suite** ⏳ Missing
   - [ ] Micro-benchmarks (vs Rust, C)
   - [ ] Memory safety overhead
   - [ ] Compilation speed
   - [ ] Runtime performance
   - [ ] WASM size comparison
   - **Target**: Show competitive performance

9. **Real Applications** ⏳ Missing
   **Need at least 3-5 of:**
   - [ ] HTTP server
   - [ ] CLI tool (file processor)
   - [ ] Data structure library
   - [ ] Parser library
   - [ ] Crypto library
   - [ ] Web service
   - [ ] Database driver
   - **Target**: Show language is practical

10. **Case Studies** ⏳ Missing
    **Document:**
    - [ ] Porting Rust code to Ephapax
    - [ ] Writing safe C alternative
    - [ ] Memory leak prevention in practice
    - [ ] Linear types for protocol correctness
    - **Format**: Blog posts, papers

#### C. Educational Materials

11. **Tutorial Series** ⏳ Missing
    - [ ] Getting started (Hello World)
    - [ ] Understanding linear types
    - [ ] Working with regions
    - [ ] Building real applications
    - [ ] Advanced patterns
    - **Format**: Interactive tutorial website

12. **Book** ⏳ Future
    - [ ] "The Ephapax Programming Language"
    - [ ] Comprehensive guide
    - [ ] Theory + practice
    - [ ] Examples throughout
    - **Format**: mdBook (like Rust Book)
    - **Target**: 200-300 pages

13. **Video Content** ⏳ Future
    - [ ] Introduction to linear types
    - [ ] Building a project
    - [ ] Comparing with Rust
    - **Platform**: YouTube

### Priority Order (Practical)

1. **CRITICAL**: Standard library (50+ functions)
2. **CRITICAL**: 3+ real applications
3. **HIGH**: LSP (VS Code support)
4. **HIGH**: Tutorial series
5. **MEDIUM**: Benchmark suite
6. **MEDIUM**: Package manager
7. **LOW**: Book, videos (can come later)

---

## III. Case for arXiv: Dyadic Programming Language Design

### Thesis

**"Dyadic Language Design: Bootstrapping Linear Type Systems from Affine Foundations"**

### Abstract (Draft)

> We present Ephapax, a linearly-typed language for safe systems programming targeting WebAssembly. Unlike prior work, we demonstrate a novel **dyadic design methodology**: implementing a stricter type discipline (linear) by bootstrapping from a more permissive one (affine).
>
> This approach offers several benefits:
> 1. **Gradual strengthening**: Begin with easy-to-implement affine types, then add linear strictness
> 2. **Meta-circular validation**: The affine compiler compiles the linear compiler, which recompiles itself
> 3. **Practical migration**: Codebases can mix affine (prototyping) and linear (production) code
> 4. **Formal grounding**: Both disciplines are proven sound via Coq mechanization
>
> We formalize this dyadic methodology, prove its correctness, and demonstrate its effectiveness through a self-hosting implementation. Our results suggest that **staged type system development** is a viable alternative to monolithic language design.

### Paper Structure

#### 1. Introduction (2 pages)
- The challenge of linear type systems
- Why they're hard to implement correctly
- Our solution: staged development
- Contributions

#### 2. Background (2 pages)
- Linear vs affine types
- Prior work: Rust, Linear Haskell, Cyclone
- WebAssembly as compilation target

#### 3. Dyadic Design Methodology (3 pages)
- **Definition**: What makes a design "dyadic"?
- **Properties**: Formal requirements
- **Instantiation**: Affine + Linear as case study
- **Generalization**: Other pairs (e.g., pure + effectful)

#### 4. Formal Semantics (3 pages)
- Type system for affine mode
- Type system for linear mode
- Relationship between them
- Key theorems (soundness, progress, preservation)

#### 5. Implementation (3 pages)
- Compiler architecture
- Self-hosting bootstrap process
- Idris2 → Ephapax → WASM pipeline
- Code metrics

#### 6. Evaluation (3 pages)
- Case studies (applications)
- Performance benchmarks
- Compile-time overhead
- Safety guarantees validated

#### 7. Related Work (2 pages)
- Comparison with Rust
- Comparison with Linear Haskell
- Comparison with MLKit (regions)
- Uniqueness types (Clean)

#### 8. Discussion & Future Work (1 page)
- Lessons learned
- Applicability to other type systems
- Future extensions

#### 9. Conclusion (1 page)
- Summary of contributions
- Impact on PL design

**Total**: ~20 pages (arXiv format)

### Key Contributions

1. **Dyadic design methodology** (novel)
   - Formalized staged type system development
   - Proven correct via Coq

2. **Self-hosting linear compiler** (implementation)
   - First linearly-typed compiler in itself (?)
   - Full bootstrap from affine

3. **Practical language** (demonstration)
   - Real applications
   - WebAssembly target
   - Competitive performance

4. **Formal mechanization** (rigor)
   - Coq proofs of soundness
   - Compilation correctness
   - End-to-end guarantees

### Positioning

**Related Work**:
- Rust: practical but not formally verified
- Linear Haskell: formally verified but not self-hosting
- MLKit: regions but not linear/affine
- Cyclone: safe C but not formally verified

**Ephapax Unique**:
- ✅ Formally verified (Coq)
- ✅ Self-hosting (compiles itself)
- ✅ Practical (WASM target)
- ✅ Novel methodology (dyadic design)

### Potential Venues

1. **POPL** (ACM SIGPLAN Symposium on Principles of Programming Languages)
   - Deadline: June/July
   - Best for: Theory + formal methods
   - Acceptance: ~20%

2. **ICFP** (International Conference on Functional Programming)
   - Deadline: March
   - Best for: FP language design
   - Acceptance: ~25%

3. **OOPSLA** (Object-Oriented Programming, Systems, Languages & Applications)
   - Deadline: April
   - Best for: Language design + implementation
   - Acceptance: ~20%

4. **arXiv + Journal**
   - Post to arXiv first (immediate visibility)
   - Submit to TOPLAS (ACM Transactions on PL)
   - Or JFP (Journal of Functional Programming)

### Timeline to Paper

Assuming we complete the practical requirements:

- **Month 1**: Draft introduction + methodology
- **Month 2**: Write formal semantics section
- **Month 3**: Implementation + evaluation sections
- **Month 4**: Related work, polish, submit to arXiv
- **Month 5**: Submit to conference (ICFP March deadline)

---

## IV. Integration Plan

### Short-Term (1-3 Months)

**Theory**:
1. Complete language specification
2. Draft compilation correctness proofs
3. Begin formal semantics paper

**Practice**:
1. Expand standard library (50+ functions)
2. Build 3 real applications
3. Create tutorial series

**Paper**:
1. Outline dyadic design methodology paper
2. Draft introduction and background

### Medium-Term (3-6 Months)

**Theory**:
1. Finish compilation correctness
2. Submit formal semantics paper (ICFP/POPL)
3. Mechanization report (CPP)

**Practice**:
1. LSP implementation
2. VS Code extension
3. Benchmark suite

**Paper**:
1. Complete dyadic design paper
2. Submit to arXiv
3. Submit to OOPSLA or ICFP

### Long-Term (6-12 Months)

**Theory**:
1. Effect system
2. Logical relations (advanced)
3. Optimization theory

**Practice**:
1. Package manager
2. Build system
3. Documentation generator
4. "The Ephapax Book"

**Paper**:
1. Publish dyadic design paper
2. Follow-up papers (effects, optimizations)
3. Position paper on PL bootstrapping

---

## V. Success Metrics

### Academic Success

- [ ] 3+ peer-reviewed papers
- [ ] Citations from PL community
- [ ] Invited talks at conferences
- [ ] Adoption in PL courses

### Practical Success

- [ ] 100+ GitHub stars
- [ ] 10+ external contributors
- [ ] 50+ published packages
- [ ] Production deployments

### Impact Success

- [ ] Influences future language designs
- [ ] Cited in "Related Work" of other papers
- [ ] Taught in universities
- [ ] Industry adoption (even small scale)

---

## VI. Immediate Next Steps

### This Week

1. **Choose approach** for linear compiler (Option A or B from BOOTSTRAP-STATUS.md)
2. **Start language spec** (complete syntax grammar)
3. **Build first real app** (HTTP server or CLI tool)

### Next Week

1. **Expand standard library** (add 20 functions)
2. **Draft paper outline** (dyadic design methodology)
3. **Continue linear compiler** implementation

### This Month

1. **Complete linear compiler**
2. **Build 3 applications**
3. **Write 5 tutorial posts**
4. **Submit to arXiv** (pre-print)

---

## Appendix: Dyadic Design Beyond Ephapax

The methodology generalizes to other pairs:

| Permissive System | Strict System | Domain |
|-------------------|---------------|---------|
| Affine | Linear | Resource management |
| Impure | Pure | Effect tracking |
| Dynamic | Static | Type safety |
| Unproven | Proven | Formal verification |
| Prototype | Production | Software development |

**Future Work**: Apply dyadic design to:
- Pure/impure (Haskell → Idris)
- Dynamic/static (Lisp → Typed Lisp)
- Unverified/verified (C → Verified C)

This positions Ephapax not just as a language, but as a **methodology for PL design**.
