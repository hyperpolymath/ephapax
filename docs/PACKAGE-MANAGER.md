# Ephapax Package Manager

**Status**: ✅ Implemented
**Version**: 0.1.0

## Overview

The Ephapax package manager provides Cargo-style dependency management for Ephapax projects. It enables code reuse, version management, and easy distribution of libraries.

## Features

### ✅ Implemented

- **Project Initialization**: Create new projects with `ephapax.toml` manifests
- **Manifest Parsing**: Read and validate project metadata and dependencies
- **Dependency Resolution**: Resolve version constraints using backtracking algorithm
- **Local Registry**: Manage installed packages in `~/.ephapax/registry/`
- **Version Selection**: Automatically select latest compatible version
- **Transitive Dependencies**: Resolve nested dependency trees
- **CLI Commands**: `init`, `install`, `search`, `list`

### ⏳ Future Enhancements

- Remote registry support (publish to central repository)
- Git source dependencies
- Package publishing workflow
- Module import syntax in language
- Lockfile generation (`ephapax.lock`)

---

## Quick Start

### 1. Initialize a New Project

```bash
ephapax package init my-library
cd my-library
```

This creates:
```
my-library/
├── ephapax.toml      # Project manifest
└── src/
    └── main.eph      # Entry point
```

### 2. Edit ephapax.toml

```toml
[package]
name = "my-library"
version = "0.1.0"
authors = ["Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>"]
license = "PMPL-1.0-or-later"
description = "My awesome Ephapax library"

[dependencies]
linear-collections = "1.0"
affine-utils = { version = "0.5", mode = "affine" }
```

### 3. Install Dependencies

```bash
ephapax package install
```

Output:
```
✓ Resolved 2 packages:
  linear-collections v1.0.0
  affine-utils v0.5.2
```

---

## Manifest Format

### `ephapax.toml` Structure

```toml
[package]
name = "package-name"           # Required: lowercase, hyphens, no underscores
version = "0.1.0"               # Required: SemVer format
authors = ["Name <email>"]      # Required: at least one author
license = "PMPL-1.0-or-later"   # Required: SPDX identifier
description = "Short description"
repository = "https://github.com/user/repo"  # Optional
keywords = ["linear", "types"]  # Optional

[dependencies]
# Simple version constraint
simple-dep = "1.0"

# Detailed specification
detailed-dep = { version = "0.5", mode = "affine" }

# Path dependency (local development)
local-dep = { path = "../local-lib" }

# Git dependency (future)
git-dep = { git = "https://github.com/user/lib", tag = "v1.0" }

[dev_dependencies]
test-utils = "0.1"
```

### Package Name Rules

- Must be lowercase
- Can contain letters, numbers, and hyphens
- Must start with a letter
- Maximum 64 characters
- No underscores or uppercase

**Valid**: `my-lib`, `lib123`, `a`
**Invalid**: `MyLib`, `my_lib`, `123lib`

### Version Constraints

Uses SemVer syntax:

| Constraint | Meaning |
|------------|---------|
| `1.0` | Exactly 1.0.0 |
| `^1.0` | ≥1.0.0, <2.0.0 (compatible) |
| `~1.2` | ≥1.2.0, <1.3.0 (patch updates) |
| `*` | Any version |
| `>=1.0, <2.0` | Range |

### Mode-Specific Dependencies

Ephapax's dyadic type system (affine + linear modes) allows mode-specific dependencies:

```toml
[dependencies]
# This library requires affine mode compilation
affine-utils = { version = "0.5", mode = "affine" }

# This works in both modes
universal-lib = "1.0"
```

---

## CLI Commands

### `ephapax package init <name>`

Initialize a new Ephapax project.

**Options**:
- `--path <dir>`: Project directory (default: current directory)

**Example**:
```bash
ephapax package init my-project
ephapax package init my-lib --path ~/projects/my-lib
```

### `ephapax package install`

Install dependencies from `ephapax.toml`.

**Example**:
```bash
# In project directory with ephapax.toml
ephapax package install
```

**Output**:
```
⚙ Resolving dependencies...
✓ Resolved 3 packages:
  linear-collections v1.0.0
    └─ linear-core v0.5.0
  affine-utils v0.5.2
```

### `ephapax package search <query>`

Search for packages in the local registry.

**Example**:
```bash
ephapax package search linear
```

**Output**:
```
Found 2 package(s):
  linear-collections (1.0.0, 1.1.0)
  linear-core (0.5.0)
```

### `ephapax package list`

List all installed packages.

**Example**:
```bash
ephapax package list
```

**Output**:
```
Installed packages:
  linear-collections (1.0.0, 1.1.0)
  affine-utils (0.5.2)
  linear-core (0.5.0)
```

---

## Registry Structure

The local registry is stored at `~/.ephapax/registry/`:

```
~/.ephapax/
├── registry/
│   ├── index.json              # Package index
│   └── packages/
│       ├── linear-collections/
│       │   ├── 1.0.0/
│       │   │   ├── ephapax.toml
│       │   │   └── src/
│       │   │       └── lib.eph
│       │   └── 1.1.0/
│       │       └── ...
│       └── affine-utils/
│           └── 0.5.2/
│               └── ...
└── cache/                      # Downloaded packages (future)
```

### index.json Format

```json
{
  "packages": {
    "linear-collections": {
      "name": "linear-collections",
      "versions": [
        {
          "version": "1.0.0",
          "checksum": "a1b2c3...",
          "yanked": false
        },
        {
          "version": "1.1.0",
          "checksum": "d4e5f6...",
          "yanked": false
        }
      ]
    }
  }
}
```

---

## Dependency Resolution

The resolver uses a **backtracking algorithm** to find compatible version sets:

### Algorithm

1. Parse version constraints from manifest
2. For each dependency:
   - Find all versions in registry
   - Filter by version requirement
   - Select latest matching version
3. Load transitive dependencies recursively
4. Detect circular dependencies
5. Return topologically sorted dependency graph

### Example Resolution

**Input** (`ephapax.toml`):
```toml
[dependencies]
middle = "^1.0"
```

**Registry contains**:
- `middle` versions: 1.0.0, 1.1.0, 1.2.0
- `middle@1.2.0` depends on `leaf@^0.5`
- `leaf` versions: 0.5.0, 0.6.0

**Resolution process**:
1. Select `middle@1.2.0` (latest matching `^1.0`)
2. Load `middle@1.2.0` manifest → depends on `leaf@^0.5`
3. Select `leaf@0.6.0` (latest matching `^0.5`)
4. No more dependencies
5. Topological sort: `[leaf@0.6.0, middle@1.2.0]`

**Output**:
```
✓ Resolved 2 packages:
  middle v1.2.0
    └─ leaf v0.6.0
  leaf v0.6.0
```

### Conflict Detection

If two dependencies require incompatible versions:

```toml
[dependencies]
lib-a = "1.0"  # depends on common@^1.0
lib-b = "2.0"  # depends on common@^2.0
```

**Error**:
```
Error: Dependency conflict
lib-a requires common@^1.0
lib-b requires common@^2.0
No version satisfies both constraints
```

---

## Testing

### Unit Tests

```bash
# Test manifest parsing
cargo test --package ephapax-package manifest

# Test registry operations
cargo test --package ephapax-package registry

# Test dependency resolution
cargo test --package ephapax-package resolver

# Run all tests
cargo test --package ephapax-package
```

### Integration Test

```bash
# Create test project
cd /tmp
ephapax package init test-project
cd test-project

# Add dependencies to ephapax.toml
# (manually edit file)

# Install
ephapax package install
```

---

## API Documentation

### Rust API

The `ephapax-package` crate can be used programmatically:

```rust
use ephapax_package::{Manifest, Registry, Resolver};

// Load project manifest
let manifest = Manifest::from_file("ephapax.toml".as_ref())?;

// Open local registry
let registry = Registry::open()?;

// Resolve dependencies
let resolver = Resolver::new(&registry);
let resolved = resolver.resolve(&manifest)?;

// Print dependency tree
resolved.print();
```

### Public API

```rust
// Manifest operations
pub struct Manifest { /* ... */ }
impl Manifest {
    pub fn from_file(path: &Path) -> Result<Self, ManifestError>;
    pub fn from_str(content: &str) -> Result<Self, ManifestError>;
    pub fn validate(&self) -> Result<(), ManifestError>;
    pub fn to_file(&self, path: &Path) -> Result<(), ManifestError>;
    pub fn default_template(name: &str) -> Self;
}

// Registry operations
pub struct Registry { /* ... */ }
impl Registry {
    pub fn open() -> Result<Self, RegistryError>;
    pub fn has_package(&self, name: &str, version: &str) -> bool;
    pub fn get_versions(&self, name: &str) -> Vec<String>;
    pub fn install_package(&mut self, name: &str, version: &str, source_dir: &Path) -> Result<(), RegistryError>;
    pub fn load_manifest(&self, name: &str, version: &str) -> Result<Manifest, RegistryError>;
    pub fn search(&self, query: &str) -> Vec<String>;
}

// Dependency resolution
pub struct Resolver<'a> { /* ... */ }
impl<'a> Resolver<'a> {
    pub fn new(registry: &'a Registry) -> Self;
    pub fn resolve(&self, manifest: &Manifest) -> Result<ResolvedGraph, ResolverError>;
}

pub struct ResolvedGraph {
    pub packages: IndexMap<String, ResolvedPackage>;
}
impl ResolvedGraph {
    pub fn topological_order(&self) -> Vec<String>;
    pub fn print(&self);
}
```

---

## Future Enhancements

### Phase 2: Remote Registry

Add support for publishing to and installing from a central registry:

```bash
# Publish package
ephapax package publish

# Install from remote
ephapax package install linear-collections@1.0
```

**Implementation**:
- HTTP API for package upload/download
- Authentication (API tokens)
- Package verification (checksums, signatures)

### Phase 3: Module Import Syntax

Extend the Ephapax language with module imports:

```ephapax
// Import a module from a package
import "linear-collections/vec" as Vec
import "affine-utils/option" as Opt

fn main(): I32 =
  let v = Vec.new() in
  let opt = Opt.some(42) in
  ...
```

**Implementation**:
- Parser: Add `import` statement
- Type checker: Resolve module paths to registry packages
- Codegen: Link multiple modules into single WASM

### Phase 4: Lockfile

Generate `ephapax.lock` for reproducible builds:

```toml
# ephapax.lock
[[package]]
name = "linear-collections"
version = "1.0.0"
checksum = "a1b2c3..."

[[package]]
name = "linear-core"
version = "0.5.0"
checksum = "d4e5f6..."
dependencies = []
```

---

## Troubleshooting

### "No ephapax.toml found"

**Cause**: Running `ephapax package install` outside a project directory.

**Solution**:
```bash
# Initialize project first
ephapax package init my-project
cd my-project
ephapax package install
```

### "Package not found: foo"

**Cause**: Package not in local registry.

**Solution**:
```bash
# List available packages
ephapax package list

# Search for similar packages
ephapax package search foo
```

### "Dependency conflict"

**Cause**: Two dependencies require incompatible versions of the same package.

**Solution**:
- Update dependency versions in `ephapax.toml`
- Check if newer versions are compatible
- Use `^` (caret) constraints for flexibility

---

## Comparison with Other Package Managers

| Feature | Ephapax | Cargo (Rust) | npm (Node.js) |
|---------|---------|--------------|---------------|
| Manifest format | TOML | TOML | JSON |
| Version resolution | Backtracking | SAT solver | Backtracking |
| Local registry | Yes | Yes | Global cache |
| Lockfile | Planned | ✓ | ✓ |
| Remote registry | Planned | crates.io | npmjs.com |
| Mode-specific deps | ✓ (affine/linear) | Features | - |

---

## Related Documentation

- [ENHANCEMENTS-STATUS.md](../ENHANCEMENTS-STATUS.md) - Overall enhancement roadmap
- [Cargo Book](https://doc.rust-lang.org/cargo/) - Inspiration for design
- [SemVer Specification](https://semver.org/) - Version format

---

**Last Updated**: 2026-02-07
**Authors**: Jonathan D.A. Jewell
**License**: PMPL-1.0-or-later
