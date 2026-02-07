// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Ephapax Package Manager
//!
//! Provides Cargo-style dependency management for Ephapax projects.
//!
//! ## Features
//!
//! - **Manifest parsing**: Read and validate `ephapax.toml`
//! - **Dependency resolution**: Resolve version constraints with backtracking
//! - **Local registry**: Manage installed packages in `~/.ephapax/registry`
//! - **Package installation**: Download and cache packages
//!
//! ## Usage
//!
//! ```no_run
//! use ephapax_package::{Manifest, Registry, Resolver};
//!
//! // Load project manifest
//! let manifest = Manifest::from_file("ephapax.toml".as_ref()).unwrap();
//!
//! // Open local registry
//! let registry = Registry::open().unwrap();
//!
//! // Resolve dependencies
//! let resolver = Resolver::new(&registry);
//! let resolved = resolver.resolve(&manifest).unwrap();
//!
//! // Print dependency tree
//! resolved.print();
//! ```

pub mod manifest;
pub mod registry;
pub mod resolver;

pub use manifest::{Dependency, Manifest, ManifestError, PackageMetadata};
pub use registry::{Registry, RegistryError, RegistryIndex};
pub use resolver::{ResolvedGraph, ResolvedPackage, Resolver, ResolverError};

use std::path::Path;
use thiserror::Error;

/// Package manager errors
#[derive(Debug, Error)]
pub enum PackageError {
    #[error("Manifest error: {0}")]
    Manifest(#[from] ManifestError),

    #[error("Registry error: {0}")]
    Registry(#[from] RegistryError),

    #[error("Resolver error: {0}")]
    Resolver(#[from] ResolverError),

    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

/// Initialize a new Ephapax project with default manifest
pub fn init_project(path: &Path, name: &str) -> Result<(), PackageError> {
    let manifest_path = path.join("ephapax.toml");

    if manifest_path.exists() {
        return Err(PackageError::Io(std::io::Error::new(
            std::io::ErrorKind::AlreadyExists,
            "ephapax.toml already exists",
        )));
    }

    let manifest = Manifest::default_template(name);
    manifest.to_file(&manifest_path)?;

    // Create src directory
    let src_dir = path.join("src");
    std::fs::create_dir_all(&src_dir)?;

    // Create main.eph
    let main_eph = src_dir.join("main.eph");
    std::fs::write(
        main_eph,
        r#"// SPDX-License-Identifier: PMPL-1.0-or-later

fn main(): I32 =
    42
"#,
    )?;

    Ok(())
}

/// Install dependencies for a project
pub fn install_dependencies(manifest_path: &Path) -> Result<ResolvedGraph, PackageError> {
    let manifest = Manifest::from_file(manifest_path)?;
    let registry = Registry::open()?;
    let resolver = Resolver::new(&registry);
    let resolved = resolver.resolve(&manifest)?;
    Ok(resolved)
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_init_project() {
        let temp = TempDir::new().unwrap();
        init_project(temp.path(), "test-project").unwrap();

        assert!(temp.path().join("ephapax.toml").exists());
        assert!(temp.path().join("src").exists());
        assert!(temp.path().join("src/main.eph").exists());

        let manifest = Manifest::from_file(&temp.path().join("ephapax.toml")).unwrap();
        assert_eq!(manifest.package.name, "test-project");
    }

    #[test]
    fn test_init_project_already_exists() {
        let temp = TempDir::new().unwrap();
        std::fs::write(temp.path().join("ephapax.toml"), "").unwrap();

        let result = init_project(temp.path(), "test");
        assert!(result.is_err());
    }
}
