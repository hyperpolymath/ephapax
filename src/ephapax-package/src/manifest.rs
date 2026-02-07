// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Manifest file (ephapax.toml) parsing and validation

use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use thiserror::Error;

/// Errors that can occur during manifest operations
#[derive(Debug, Error)]
pub enum ManifestError {
    #[error("Failed to read manifest file: {0}")]
    ReadError(#[from] std::io::Error),

    #[error("Failed to parse manifest: {0}")]
    ParseError(#[from] toml::de::Error),

    #[error("Invalid package name: {0}")]
    InvalidPackageName(String),

    #[error("Invalid version: {0}")]
    InvalidVersion(String),

    #[error("Missing required field: {0}")]
    MissingField(String),
}

/// Package manifest (ephapax.toml)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Manifest {
    pub package: PackageMetadata,
    #[serde(default)]
    pub dependencies: HashMap<String, Dependency>,
    #[serde(default)]
    pub dev_dependencies: HashMap<String, Dependency>,
}

/// Package metadata section
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageMetadata {
    pub name: String,
    pub version: String,
    pub authors: Vec<String>,
    pub license: String,
    #[serde(default)]
    pub description: String,
    #[serde(default)]
    pub repository: Option<String>,
    #[serde(default)]
    pub keywords: Vec<String>,
}

/// Dependency specification
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged)]
pub enum Dependency {
    /// Simple version string: "1.0"
    Simple(String),
    /// Detailed specification
    Detailed {
        #[serde(default)]
        version: Option<String>,
        #[serde(default)]
        git: Option<String>,
        #[serde(default)]
        branch: Option<String>,
        #[serde(default)]
        tag: Option<String>,
        #[serde(default)]
        rev: Option<String>,
        #[serde(default)]
        path: Option<PathBuf>,
        /// Compilation mode required for this dependency
        #[serde(default)]
        mode: Option<String>,
        #[serde(default)]
        optional: bool,
    },
}

impl Dependency {
    /// Get the version requirement string
    pub fn version(&self) -> &str {
        match self {
            Dependency::Simple(v) => v,
            Dependency::Detailed { version, .. } => {
                version.as_deref().unwrap_or("*")
            }
        }
    }

    /// Check if this is a git dependency
    pub fn is_git(&self) -> bool {
        matches!(self, Dependency::Detailed { git: Some(_), .. })
    }

    /// Check if this is a path dependency
    pub fn is_path(&self) -> bool {
        matches!(self, Dependency::Detailed { path: Some(_), .. })
    }

    /// Get the git URL if this is a git dependency
    pub fn git_url(&self) -> Option<&str> {
        match self {
            Dependency::Detailed { git: Some(url), .. } => Some(url),
            _ => None,
        }
    }

    /// Get the path if this is a path dependency
    pub fn path(&self) -> Option<&Path> {
        match self {
            Dependency::Detailed { path: Some(p), .. } => Some(p),
            _ => None,
        }
    }

    /// Get the required compilation mode
    pub fn mode(&self) -> Option<&str> {
        match self {
            Dependency::Detailed { mode: Some(m), .. } => Some(m),
            _ => None,
        }
    }
}

impl Manifest {
    /// Load manifest from file
    pub fn from_file(path: &Path) -> Result<Self, ManifestError> {
        let content = std::fs::read_to_string(path)?;
        Self::from_str(&content)
    }

    /// Parse manifest from string
    pub fn from_str(content: &str) -> Result<Self, ManifestError> {
        let manifest: Manifest = toml::from_str(content)?;
        manifest.validate()?;
        Ok(manifest)
    }

    /// Validate manifest
    pub fn validate(&self) -> Result<(), ManifestError> {
        // Validate package name
        if !is_valid_package_name(&self.package.name) {
            return Err(ManifestError::InvalidPackageName(
                self.package.name.clone(),
            ));
        }

        // Validate version
        if semver::Version::parse(&self.package.version).is_err() {
            return Err(ManifestError::InvalidVersion(
                self.package.version.clone(),
            ));
        }

        // Validate authors
        if self.package.authors.is_empty() {
            return Err(ManifestError::MissingField("authors".to_string()));
        }

        // Validate license
        if self.package.license.is_empty() {
            return Err(ManifestError::MissingField("license".to_string()));
        }

        Ok(())
    }

    /// Write manifest to file
    pub fn to_file(&self, path: &Path) -> Result<(), ManifestError> {
        let content = toml::to_string_pretty(self)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::Other, e))?;
        std::fs::write(path, content)?;
        Ok(())
    }

    /// Create a default manifest template
    pub fn default_template(name: &str) -> Self {
        Manifest {
            package: PackageMetadata {
                name: name.to_string(),
                version: "0.1.0".to_string(),
                authors: vec!["Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>".to_string()],
                license: "PMPL-1.0-or-later".to_string(),
                description: String::new(),
                repository: None,
                keywords: Vec::new(),
            },
            dependencies: HashMap::new(),
            dev_dependencies: HashMap::new(),
        }
    }
}

/// Validate package name
fn is_valid_package_name(name: &str) -> bool {
    if name.is_empty() || name.len() > 64 {
        return false;
    }

    // Must start with letter
    if !name.chars().next().unwrap().is_ascii_lowercase() {
        return false;
    }

    // Only lowercase letters, numbers, hyphens
    name.chars()
        .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '-')
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_manifest() {
        let toml = r#"
[package]
name = "my-lib"
version = "0.1.0"
authors = ["Jonathan D.A. Jewell <jonathan.jewell@open.ac.uk>"]
license = "PMPL-1.0-or-later"

[dependencies]
linear-collections = "1.0"
"#;

        let manifest = Manifest::from_str(toml).unwrap();
        assert_eq!(manifest.package.name, "my-lib");
        assert_eq!(manifest.package.version, "0.1.0");
        assert_eq!(manifest.dependencies.len(), 1);
    }

    #[test]
    fn test_parse_detailed_dependency() {
        let toml = r#"
[package]
name = "test"
version = "1.0.0"
authors = ["Test"]
license = "PMPL-1.0-or-later"

[dependencies]
affine-utils = { version = "0.5", mode = "affine" }
local-lib = { path = "../local" }
git-lib = { git = "https://github.com/example/lib", tag = "v1.0" }
"#;

        let manifest = Manifest::from_str(toml).unwrap();
        assert_eq!(manifest.dependencies.len(), 3);

        let affine = &manifest.dependencies["affine-utils"];
        assert_eq!(affine.version(), "0.5");
        assert_eq!(affine.mode(), Some("affine"));

        let local = &manifest.dependencies["local-lib"];
        assert!(local.is_path());

        let git = &manifest.dependencies["git-lib"];
        assert!(git.is_git());
    }

    #[test]
    fn test_invalid_package_name() {
        let toml = r#"
[package]
name = "Invalid-Name"
version = "1.0.0"
authors = ["Test"]
license = "PMPL-1.0-or-later"
"#;

        assert!(Manifest::from_str(toml).is_err());
    }

    #[test]
    fn test_invalid_version() {
        let toml = r#"
[package]
name = "test"
version = "not-a-version"
authors = ["Test"]
license = "PMPL-1.0-or-later"
"#;

        assert!(Manifest::from_str(toml).is_err());
    }

    #[test]
    fn test_default_template() {
        let manifest = Manifest::default_template("my-project");
        assert_eq!(manifest.package.name, "my-project");
        assert_eq!(manifest.package.version, "0.1.0");
        assert!(manifest.validate().is_ok());
    }

    #[test]
    fn test_valid_package_names() {
        assert!(is_valid_package_name("my-lib"));
        assert!(is_valid_package_name("lib123"));
        assert!(is_valid_package_name("a"));

        assert!(!is_valid_package_name(""));
        assert!(!is_valid_package_name("MyLib"));
        assert!(!is_valid_package_name("my_lib"));
        assert!(!is_valid_package_name("123lib"));
    }
}
