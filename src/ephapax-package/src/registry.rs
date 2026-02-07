// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Local package registry management

use crate::manifest::Manifest;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use thiserror::Error;

/// Registry errors
#[derive(Debug, Error)]
pub enum RegistryError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),

    #[error("Package not found: {0}")]
    PackageNotFound(String),

    #[error("Version not found: {0}@{1}")]
    VersionNotFound(String, String),

    #[error("Invalid registry structure")]
    InvalidStructure,

    #[error("Failed to parse registry index: {0}")]
    ParseError(#[from] serde_json::Error),
}

/// Local package registry
///
/// Structure:
/// ```text
/// ~/.ephapax/
/// ├── registry/
/// │   ├── index.json           # Package index
/// │   └── packages/
/// │       ├── linear-collections/
/// │       │   ├── 1.0.0/
/// │       │   │   ├── ephapax.toml
/// │       │   │   └── src/
/// │       │   └── 1.1.0/
/// │       └── affine-utils/
/// └── cache/                   # Downloaded packages
/// ```
pub struct Registry {
    root: PathBuf,
    index: RegistryIndex,
}

/// Registry index (index.json)
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct RegistryIndex {
    /// Map of package name to available versions
    pub packages: HashMap<String, PackageInfo>,
}

/// Information about a package in the registry
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct PackageInfo {
    pub name: String,
    pub versions: Vec<VersionInfo>,
}

/// Information about a specific version
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VersionInfo {
    pub version: String,
    pub checksum: String,
    #[serde(default)]
    pub yanked: bool,
}

impl Registry {
    /// Get the default registry path (~/.ephapax/registry)
    pub fn default_path() -> Result<PathBuf, RegistryError> {
        let home = home::home_dir().ok_or(RegistryError::InvalidStructure)?;
        Ok(home.join(".ephapax").join("registry"))
    }

    /// Open or create the registry
    pub fn open() -> Result<Self, RegistryError> {
        let root = Self::default_path()?;
        Self::open_at(root)
    }

    /// Open registry at a specific path
    pub fn open_at(root: PathBuf) -> Result<Self, RegistryError> {
        // Create directory structure if needed
        std::fs::create_dir_all(&root)?;
        std::fs::create_dir_all(root.join("packages"))?;
        std::fs::create_dir_all(root.join("cache"))?;

        // Load or create index
        let index_path = root.join("index.json");
        let index = if index_path.exists() {
            let content = std::fs::read_to_string(&index_path)?;
            serde_json::from_str(&content)?
        } else {
            RegistryIndex::default()
        };

        Ok(Registry { root, index })
    }

    /// Save the registry index
    pub fn save_index(&self) -> Result<(), RegistryError> {
        let index_path = self.root.join("index.json");
        let content = serde_json::to_string_pretty(&self.index)?;
        std::fs::write(index_path, content)?;
        Ok(())
    }

    /// Get package directory
    pub fn package_dir(&self, name: &str, version: &str) -> PathBuf {
        self.root
            .join("packages")
            .join(name)
            .join(version)
    }

    /// Check if a package version exists in the registry
    pub fn has_package(&self, name: &str, version: &str) -> bool {
        self.index
            .packages
            .get(name)
            .and_then(|info| info.versions.iter().find(|v| v.version == version))
            .is_some()
    }

    /// Get all versions of a package
    pub fn get_versions(&self, name: &str) -> Vec<String> {
        self.index
            .packages
            .get(name)
            .map(|info| info.versions.iter().map(|v| v.version.clone()).collect())
            .unwrap_or_default()
    }

    /// Install a package to the registry
    pub fn install_package(
        &mut self,
        name: &str,
        version: &str,
        source_dir: &Path,
    ) -> Result<(), RegistryError> {
        let pkg_dir = self.package_dir(name, version);

        // Create package directory
        std::fs::create_dir_all(&pkg_dir)?;

        // Copy source files
        copy_dir_recursive(source_dir, &pkg_dir)?;

        // Calculate checksum
        let checksum = calculate_dir_checksum(&pkg_dir)?;

        // Update index
        let package_info = self
            .index
            .packages
            .entry(name.to_string())
            .or_insert_with(|| PackageInfo {
                name: name.to_string(),
                versions: Vec::new(),
            });

        // Add or update version
        if let Some(existing) = package_info
            .versions
            .iter_mut()
            .find(|v| v.version == version)
        {
            existing.checksum = checksum;
        } else {
            package_info.versions.push(VersionInfo {
                version: version.to_string(),
                checksum,
                yanked: false,
            });
        }

        // Sort versions
        package_info
            .versions
            .sort_by(|a, b| {
                semver::Version::parse(&a.version)
                    .ok()
                    .cmp(&semver::Version::parse(&b.version).ok())
            });

        self.save_index()?;
        Ok(())
    }

    /// Load a package manifest from the registry
    pub fn load_manifest(&self, name: &str, version: &str) -> Result<Manifest, RegistryError> {
        let manifest_path = self.package_dir(name, version).join("ephapax.toml");

        if !manifest_path.exists() {
            return Err(RegistryError::VersionNotFound(
                name.to_string(),
                version.to_string(),
            ));
        }

        Manifest::from_file(&manifest_path)
            .map_err(|e| RegistryError::Io(std::io::Error::new(std::io::ErrorKind::Other, e)))
    }

    /// List all packages in the registry
    pub fn list_packages(&self) -> Vec<String> {
        self.index.packages.keys().cloned().collect()
    }

    /// Search for packages by name or keyword
    pub fn search(&self, query: &str) -> Vec<String> {
        let query_lower = query.to_lowercase();
        self.index
            .packages
            .keys()
            .filter(|name| name.to_lowercase().contains(&query_lower))
            .cloned()
            .collect()
    }
}

/// Recursively copy directory
fn copy_dir_recursive(src: &Path, dst: &Path) -> std::io::Result<()> {
    std::fs::create_dir_all(dst)?;

    for entry in std::fs::read_dir(src)? {
        let entry = entry?;
        let path = entry.path();
        let file_name = entry.file_name();
        let dst_path = dst.join(file_name);

        if path.is_dir() {
            // Skip hidden directories and target directories
            if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                if name.starts_with('.') || name == "target" {
                    continue;
                }
            }
            copy_dir_recursive(&path, &dst_path)?;
        } else {
            std::fs::copy(&path, &dst_path)?;
        }
    }

    Ok(())
}

/// Calculate checksum for a directory
fn calculate_dir_checksum(dir: &Path) -> std::io::Result<String> {
    use sha2::{Digest, Sha256};

    let mut hasher = Sha256::new();
    let mut entries: Vec<_> = std::fs::read_dir(dir)?
        .filter_map(|e| e.ok())
        .collect();

    entries.sort_by_key(|e| e.path());

    for entry in entries {
        let path = entry.path();
        if path.is_file() {
            let content = std::fs::read(&path)?;
            hasher.update(&content);
        }
    }

    Ok(format!("{:x}", hasher.finalize()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_registry_creation() {
        let temp = TempDir::new().unwrap();
        let registry = Registry::open_at(temp.path().to_path_buf()).unwrap();

        assert!(temp.path().join("packages").exists());
        assert!(temp.path().join("cache").exists());
        assert!(registry.index.packages.is_empty());
    }

    #[test]
    fn test_package_installation() {
        let temp = TempDir::new().unwrap();
        let mut registry = Registry::open_at(temp.path().to_path_buf()).unwrap();

        let source = TempDir::new().unwrap();
        std::fs::write(source.path().join("test.eph"), "fn main(): I32 = 42").unwrap();

        registry
            .install_package("test-lib", "1.0.0", source.path())
            .unwrap();

        assert!(registry.has_package("test-lib", "1.0.0"));
        let versions = registry.get_versions("test-lib");
        assert_eq!(versions, vec!["1.0.0"]);
    }

    #[test]
    fn test_package_search() {
        let temp = TempDir::new().unwrap();
        let mut registry = Registry::open_at(temp.path().to_path_buf()).unwrap();

        let source = TempDir::new().unwrap();
        registry
            .install_package("linear-collections", "1.0.0", source.path())
            .unwrap();
        registry
            .install_package("affine-utils", "0.5.0", source.path())
            .unwrap();

        let results = registry.search("linear");
        assert_eq!(results, vec!["linear-collections"]);

        let all = registry.list_packages();
        assert_eq!(all.len(), 2);
    }
}
