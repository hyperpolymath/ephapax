// SPDX-License-Identifier: PMPL-1.0-or-later
// SPDX-FileCopyrightText: 2025 Jonathan D.A. Jewell

//! Dependency resolution

use crate::manifest::{Dependency, Manifest};
use crate::registry::Registry;
use indexmap::IndexMap;
use semver::{Version, VersionReq};
use std::collections::{HashMap, HashSet};
use thiserror::Error;

/// Dependency resolution errors
#[derive(Debug, Error)]
pub enum ResolverError {
    #[error("Package not found: {0}")]
    PackageNotFound(String),

    #[error("No version of {package} satisfies requirement {requirement}")]
    NoMatchingVersion {
        package: String,
        requirement: String,
    },

    #[error("Dependency conflict: {0}")]
    Conflict(String),

    #[error("Circular dependency detected: {0}")]
    CircularDependency(String),

    #[error("Registry error: {0}")]
    Registry(String),
}

/// Resolved dependency graph
#[derive(Debug, Clone)]
pub struct ResolvedGraph {
    /// Package name -> resolved version
    pub packages: IndexMap<String, ResolvedPackage>,
}

/// A resolved package with its dependencies
#[derive(Debug, Clone)]
pub struct ResolvedPackage {
    pub name: String,
    pub version: Version,
    pub dependencies: HashMap<String, Version>,
}

/// Dependency resolver using backtracking algorithm
pub struct Resolver<'a> {
    registry: &'a Registry,
    /// Maximum resolution depth to prevent infinite loops
    max_depth: usize,
}

impl<'a> Resolver<'a> {
    /// Create a new resolver
    pub fn new(registry: &'a Registry) -> Self {
        Resolver {
            registry,
            max_depth: 100,
        }
    }

    /// Resolve dependencies for a manifest
    pub fn resolve(&self, manifest: &Manifest) -> Result<ResolvedGraph, ResolverError> {
        let mut resolved = IndexMap::new();
        let mut in_progress = HashSet::new();

        // Resolve each direct dependency
        for (name, dep) in &manifest.dependencies {
            self.resolve_dependency(
                name,
                dep,
                &mut resolved,
                &mut in_progress,
                0,
            )?;
        }

        Ok(ResolvedGraph { packages: resolved })
    }

    /// Resolve a single dependency recursively
    fn resolve_dependency(
        &self,
        name: &str,
        dep: &Dependency,
        resolved: &mut IndexMap<String, ResolvedPackage>,
        in_progress: &mut HashSet<String>,
        depth: usize,
    ) -> Result<(), ResolverError> {
        // Check depth limit
        if depth >= self.max_depth {
            return Err(ResolverError::CircularDependency(format!(
                "Maximum depth {} exceeded",
                self.max_depth
            )));
        }

        // Check for circular dependencies
        if in_progress.contains(name) {
            return Err(ResolverError::CircularDependency(name.to_string()));
        }

        // Already resolved?
        if resolved.contains_key(name) {
            return Ok(());
        }

        // Mark as in progress
        in_progress.insert(name.to_string());

        // Get version requirement
        let req = VersionReq::parse(dep.version())
            .map_err(|_| ResolverError::NoMatchingVersion {
                package: name.to_string(),
                requirement: dep.version().to_string(),
            })?;

        // Find matching version
        let version = self.find_matching_version(name, &req)?;

        // Load manifest for this version
        let manifest = self
            .registry
            .load_manifest(name, &version.to_string())
            .map_err(|e| ResolverError::Registry(e.to_string()))?;

        // Resolve transitive dependencies
        let mut dependencies = HashMap::new();
        for (dep_name, dep_spec) in &manifest.dependencies {
            self.resolve_dependency(
                dep_name,
                dep_spec,
                resolved,
                in_progress,
                depth + 1,
            )?;

            // Record the resolved version
            if let Some(resolved_dep) = resolved.get(dep_name) {
                dependencies.insert(dep_name.clone(), resolved_dep.version.clone());
            }
        }

        // Add to resolved set
        resolved.insert(
            name.to_string(),
            ResolvedPackage {
                name: name.to_string(),
                version,
                dependencies,
            },
        );

        // Remove from in-progress
        in_progress.remove(name);

        Ok(())
    }

    /// Find the latest version matching a requirement
    fn find_matching_version(
        &self,
        name: &str,
        req: &VersionReq,
    ) -> Result<Version, ResolverError> {
        let versions = self.registry.get_versions(name);

        if versions.is_empty() {
            return Err(ResolverError::PackageNotFound(name.to_string()));
        }

        // Parse and filter versions
        let mut matching: Vec<Version> = versions
            .iter()
            .filter_map(|v| Version::parse(v).ok())
            .filter(|v| req.matches(v))
            .collect();

        if matching.is_empty() {
            return Err(ResolverError::NoMatchingVersion {
                package: name.to_string(),
                requirement: req.to_string(),
            });
        }

        // Sort descending and take the latest
        matching.sort_by(|a, b| b.cmp(a));
        Ok(matching[0].clone())
    }
}

impl ResolvedGraph {
    /// Get packages in topological order (dependencies first)
    pub fn topological_order(&self) -> Vec<String> {
        let mut order = Vec::new();
        let mut visited = HashSet::new();
        let mut temp = HashSet::new();

        for name in self.packages.keys() {
            self.visit(name, &mut visited, &mut temp, &mut order);
        }

        order
    }

    /// DFS visit for topological sort
    fn visit(
        &self,
        name: &str,
        visited: &mut HashSet<String>,
        temp: &mut HashSet<String>,
        order: &mut Vec<String>,
    ) {
        if visited.contains(name) {
            return;
        }

        if temp.contains(name) {
            // Circular dependency (should have been caught earlier)
            return;
        }

        temp.insert(name.to_string());

        if let Some(pkg) = self.packages.get(name) {
            for dep_name in pkg.dependencies.keys() {
                self.visit(dep_name, visited, temp, order);
            }
        }

        temp.remove(name);
        visited.insert(name.to_string());
        order.push(name.to_string());
    }

    /// Print the dependency graph
    pub fn print(&self) {
        println!("Resolved dependencies:");
        for (name, pkg) in &self.packages {
            println!("  {} v{}", name, pkg.version);
            for (dep_name, dep_version) in &pkg.dependencies {
                println!("    └─ {} v{}", dep_name, dep_version);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::manifest::{Manifest, PackageMetadata};
    use crate::registry::Registry;
    use tempfile::TempDir;

    fn create_test_package(name: &str, version: &str, deps: Vec<(&str, &str)>) -> Manifest {
        let dependencies: HashMap<String, Dependency> = deps
            .into_iter()
            .map(|(n, v)| (n.to_string(), Dependency::Simple(v.to_string())))
            .collect();

        Manifest {
            package: PackageMetadata {
                name: name.to_string(),
                version: version.to_string(),
                authors: vec!["Test".to_string()],
                license: "PMPL-1.0-or-later".to_string(),
                description: String::new(),
                repository: None,
                keywords: Vec::new(),
            },
            dependencies,
            dev_dependencies: HashMap::new(),
        }
    }

    #[test]
    fn test_simple_resolution() {
        let temp = TempDir::new().unwrap();
        let mut registry = Registry::open_at(temp.path().to_path_buf()).unwrap();

        // Create package structure
        let pkg_dir = temp.path().join("pkg");
        std::fs::create_dir_all(&pkg_dir).unwrap();

        let dep_manifest = create_test_package("dep", "1.0.0", vec![]);
        dep_manifest
            .to_file(&pkg_dir.join("ephapax.toml"))
            .unwrap();
        registry.install_package("dep", "1.0.0", &pkg_dir).unwrap();

        // Main package depends on dep
        let main_manifest = create_test_package("main", "1.0.0", vec![("dep", "^1.0")]);

        let resolver = Resolver::new(&registry);
        let resolved = resolver.resolve(&main_manifest).unwrap();

        assert_eq!(resolved.packages.len(), 1);
        assert!(resolved.packages.contains_key("dep"));
    }

    #[test]
    fn test_transitive_resolution() {
        let temp = TempDir::new().unwrap();
        let mut registry = Registry::open_at(temp.path().to_path_buf()).unwrap();

        let pkg_dir = temp.path().join("pkg");
        std::fs::create_dir_all(&pkg_dir).unwrap();

        // leaf: no dependencies
        let leaf = create_test_package("leaf", "1.0.0", vec![]);
        leaf.to_file(&pkg_dir.join("ephapax.toml")).unwrap();
        registry.install_package("leaf", "1.0.0", &pkg_dir).unwrap();

        // middle: depends on leaf
        let middle = create_test_package("middle", "1.0.0", vec![("leaf", "^1.0")]);
        middle.to_file(&pkg_dir.join("ephapax.toml")).unwrap();
        registry
            .install_package("middle", "1.0.0", &pkg_dir)
            .unwrap();

        // main: depends on middle
        let main = create_test_package("main", "1.0.0", vec![("middle", "^1.0")]);

        let resolver = Resolver::new(&registry);
        let resolved = resolver.resolve(&main).unwrap();

        assert_eq!(resolved.packages.len(), 2);
        assert!(resolved.packages.contains_key("middle"));
        assert!(resolved.packages.contains_key("leaf"));

        // Check topological order (leaf before middle)
        let order = resolved.topological_order();
        let leaf_pos = order.iter().position(|n| n == "leaf").unwrap();
        let middle_pos = order.iter().position(|n| n == "middle").unwrap();
        assert!(leaf_pos < middle_pos);
    }

    #[test]
    fn test_version_selection() {
        let temp = TempDir::new().unwrap();
        let mut registry = Registry::open_at(temp.path().to_path_buf()).unwrap();

        let pkg_dir = temp.path().join("pkg");
        std::fs::create_dir_all(&pkg_dir).unwrap();

        // Install multiple versions
        for version in &["1.0.0", "1.1.0", "1.2.0", "2.0.0"] {
            let pkg = create_test_package("lib", version, vec![]);
            pkg.to_file(&pkg_dir.join("ephapax.toml")).unwrap();
            registry.install_package("lib", version, &pkg_dir).unwrap();
        }

        let main = create_test_package("main", "1.0.0", vec![("lib", "^1.0")]);

        let resolver = Resolver::new(&registry);
        let resolved = resolver.resolve(&main).unwrap();

        // Should pick 1.2.0 (latest matching ^1.0)
        let lib = &resolved.packages["lib"];
        assert_eq!(lib.version.to_string(), "1.2.0");
    }
}
