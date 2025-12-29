//! Extension Discovery and Registration System
//!
//! This module provides utilities for discovering and registering extensions
//! in a clean, composable way. It supports extension versioning, dependency
//! management, and compatibility checking.

use super::{ExtensionRegistry, GrammarExtension, ParseError};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

/// Extension metadata for discovery and versioning
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExtensionMetadata {
    pub name: String,
    pub version: String,
    pub description: String,
    pub author: String,
    pub dependencies: Vec<String>,
    pub required_rumpsteak_version: Option<String>,
    pub priority: Option<u32>,
    /// Documentation fields
    pub overview: Option<String>,
    pub syntax_guide: Option<String>,
    pub use_cases: Option<Vec<String>>,
    pub keywords: Option<Vec<String>>,
}

/// Extension package containing metadata and implementation
#[derive(Debug)]
pub struct ExtensionPackage {
    pub metadata: ExtensionMetadata,
    pub extension: Box<dyn GrammarExtension>,
    pub source_path: Option<PathBuf>,
}

/// Registry for extension discovery and management
#[derive(Debug, Default)]
pub struct ExtensionDiscovery {
    discovered_extensions: HashMap<String, ExtensionPackage>,
    search_paths: Vec<PathBuf>,
}

impl ExtensionDiscovery {
    /// Create a new extension discovery manager
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a search path for extensions
    pub fn add_search_path<P: AsRef<Path>>(&mut self, path: P) {
        self.search_paths.push(path.as_ref().to_path_buf());
    }

    /// Manually register an extension with metadata
    pub fn register_extension(
        &mut self,
        metadata: ExtensionMetadata,
        extension: Box<dyn GrammarExtension>,
    ) -> Result<(), ParseError> {
        // Validate metadata
        if metadata.name.is_empty() {
            return Err(ParseError::InvalidSyntax {
                details: "Extension name cannot be empty".to_string(),
            });
        }

        // Check for conflicts
        if self.discovered_extensions.contains_key(&metadata.name) {
            return Err(ParseError::RegistrationFailed {
                extension: metadata.name.clone(),
                rule: "discovery".to_string(),
                details: format!(
                    "Extension '{}' is already registered in discovery system",
                    metadata.name
                ),
            });
        }

        let package = ExtensionPackage {
            metadata,
            extension,
            source_path: None,
        };

        self.discovered_extensions
            .insert(package.metadata.name.clone(), package);
        Ok(())
    }

    /// Get all discovered extensions
    pub fn get_extensions(&self) -> &HashMap<String, ExtensionPackage> {
        &self.discovered_extensions
    }

    /// Check if an extension is available
    pub fn has_extension(&self, name: &str) -> bool {
        self.discovered_extensions.contains_key(name)
    }

    /// Get extension metadata by name
    pub fn get_metadata(&self, name: &str) -> Option<&ExtensionMetadata> {
        self.discovered_extensions
            .get(name)
            .map(|pkg| &pkg.metadata)
    }

    /// Resolve extension dependencies
    pub fn resolve_dependencies(
        &self,
        extension_names: &[String],
    ) -> Result<Vec<String>, ParseError> {
        let mut resolved = Vec::new();
        let mut to_process = extension_names.to_vec();
        let mut processed = std::collections::HashSet::new();

        while let Some(ext_name) = to_process.pop() {
            if processed.contains(&ext_name) {
                continue;
            }

            if let Some(package) = self.discovered_extensions.get(&ext_name) {
                // Add dependencies first
                for dep in &package.metadata.dependencies {
                    if !processed.contains(dep) && !to_process.contains(dep) {
                        to_process.push(dep.clone());
                    }
                }

                resolved.push(ext_name.clone());
                processed.insert(ext_name);
            } else {
                return Err(ParseError::MissingDependency {
                    extension: "dependency_resolution".to_string(),
                    dependency: ext_name.clone(),
                });
            }
        }

        Ok(resolved)
    }

    /// Create a configured extension registry
    pub fn create_registry(
        &self,
        extension_names: &[String],
    ) -> Result<ExtensionRegistry, ParseError> {
        let resolved = self.resolve_dependencies(extension_names)?;
        let mut registry = ExtensionRegistry::new();

        // Register extensions in dependency order
        for ext_name in resolved {
            if let Some(package) = self.discovered_extensions.get(&ext_name) {
                // Clone the extension (this requires extensions to be cloneable or
                // we need a different approach for ownership)
                registry.register_grammar_legacy(ClonableExtensionWrapper::new(
                    &*package.extension,
                    &package.metadata,
                ));

                // Add dependencies to registry
                for dep in &package.metadata.dependencies {
                    registry.add_dependency(&ext_name, dep);
                }
            }
        }

        // Validate all dependencies are satisfied
        registry.validate_dependencies()?;

        Ok(registry)
    }

    /// Validate extension compatibility
    pub fn check_compatibility(&self, extension_names: &[String]) -> Result<(), ParseError> {
        let resolved = self.resolve_dependencies(extension_names)?;

        // Check version compatibility
        for ext_name in &resolved {
            if let Some(package) = self.discovered_extensions.get(ext_name) {
                if let Some(required_version) = &package.metadata.required_rumpsteak_version {
                    // In a real implementation, we'd check against actual version
                    if required_version != "0.5.0" {
                        return Err(ParseError::IncompatibleExtensions {
                            details: format!(
                                "Extension '{}' requires rumpsteak-aura version '{}', but current version is '0.5.0'. Please update the extension or rumpsteak-aura to compatible versions.",
                                ext_name, required_version
                            ),
                        });
                    }
                }
            }
        }

        Ok(())
    }

    /// Load extension from a directory or file
    pub fn load_from_path<P: AsRef<Path>>(&mut self, path: P) -> Result<(), ParseError> {
        let path = path.as_ref();

        // Look for extension metadata file
        let metadata_path = path.join("extension.toml");
        if metadata_path.exists() {
            let metadata_str =
                std::fs::read_to_string(&metadata_path).map_err(|e| ParseError::InvalidSyntax {
                    details: format!("Failed to read extension metadata: {}", e),
                })?;

            let metadata: ExtensionMetadata =
                toml::from_str(&metadata_str).map_err(|e| ParseError::InvalidSyntax {
                    details: format!("Invalid extension metadata: {}", e),
                })?;

            // For now, we'll create a placeholder extension since we can't load dynamic libraries
            let extension = Box::new(PlaceholderExtension::new(&metadata));

            let package = ExtensionPackage {
                metadata: metadata.clone(),
                extension,
                source_path: Some(path.to_path_buf()),
            };

            self.discovered_extensions.insert(metadata.name, package);
        }

        Ok(())
    }

    /// Create a registry with commonly used extensions
    pub fn with_common_extensions() -> Result<ExtensionRegistry, ParseError> {
        let mut discovery = Self::new();

        // Register built-in extensions
        discovery.register_extension(
            ExtensionMetadata {
                name: "timeout".to_string(),
                version: "0.5.0".to_string(),
                description: "Timeout support for choreographic protocols".to_string(),
                author: "Rumpsteak Aura Team".to_string(),
                dependencies: vec![],
                required_rumpsteak_version: Some("0.5.0".to_string()),
                priority: Some(100),
                overview: Some("Adds timeout semantics to choreographic protocols".to_string()),
                syntax_guide: Some("Use `timeout(duration) { ... }` syntax".to_string()),
                use_cases: Some(vec![
                    "Network protocols".to_string(),
                    "Real-time systems".to_string(),
                ]),
                keywords: Some(vec!["timeout".to_string(), "timing".to_string()]),
            },
            Box::new(super::timeout::TimeoutGrammarExtension),
        )?;

        discovery.register_extension(
            ExtensionMetadata {
                name: "aura_annotations".to_string(),
                version: "0.1.0".to_string(),
                description: "Aura-style annotations for capability tracking".to_string(),
                author: "Aura Project".to_string(),
                dependencies: vec![],
                required_rumpsteak_version: Some("0.5.0".to_string()),
                priority: Some(110),
                overview: Some(
                    "Adds Aura-specific annotations for capabilities and flow control".to_string(),
                ),
                syntax_guide: Some(
                    "Use Role[annotation=value] syntax in communications".to_string(),
                ),
                use_cases: Some(vec![
                    "Capability verification".to_string(),
                    "Flow control".to_string(),
                ]),
                keywords: Some(vec![
                    "aura".to_string(),
                    "capabilities".to_string(),
                    "annotations".to_string(),
                ]),
            },
            Box::new(AuraAnnotationExtension),
        )?;

        discovery.create_registry(&["timeout".to_string(), "aura_annotations".to_string()])
    }

    /// Helper to create a minimal registry for 3rd party integration
    pub fn for_third_party() -> Self {
        Self::new()
    }

    /// Helper to register built-in rumpsteak extensions
    pub fn with_builtin_only() -> Result<ExtensionRegistry, ParseError> {
        let mut discovery = Self::new();

        discovery.register_extension(
            ExtensionMetadata {
                name: "timeout".to_string(),
                version: "0.5.0".to_string(),
                description: "Timeout support for choreographic protocols".to_string(),
                author: "Rumpsteak Aura Team".to_string(),
                dependencies: vec![],
                required_rumpsteak_version: Some("0.5.0".to_string()),
                priority: Some(100),
                overview: Some("Adds timeout semantics to choreographic protocols".to_string()),
                syntax_guide: Some("Use `timeout(duration) { ... }` syntax".to_string()),
                use_cases: Some(vec![
                    "Network protocols".to_string(),
                    "Real-time systems".to_string(),
                ]),
                keywords: Some(vec!["timeout".to_string(), "timing".to_string()]),
            },
            Box::new(super::timeout::TimeoutGrammarExtension),
        )?;

        discovery.create_registry(&["timeout".to_string()])
    }

    /// Helper to validate extension metadata before registration
    pub fn validate_metadata(metadata: &ExtensionMetadata) -> Result<(), ParseError> {
        if metadata.name.is_empty() {
            return Err(ParseError::InvalidSyntax {
                details: "Extension name cannot be empty".to_string(),
            });
        }

        if metadata.version.is_empty() {
            return Err(ParseError::InvalidSyntax {
                details: "Extension version cannot be empty".to_string(),
            });
        }

        if metadata.name.contains(' ') {
            return Err(ParseError::InvalidSyntax {
                details: "Extension name cannot contain spaces".to_string(),
            });
        }

        Ok(())
    }

    /// List all available extensions with their metadata
    pub fn list_extensions(&self) -> Vec<&ExtensionMetadata> {
        self.discovered_extensions
            .values()
            .map(|pkg| &pkg.metadata)
            .collect()
    }

    /// Find extensions by author
    pub fn find_by_author(&self, author: &str) -> Vec<&ExtensionMetadata> {
        self.discovered_extensions
            .values()
            .filter_map(|pkg| {
                if pkg.metadata.author == author {
                    Some(&pkg.metadata)
                } else {
                    None
                }
            })
            .collect()
    }
}

/// Wrapper to make extensions cloneable for registry management
#[derive(Debug, Clone)]
struct ClonableExtensionWrapper {
    #[allow(dead_code)]
    id: String,
    #[allow(dead_code)]
    rules: Vec<String>,
    #[allow(dead_code)]
    grammar: String,
    priority: u32,
}

impl ClonableExtensionWrapper {
    fn new(extension: &dyn GrammarExtension, metadata: &ExtensionMetadata) -> Self {
        Self {
            id: metadata.name.clone(),
            rules: extension
                .statement_rules()
                .iter()
                .map(|s| s.to_string())
                .collect(),
            grammar: extension.grammar_rules().to_string(),
            priority: metadata.priority.unwrap_or(extension.priority()),
        }
    }
}

impl GrammarExtension for ClonableExtensionWrapper {
    fn grammar_rules(&self) -> &'static str {
        // This is a limitation - we need to box the string or use a different approach
        // For now, return empty string
        ""
    }

    fn statement_rules(&self) -> Vec<&'static str> {
        // Another limitation - return empty for now
        vec![]
    }

    fn priority(&self) -> u32 {
        self.priority
    }

    fn extension_id(&self) -> &'static str {
        // This needs a different approach for dynamic extensions
        "cloneable_wrapper"
    }
}

/// Placeholder extension for loaded extensions
#[derive(Debug, Clone)]
struct PlaceholderExtension {
    #[allow(dead_code)]
    name: String,
    priority: u32,
}

impl PlaceholderExtension {
    fn new(metadata: &ExtensionMetadata) -> Self {
        Self {
            name: metadata.name.clone(),
            priority: metadata.priority.unwrap_or(100),
        }
    }
}

impl GrammarExtension for PlaceholderExtension {
    fn grammar_rules(&self) -> &'static str {
        ""
    }

    fn statement_rules(&self) -> Vec<&'static str> {
        vec![]
    }

    fn priority(&self) -> u32 {
        self.priority
    }

    fn extension_id(&self) -> &'static str {
        "placeholder"
    }
}

/// Aura annotation extension implementation
#[derive(Debug, Clone)]
struct AuraAnnotationExtension;

impl GrammarExtension for AuraAnnotationExtension {
    fn grammar_rules(&self) -> &'static str {
        r#"
aura_annotation_stmt = { role_ref ~ "[" ~ aura_annotation_list ~ "]" ~ "->" ~ role_ref ~ ":" ~ message ~ ";" }
aura_annotation_list = { aura_annotation_item ~ ("," ~ aura_annotation_item)* }
aura_annotation_item = { ident ~ "=" ~ annotation_value }
"#
    }

    fn statement_rules(&self) -> Vec<&'static str> {
        vec!["aura_annotation_stmt"]
    }

    fn priority(&self) -> u32 {
        110
    }

    fn extension_id(&self) -> &'static str {
        "aura_annotations"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extension_discovery() {
        let mut discovery = ExtensionDiscovery::new();

        let metadata = ExtensionMetadata {
            name: "test_ext".to_string(),
            version: "1.0.0".to_string(),
            description: "Test extension".to_string(),
            author: "Test Author".to_string(),
            dependencies: vec![],
            required_rumpsteak_version: Some("0.5.0".to_string()),
            priority: Some(100),
            overview: None,
            syntax_guide: None,
            use_cases: None,
            keywords: None,
        };

        let extension = Box::new(PlaceholderExtension::new(&metadata));
        assert!(discovery.register_extension(metadata, extension).is_ok());
        assert!(discovery.has_extension("test_ext"));
    }

    #[test]
    fn test_dependency_resolution() {
        let mut discovery = ExtensionDiscovery::new();

        // Add base extension
        let base_metadata = ExtensionMetadata {
            name: "base".to_string(),
            version: "1.0.0".to_string(),
            description: "Base extension".to_string(),
            author: "Test".to_string(),
            dependencies: vec![],
            required_rumpsteak_version: Some("0.5.0".to_string()),
            priority: Some(100),
            overview: None,
            syntax_guide: None,
            use_cases: None,
            keywords: None,
        };
        discovery
            .register_extension(
                base_metadata.clone(),
                Box::new(PlaceholderExtension::new(&base_metadata)),
            )
            .unwrap();

        // Add dependent extension
        let dep_metadata = ExtensionMetadata {
            name: "dependent".to_string(),
            version: "1.0.0".to_string(),
            description: "Dependent extension".to_string(),
            author: "Test".to_string(),
            dependencies: vec!["base".to_string()],
            required_rumpsteak_version: Some("0.5.0".to_string()),
            priority: Some(100),
            overview: None,
            syntax_guide: None,
            use_cases: None,
            keywords: None,
        };
        discovery
            .register_extension(
                dep_metadata.clone(),
                Box::new(PlaceholderExtension::new(&dep_metadata)),
            )
            .unwrap();

        let resolved = discovery
            .resolve_dependencies(&["dependent".to_string()])
            .unwrap();
        assert!(resolved.contains(&"base".to_string()));
        assert!(resolved.contains(&"dependent".to_string()));
    }
}
