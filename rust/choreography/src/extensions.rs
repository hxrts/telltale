//! DSL Extension System for Rumpsteak-Aura
//!
//! This module provides a clean, composable system for extending choreographic DSL syntax.
//! Extensions can add new grammar rules, custom statement parsers, and protocol behaviors
//! while maintaining compatibility with the core choreographic infrastructure.

use crate::ast::{LocalType, Role};
use crate::compiler::projection::ProjectionError;
use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::fmt::Debug;

/// Documentation for an extension
#[derive(Debug, Clone)]
pub struct ExtensionDocumentation {
    pub overview: String,
    pub syntax_guide: String,
    pub use_cases: Vec<String>,
    pub limitations: Vec<String>,
    pub see_also: Vec<String>,
}

impl Default for ExtensionDocumentation {
    fn default() -> Self {
        Self {
            overview: "No documentation provided".to_string(),
            syntax_guide: "No syntax guide provided".to_string(),
            use_cases: vec![],
            limitations: vec![],
            see_also: vec![],
        }
    }
}

/// Example usage for an extension
#[derive(Debug, Clone)]
pub struct ExtensionExample {
    pub title: String,
    pub description: String,
    pub code: String,
    pub expected_output: Option<String>,
}

/// Trait for adding new grammar rules to the choreographic DSL
pub trait GrammarExtension: Send + Sync + Debug {
    /// Return the Pest grammar rules this extension provides
    fn grammar_rules(&self) -> &'static str;

    /// List of statement rule names this extension handles
    fn statement_rules(&self) -> Vec<&'static str>;

    /// Priority for conflict resolution (higher = more precedence)
    fn priority(&self) -> u32 {
        100
    }

    /// Extension identifier for debugging and registration
    fn extension_id(&self) -> &'static str;
}

/// Trait for self-documenting extensions
pub trait DocumentedGrammarExtension: GrammarExtension {
    /// Documentation for this extension
    fn documentation(&self) -> ExtensionDocumentation {
        ExtensionDocumentation::default()
    }

    /// Examples showing how to use this extension
    fn examples(&self) -> Vec<ExtensionExample> {
        vec![]
    }

    /// Grammar rules with human-readable descriptions
    fn rule_descriptions(&self) -> std::collections::HashMap<String, String> {
        std::collections::HashMap::new()
    }
}

/// Trait for parsing custom protocol statements
pub trait StatementParser: Send + Sync + Debug {
    /// Check if this parser can handle the given rule name
    fn can_parse(&self, rule_name: &str) -> bool;

    /// Return all rules this parser supports
    fn supported_rules(&self) -> Vec<String>;

    /// Parse a statement into a protocol extension
    ///
    /// # Arguments
    /// * `rule_name` - The grammar rule name being parsed
    /// * `content` - The matched content as a string
    /// * `context` - Parsing context with declared roles
    ///
    /// # Returns
    /// A boxed protocol extension representing the parsed statement
    fn parse_statement(
        &self,
        rule_name: &str,
        content: &str,
        context: &ParseContext,
    ) -> Result<Box<dyn ProtocolExtension>, ParseError>;
}

/// Trait for custom protocol behaviors that can be projected and validated
pub trait ProtocolExtension: Send + Sync + Debug {
    /// Unique identifier for this protocol extension type
    fn type_name(&self) -> &'static str;

    /// Check if this protocol mentions a specific role
    fn mentions_role(&self, role: &Role) -> bool;

    /// Validate this protocol against declared roles
    fn validate(&self, roles: &[Role]) -> Result<(), ExtensionValidationError>;

    /// Project this protocol to a local type for a specific role
    fn project(
        &self,
        role: &Role,
        context: &ProjectionContext,
    ) -> Result<LocalType, ProjectionError>;

    /// Generate code for this protocol extension
    fn generate_code(&self, context: &CodegenContext) -> proc_macro2::TokenStream;

    /// For trait object safety and downcasting
    fn as_any(&self) -> &dyn Any;
    fn as_any_mut(&mut self) -> &mut dyn Any;
    fn type_id(&self) -> TypeId;
}

/// Registry for managing DSL extensions with conflict resolution
#[derive(Debug, Default)]
pub struct ExtensionRegistry {
    grammar_extensions: HashMap<String, Box<dyn GrammarExtension>>,
    statement_parsers: HashMap<String, Box<dyn StatementParser>>,
    rule_to_parser: HashMap<String, String>,
    /// Track rule conflicts for resolution
    rule_conflicts: HashMap<String, Vec<String>>,
    /// Extension dependencies
    extension_dependencies: HashMap<String, Vec<String>>,
    /// Extension version information for compatibility checking
    extension_versions: HashMap<String, String>,
}

impl ExtensionRegistry {
    /// Create a new empty extension registry
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a grammar extension with conflict detection
    pub fn register_grammar<T: GrammarExtension + 'static>(
        &mut self,
        extension: T,
    ) -> Result<(), ParseError> {
        let id = extension.extension_id().to_string();
        let rules = extension.statement_rules();
        let priority = extension.priority();

        // Check for conflicts and resolve by priority
        for rule in &rules {
            if let Some(existing_id) = self.rule_to_parser.get(*rule) {
                let existing_priority = self
                    .grammar_extensions
                    .get(existing_id)
                    .map(|e| e.priority())
                    .unwrap_or(0);

                if priority > existing_priority {
                    // New extension wins, record conflict
                    self.rule_conflicts
                        .entry(rule.to_string())
                        .or_default()
                        .push(existing_id.clone());
                    self.rule_to_parser.insert(rule.to_string(), id.clone());
                } else if priority == existing_priority {
                    // Equal priority - this is a conflict
                    return Err(ParseError::PriorityConflict {
                        extension1: existing_id.clone(),
                        extension2: id.clone(),
                        priority1: existing_priority,
                        priority2: priority,
                        rule: rule.to_string(),
                    });
                }
                // Lower priority - existing extension wins
            } else {
                self.rule_to_parser.insert(rule.to_string(), id.clone());
            }
        }

        self.grammar_extensions
            .insert(id.clone(), Box::new(extension));
        // Set default version if not specified
        self.extension_versions
            .entry(id)
            .or_insert_with(|| "0.1.0".to_string());
        Ok(())
    }

    /// Register a grammar extension with version information
    pub fn register_grammar_with_version<T: GrammarExtension + 'static>(
        &mut self,
        extension: T,
        version: String,
    ) -> Result<(), ParseError> {
        let id = extension.extension_id().to_string();
        self.extension_versions.insert(id.clone(), version);
        self.register_grammar(extension)
    }

    /// Register a grammar extension (legacy method for compatibility)
    pub fn register_grammar_legacy<T: GrammarExtension + 'static>(&mut self, extension: T) {
        let _ = self.register_grammar(extension);
    }

    /// Register a statement parser
    pub fn register_parser<T: StatementParser + 'static>(&mut self, parser: T, parser_id: String) {
        self.statement_parsers.insert(parser_id, Box::new(parser));
    }

    /// Get all grammar rules from registered extensions
    pub fn compose_grammar(&self, base_grammar: &str) -> String {
        let mut composed = base_grammar.to_string();

        // Sort extensions by priority (highest first)
        let mut extensions: Vec<_> = self.grammar_extensions.values().collect();
        extensions.sort_by_key(|b| std::cmp::Reverse(b.priority()));

        for extension in extensions {
            composed.push('\n');
            composed.push_str(extension.grammar_rules());
        }

        composed
    }

    /// Find parser for a given rule name
    pub fn find_parser(&self, rule_name: &str) -> Option<&dyn StatementParser> {
        if let Some(parser_id) = self.rule_to_parser.get(rule_name) {
            self.statement_parsers.get(parser_id).map(|p| p.as_ref())
        } else {
            None
        }
    }

    /// Check if a rule is handled by an extension
    pub fn can_handle(&self, rule_name: &str) -> bool {
        self.rule_to_parser.contains_key(rule_name)
    }

    /// Check if any extensions are registered
    pub fn has_extensions(&self) -> bool {
        !self.grammar_extensions.is_empty() || !self.statement_parsers.is_empty()
    }

    /// Get all grammar extensions
    pub fn grammar_extensions(&self) -> impl Iterator<Item = &dyn GrammarExtension> {
        self.grammar_extensions.values().map(|e| e.as_ref())
    }

    /// Check if a specific extension is registered
    pub fn has_extension(&self, extension_id: &str) -> bool {
        self.grammar_extensions.contains_key(extension_id)
    }

    /// Get parser for a rule name
    pub fn get_parser_for_rule(&self, rule_name: &str) -> Option<&str> {
        self.rule_to_parser.get(rule_name).map(String::as_str)
    }

    /// Get statement parser by ID
    pub fn get_statement_parser(&self, parser_id: &str) -> Option<&dyn StatementParser> {
        self.statement_parsers.get(parser_id).map(|p| p.as_ref())
    }

    /// Add dependency between extensions
    pub fn add_dependency(&mut self, dependent: &str, required: &str) {
        self.extension_dependencies
            .entry(dependent.to_string())
            .or_default()
            .push(required.to_string());
    }

    /// Validate all extension dependencies are satisfied
    pub fn validate_dependencies(&self) -> Result<(), ParseError> {
        for (dependent, requirements) in &self.extension_dependencies {
            for required in requirements {
                if !self.grammar_extensions.contains_key(required) {
                    return Err(ParseError::MissingDependency {
                        extension: dependent.clone(),
                        dependency: required.clone(),
                    });
                }
            }
        }
        Ok(())
    }

    /// Get all rule conflicts for debugging
    pub fn get_conflicts(&self) -> &HashMap<String, Vec<String>> {
        &self.rule_conflicts
    }

    /// Get detailed conflict information with resolution suggestions
    pub fn get_detailed_conflicts(&self) -> Vec<String> {
        let mut details = Vec::new();
        let unknown_ext = "unknown".to_string();

        for (rule, conflicting_extensions) in &self.rule_conflicts {
            if !conflicting_extensions.is_empty() {
                let active_extension = self.rule_to_parser.get(rule).unwrap_or(&unknown_ext);
                let active_priority = self
                    .grammar_extensions
                    .get(active_extension)
                    .map(|e| e.priority())
                    .unwrap_or(0);

                for conflicting in conflicting_extensions {
                    let conflicting_priority = self
                        .grammar_extensions
                        .get(conflicting)
                        .map(|e| e.priority())
                        .unwrap_or(0);

                    details.push(format!(
                        "Rule '{}': Extension '{}' (priority {}) overrode '{}' (priority {}). \
                         To resolve: 1) Adjust priorities, 2) Use different rule names, or 3) Merge functionality.",
                        rule, active_extension, active_priority, conflicting, conflicting_priority
                    ));
                }
            }
        }

        details
    }

    /// Check extension compatibility
    pub fn check_compatibility(&self, extension_ids: &[&str]) -> Result<(), ParseError> {
        // Check for direct conflicts between the specified extensions
        let mut rules_used = HashMap::new();

        for &extension_id in extension_ids {
            if let Some(extension) = self.grammar_extensions.get(extension_id) {
                for rule in extension.statement_rules() {
                    if let Some(existing) = rules_used.get(rule) {
                        if existing != &extension_id {
                            return Err(ParseError::IncompatibleExtensions {
                                details: format!(
                                    "Extensions '{}' and '{}' both define rule '{}'. Use different rule names or register extensions with different priorities.",
                                    existing, extension_id, rule
                                ),
                            });
                        }
                    }
                    rules_used.insert(rule.to_string(), extension_id);
                }
            }
        }
        Ok(())
    }

    /// Create a registry with built-in extensions
    pub fn with_builtin_extensions() -> Self {
        let mut registry = Self::new();

        // Register timeout extension
        registry.register_grammar_legacy(timeout::TimeoutGrammarExtension);
        registry.register_parser(timeout::TimeoutStatementParser, "timeout".to_string());

        registry
    }

    /// Get extension version
    pub fn get_extension_version(&self, extension_id: &str) -> Option<&String> {
        self.extension_versions.get(extension_id)
    }

    /// List all registered extensions with versions
    pub fn list_extensions_with_versions(&self) -> Vec<(String, String)> {
        self.grammar_extensions
            .keys()
            .map(|id| {
                let version = self
                    .extension_versions
                    .get(id)
                    .cloned()
                    .unwrap_or_else(|| "unknown".to_string());
                (id.clone(), version)
            })
            .collect()
    }

    /// Check if extension meets minimum version requirement
    pub fn check_minimum_version(&self, extension_id: &str, min_version: &str) -> bool {
        if let Some(version) = self.extension_versions.get(extension_id) {
            // Simple version comparison - in production would use semver crate
            version.as_str() >= min_version
        } else {
            false
        }
    }

    /// Create a minimal registry for 3rd party integration
    pub fn for_third_party() -> Self {
        Self::new()
    }

    /// Generate basic documentation for all registered extensions
    pub fn generate_docs(&self) -> String {
        let mut docs = String::from("# Extension Documentation\n\n");

        for (id, extension) in &self.grammar_extensions {
            docs.push_str(&format!("## {}\n\n", id));
            docs.push_str(&format!("**Priority:** {}\n\n", extension.priority()));
            docs.push_str(&format!(
                "**Rules:** {}\n\n",
                extension.statement_rules().join(", ")
            ));

            if let Some(version) = self.extension_versions.get(id) {
                docs.push_str(&format!("**Version:** {}\n\n", version));
            }

            docs.push_str("**Grammar:**\n```\n");
            docs.push_str(extension.grammar_rules());
            docs.push_str("\n```\n\n");
        }

        docs
    }

    /// Get basic help for a specific extension
    pub fn get_extension_help(&self, extension_id: &str) -> Option<String> {
        if let Some(extension) = self.grammar_extensions.get(extension_id) {
            let mut help = format!("Extension: {}\n", extension_id);
            help.push_str(&format!("Priority: {}\n", extension.priority()));
            help.push_str(&format!(
                "Rules: {}\n",
                extension.statement_rules().join(", ")
            ));

            if let Some(version) = self.extension_versions.get(extension_id) {
                help.push_str(&format!("Version: {}\n", version));
            }

            help.push_str("\nGrammar:\n");
            help.push_str(extension.grammar_rules());

            Some(help)
        } else {
            None
        }
    }
}

/// Context provided during statement parsing
#[derive(Debug)]
pub struct ParseContext<'a> {
    /// Roles declared in the choreography
    pub declared_roles: &'a [Role],
    /// Original input string for error reporting
    pub input: &'a str,
}

/// Context provided during projection
#[derive(Debug)]
pub struct ProjectionContext<'a> {
    /// All roles in the choreography
    pub all_roles: &'a [Role],
    /// Current role being projected
    pub current_role: &'a Role,
}

/// Context provided during code generation
#[derive(Debug)]
pub struct CodegenContext<'a> {
    /// The choreography being generated
    pub choreography_name: &'a str,
    /// All roles in the choreography
    pub roles: &'a [Role],
    /// Namespace for generated code
    pub namespace: Option<&'a str>,
}

impl<'a> Default for CodegenContext<'a> {
    fn default() -> Self {
        Self {
            choreography_name: "Default",
            roles: &[],
            namespace: None,
        }
    }
}

/// Errors that can occur during extension parsing
#[derive(Debug, thiserror::Error)]
pub enum ParseError {
    #[error("Syntax error: {message}")]
    Syntax { message: String },

    #[error("Unknown role '{role}' used in extension")]
    UnknownRole { role: String },

    #[error("Invalid extension syntax: {details}")]
    InvalidSyntax { details: String },

    #[error("Extension conflict: {message}")]
    Conflict { message: String },

    #[error("Extension priority conflict: Extension '{extension1}' (priority {priority1}) conflicts with '{extension2}' (priority {priority2}) for rule '{rule}'. Consider adjusting priorities or using different rule names.")]
    PriorityConflict {
        extension1: String,
        extension2: String,
        priority1: u32,
        priority2: u32,
        rule: String,
    },

    #[error("Missing dependency: Extension '{extension}' requires '{dependency}' which is not registered. Please register the required extension first.")]
    MissingDependency {
        extension: String,
        dependency: String,
    },

    #[error("Extension registration failed: Extension '{extension}' with rule '{rule}' cannot be registered. {details}")]
    RegistrationFailed {
        extension: String,
        rule: String,
        details: String,
    },

    #[error("Incompatible extensions: {details}")]
    IncompatibleExtensions { details: String },
}

/// Validation errors for protocol extensions
#[derive(Debug, thiserror::Error)]
pub enum ExtensionValidationError {
    #[error("Role '{role}' not declared")]
    UndeclaredRole { role: String },

    #[error("Invalid protocol structure: {reason}")]
    InvalidStructure { reason: String },

    #[error("Extension validation failed: {message}")]
    ExtensionFailed { message: String },
}

/// Convenience macro for registering extensions
#[macro_export]
macro_rules! register_extension {
    ($registry:expr, $extension:expr) => {{
        let ext = $extension;
        let id = ext.extension_id().to_string();
        $registry.register_grammar(ext);
    }};
}

/// Utility trait for easy extension registration
pub trait RegisterExtension {
    fn register_all(registry: &mut ExtensionRegistry);
}

pub mod discovery;
/// Built-in extensions
pub mod timeout;

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug)]
    struct MockGrammarExtension;

    impl GrammarExtension for MockGrammarExtension {
        fn grammar_rules(&self) -> &'static str {
            "timeout_stmt = { \"timeout\" ~ integer ~ protocol_block }"
        }

        fn statement_rules(&self) -> Vec<&'static str> {
            vec!["timeout_stmt"]
        }

        fn extension_id(&self) -> &'static str {
            "mock_timeout"
        }
    }

    #[test]
    fn test_extension_registry() {
        let mut registry = ExtensionRegistry::new();

        // Register extension
        let _ = registry.register_grammar(MockGrammarExtension);

        // Test rule mapping
        assert!(registry.can_handle("timeout_stmt"));
        assert!(!registry.can_handle("unknown_rule"));

        // Test grammar composition
        let base = "basic_rule = { \"test\" }";
        let composed = registry.compose_grammar(base);
        assert!(composed.contains("basic_rule"));
        assert!(composed.contains("timeout_stmt"));
    }

    #[test]
    fn test_enhanced_error_messages() {
        use crate::extensions::ParseError;

        // Test priority conflict error
        let err = ParseError::PriorityConflict {
            extension1: "ext1".to_string(),
            extension2: "ext2".to_string(),
            priority1: 100,
            priority2: 100,
            rule: "test_rule".to_string(),
        };
        assert!(err.to_string().contains("Consider adjusting priorities"));

        // Test missing dependency error
        let err = ParseError::MissingDependency {
            extension: "dependent_ext".to_string(),
            dependency: "required_ext".to_string(),
        };
        assert!(err
            .to_string()
            .contains("Please register the required extension first"));

        // Test incompatible extensions error
        let err = ParseError::IncompatibleExtensions {
            details: "Test incompatibility".to_string(),
        };
        assert!(err.to_string().contains("Incompatible extensions"));
    }

    #[test]
    fn test_detailed_conflicts() {
        #[derive(Debug)]
        struct TestExt1;
        impl GrammarExtension for TestExt1 {
            fn grammar_rules(&self) -> &'static str {
                "rule1 = { \"test1\" }"
            }
            fn statement_rules(&self) -> Vec<&'static str> {
                vec!["rule1"]
            }
            fn priority(&self) -> u32 {
                200
            }
            fn extension_id(&self) -> &'static str {
                "test_ext1"
            }
        }

        #[derive(Debug)]
        struct TestExt2;
        impl GrammarExtension for TestExt2 {
            fn grammar_rules(&self) -> &'static str {
                "rule1 = { \"test2\" }"
            }
            fn statement_rules(&self) -> Vec<&'static str> {
                vec!["rule1"]
            }
            fn priority(&self) -> u32 {
                100
            }
            fn extension_id(&self) -> &'static str {
                "test_ext2"
            }
        }

        let mut registry = ExtensionRegistry::new();

        // Register lower priority first
        let _ = registry.register_grammar(TestExt2);
        // Register higher priority second (should override)
        let _ = registry.register_grammar(TestExt1);

        let conflicts = registry.get_detailed_conflicts();
        assert!(!conflicts.is_empty());
        assert!(conflicts[0].contains("overrode"));
        assert!(conflicts[0].contains("priority"));
    }

    #[test]
    fn test_documentation_system() {
        let mut registry = ExtensionRegistry::new();

        // Register an extension with version
        let _ = registry.register_grammar_with_version(MockGrammarExtension, "1.0.0".to_string());

        // Test documentation generation
        let docs = registry.generate_docs();
        assert!(docs.contains("# Extension Documentation"));
        assert!(docs.contains("mock_timeout"));
        assert!(docs.contains("**Priority:** 100"));
        assert!(docs.contains("**Version:** 1.0.0"));

        // Test getting help for specific extension
        let help = registry.get_extension_help("mock_timeout");
        assert!(help.is_some());
        assert!(help.unwrap().contains("Extension: mock_timeout"));

        // Test listing extensions with versions
        let extensions = registry.list_extensions_with_versions();
        assert!(!extensions.is_empty());
        assert!(extensions
            .iter()
            .any(|(name, version)| name == "mock_timeout" && version == "1.0.0"));
    }

    #[test]
    fn test_parse_context() {
        use proc_macro2::Span;
        let roles = vec![
            Role::new(proc_macro2::Ident::new("Alice", Span::call_site())),
            Role::new(proc_macro2::Ident::new("Bob", Span::call_site())),
        ];

        let context = ParseContext {
            declared_roles: &roles,
            input: "test input",
        };

        assert_eq!(context.declared_roles.len(), 2);
        assert_eq!(context.input, "test input");
    }
}
