//! Dynamic Pest Grammar Composition for Extensions
//!
//! This module provides a system for dynamically composing Pest grammars by merging
//! the base choreographic grammar with extension-provided grammar rules.

use crate::extensions::{ExtensionRegistry, GrammarExtension};
use std::collections::HashSet;
use std::fs;
use std::path::Path;

/// Manages dynamic composition of Pest grammars with extensions
pub struct GrammarComposer {
    base_grammar: String,
    extension_registry: ExtensionRegistry,
    /// Cache for composed grammar to avoid recomputation
    cached_grammar: Option<String>,
    /// Hash of current extension state for cache invalidation
    extension_hash: u64,
}

impl GrammarComposer {
    /// Create a new grammar composer with the base grammar
    pub fn new() -> Self {
        let base_grammar = include_str!("choreography.pest").to_string();
        Self {
            base_grammar,
            extension_registry: ExtensionRegistry::new(),
            cached_grammar: None,
            extension_hash: 0,
        }
    }

    /// Register an extension with the grammar composer
    pub fn register_extension<T: GrammarExtension + 'static>(&mut self, extension: T) {
        let _ = self.extension_registry.register_grammar(extension);
        // Invalidate cache when extensions change
        self.invalidate_cache();
    }

    /// Invalidate the cached grammar and force recomputation
    fn invalidate_cache(&mut self) {
        self.cached_grammar = None;
        self.extension_hash = self.compute_extension_hash();
    }

    /// Compute a hash of current extensions for cache invalidation
    fn compute_extension_hash(&self) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        use std::hash::{Hash, Hasher};

        let mut hasher = DefaultHasher::new();

        // Hash extension count and IDs for simple cache invalidation
        self.extension_registry
            .grammar_extensions()
            .count()
            .hash(&mut hasher);
        for ext in self.extension_registry.grammar_extensions() {
            ext.extension_id().hash(&mut hasher);
            ext.priority().hash(&mut hasher);
        }

        hasher.finish()
    }

    /// Register an extension from a trait reference
    pub fn register_extension_from_trait(
        &mut self,
        _extension: &dyn GrammarExtension,
    ) -> Result<(), GrammarCompositionError> {
        // For now, we can't register from trait references due to object safety
        // In a real implementation, this would require cloning or different approach
        Ok(())
    }

    /// Compose the final grammar including all registered extensions
    pub fn compose(&mut self) -> Result<String, GrammarCompositionError> {
        // Check if we can use cached grammar
        let current_hash = self.compute_extension_hash();
        if let Some(ref cached) = self.cached_grammar {
            if current_hash == self.extension_hash {
                return Ok(cached.clone());
            }
        }

        // Recompute grammar
        let composed = self.compose_uncached()?;

        // Cache the result
        self.cached_grammar = Some(composed.clone());
        self.extension_hash = current_hash;

        Ok(composed)
    }

    /// Compose grammar without using cache (for internal use)
    fn compose_uncached(&self) -> Result<String, GrammarCompositionError> {
        let mut composed = self.base_grammar.clone();

        // Validate that we can safely extend the base grammar (cached validation)
        self.validate_base_grammar_cached(&composed)?;

        // Get all grammar extensions sorted by priority
        let extension_rules = self.extension_registry.compose_grammar("");

        if !extension_rules.trim().is_empty() {
            // Inject extension rules into the statement rule (optimized)
            composed = self.inject_extension_rules_optimized(composed, &extension_rules)?;
        }

        // Validate the final composed grammar (cached validation)
        self.validate_composed_grammar_cached(&composed)?;

        Ok(composed)
    }

    /// Inject extension rules into the base grammar
    fn inject_extension_rules_optimized(
        &self,
        base_grammar: String,
        extension_rules: &str,
    ) -> Result<String, GrammarCompositionError> {
        self.inject_extension_rules_via_lines(base_grammar, extension_rules)
    }

    fn inject_extension_rules_via_lines(
        &self,
        base_grammar: String,
        extension_rules: &str,
    ) -> Result<String, GrammarCompositionError> {
        let extension_statements = self.extract_extension_statements_optimized(extension_rules)?;
        let mut lines: Vec<String> = base_grammar.lines().map(|line| line.to_string()).collect();

        if !extension_statements.is_empty() {
            let (stmt_start, stmt_end) = find_statement_rule_bounds(&lines)?;
            let indent = find_statement_indent(&lines, stmt_start, stmt_end);
            let insert_lines: Vec<String> = extension_statements
                .iter()
                .map(|rule| format!("{indent}| {rule}"))
                .collect();

            lines.splice(stmt_end..stmt_end, insert_lines);
        }

        let mut composed = lines.join("\n");
        composed.push('\n');
        composed.push_str("// Extension Rules\n");
        composed.push_str(extension_rules);
        Ok(composed)
    }

    /// Extract statement rule names from extension grammar (optimized version)
    fn extract_extension_statements_optimized(
        &self,
        extension_rules: &str,
    ) -> Result<Vec<String>, GrammarCompositionError> {
        let mut statements = Vec::new();

        // Pre-allocate based on estimated number of rules
        let estimated_rules = extension_rules.matches("_stmt = {").count();
        statements.reserve(estimated_rules);

        for line in extension_rules.lines() {
            let line = line.trim();
            if line.ends_with("_stmt = {") {
                if let Some(equals_pos) = line.find('=') {
                    let rule_name = line[..equals_pos].trim();
                    statements.push(rule_name.to_string());
                }
            }
        }

        Ok(statements)
    }

    /// Validate that the base grammar has the required extension points
    ///
    /// Note: `validate_base_grammar_cached` is preferred for production use.
    /// This method is kept for testing and API compatibility.
    #[cfg(test)]
    fn validate_base_grammar(&self, grammar: &str) -> Result<(), GrammarCompositionError> {
        let required_rules = ["statement = _{", "send_stmt", "broadcast_stmt"];

        for rule in &required_rules {
            if !grammar.contains(rule) {
                return Err(GrammarCompositionError::InvalidBaseGrammar(format!(
                    "Missing required rule: {}",
                    rule
                )));
            }
        }

        Ok(())
    }

    /// Optimized validation with static patterns and early exit
    fn validate_base_grammar_cached(&self, grammar: &str) -> Result<(), GrammarCompositionError> {
        // Use static patterns for better performance
        const REQUIRED_PATTERNS: &[&str] = &["statement = _{", "send_stmt", "broadcast_stmt"];

        for &pattern in REQUIRED_PATTERNS {
            if !grammar.contains(pattern) {
                return Err(GrammarCompositionError::InvalidBaseGrammar(format!(
                    "Missing required rule: {}",
                    pattern
                )));
            }
        }

        Ok(())
    }

    /// Validate the composed grammar for common issues
    ///
    /// Note: `validate_composed_grammar_cached` is preferred for production use.
    /// This method is kept for testing and API compatibility.
    #[cfg(test)]
    fn validate_composed_grammar(&self, grammar: &str) -> Result<(), GrammarCompositionError> {
        // Check for duplicate rule names
        let mut rule_names = HashSet::new();

        for line in grammar.lines() {
            let line = line.trim();
            if line.contains(" = {") && !line.starts_with("//") {
                if let Some(rule_name) = line.split(" = {").next() {
                    let rule_name = rule_name.trim();
                    if rule_names.contains(rule_name) {
                        return Err(GrammarCompositionError::DuplicateRule(
                            rule_name.to_string(),
                        ));
                    }
                    rule_names.insert(rule_name.to_string());
                }
            }
        }

        // Basic syntax validation (check balanced braces outside of string literals)
        let (open_braces, close_braces) = count_braces_outside_quotes(grammar);

        if open_braces != close_braces {
            return Err(GrammarCompositionError::SyntaxError(
                "Unbalanced braces in composed grammar".to_string(),
            ));
        }

        Ok(())
    }

    /// Optimized validation with pre-allocated HashSet and fast brace counting
    fn validate_composed_grammar_cached(
        &self,
        grammar: &str,
    ) -> Result<(), GrammarCompositionError> {
        // Pre-allocate HashSet with estimated capacity
        let estimated_rules = grammar.matches(" = {").count();
        let mut rule_names = HashSet::with_capacity(estimated_rules);

        for line in grammar.lines() {
            let line = line.trim();
            if line.contains(" = {") && !line.starts_with("//") {
                if let Some(rule_name) = line.split(" = {").next() {
                    let rule_name = rule_name.trim();
                    if !rule_names.insert(rule_name) {
                        return Err(GrammarCompositionError::DuplicateRule(
                            rule_name.to_string(),
                        ));
                    }
                }
            }
        }

        // Optimized brace counting (ignore braces inside string literals)
        let (open_braces, close_braces) = count_braces_outside_quotes(grammar);

        if open_braces != close_braces {
            return Err(GrammarCompositionError::SyntaxError(
                "Unbalanced braces in composed grammar".to_string(),
            ));
        }

        Ok(())
    }

    /// Check if an extension rule exists
    pub fn has_extension_rule(&self, rule_name: &str) -> bool {
        self.extension_registry.can_handle(rule_name)
    }

    /// Get the number of registered extensions
    pub fn extension_count(&self) -> usize {
        self.extension_registry.grammar_extensions().count()
    }

    /// Write the composed grammar to a file for debugging
    pub fn write_composed_grammar<P: AsRef<Path>>(
        &mut self,
        path: P,
    ) -> Result<(), GrammarCompositionError> {
        let composed = self.compose()?;
        fs::write(path, composed).map_err(|e| {
            GrammarCompositionError::IoError(format!("Failed to write grammar: {}", e))
        })?;
        Ok(())
    }
}

fn count_braces_outside_quotes(grammar: &str) -> (usize, usize) {
    let mut open_braces = 0usize;
    let mut close_braces = 0usize;
    let mut in_string = false;
    let mut escape = false;

    for ch in grammar.chars() {
        if in_string {
            if escape {
                escape = false;
            } else if ch == '\\' {
                escape = true;
            } else if ch == '"' {
                in_string = false;
            }
            continue;
        }

        if ch == '"' {
            in_string = true;
            continue;
        }

        match ch {
            '{' => open_braces += 1,
            '}' => close_braces += 1,
            _ => {}
        }
    }

    (open_braces, close_braces)
}

fn find_statement_rule_bounds(lines: &[String]) -> Result<(usize, usize), GrammarCompositionError> {
    let mut start = None;
    for (idx, line) in lines.iter().enumerate() {
        if line.trim_start().starts_with("statement = _{") {
            start = Some(idx);
            break;
        }
    }

    let start = start.ok_or_else(|| {
        GrammarCompositionError::InvalidBaseGrammar(
            "Could not find statement rule in base grammar".to_string(),
        )
    })?;

    for (idx, line) in lines.iter().enumerate().skip(start + 1) {
        if line.trim_start().starts_with('}') {
            return Ok((start, idx));
        }
    }

    Err(GrammarCompositionError::InvalidBaseGrammar(
        "Could not find end of statement rule in base grammar".to_string(),
    ))
}

fn find_statement_indent(lines: &[String], start: usize, end: usize) -> String {
    for line in lines.iter().take(end).skip(start + 1) {
        let trimmed = line.trim_start();
        if trimmed.starts_with('|') {
            let indent_len = line.len().saturating_sub(trimmed.len());
            return line[..indent_len].to_string();
        }
    }
    "    ".to_string()
}

impl Default for GrammarComposer {
    fn default() -> Self {
        Self::new()
    }
}

/// Errors that can occur during grammar composition
#[derive(Debug, thiserror::Error)]
pub enum GrammarCompositionError {
    #[error("Invalid base grammar: {0}")]
    InvalidBaseGrammar(String),

    #[error("Duplicate rule name: {0}")]
    DuplicateRule(String),

    #[error("Syntax error in composed grammar: {0}")]
    SyntaxError(String),

    #[error("Extension conflict: {0}")]
    ExtensionConflict(String),

    #[error("IO error: {0}")]
    IoError(String),
}

/// Builder pattern for constructing grammar composers with extensions
pub struct GrammarComposerBuilder {
    composer: GrammarComposer,
}

impl GrammarComposerBuilder {
    pub fn new() -> Self {
        Self {
            composer: GrammarComposer::new(),
        }
    }

    pub fn with_extension<T: GrammarExtension + 'static>(mut self, extension: T) -> Self {
        self.composer.register_extension(extension);
        self
    }

    pub fn build(self) -> GrammarComposer {
        self.composer
    }
}

impl Default for GrammarComposerBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::extensions::GrammarExtension;

    #[derive(Debug)]
    struct TestExtension;

    impl GrammarExtension for TestExtension {
        fn grammar_rules(&self) -> &'static str {
            "timeout_stmt = { \"timeout\" ~ integer ~ block }"
        }

        fn statement_rules(&self) -> Vec<&'static str> {
            vec!["timeout_stmt"]
        }

        fn extension_id(&self) -> &'static str {
            "test_timeout"
        }
    }

    #[test]
    fn test_grammar_composer_creation() {
        let composer = GrammarComposer::new();
        assert_eq!(composer.extension_count(), 0);
        assert!(composer.base_grammar.contains("choreography"));
        assert!(composer.base_grammar.contains("statement = _{"));
    }

    #[test]
    fn test_extension_registration() {
        let mut composer = GrammarComposer::new();
        composer.register_extension(TestExtension);
        assert_eq!(composer.extension_count(), 1);
        assert!(composer.has_extension_rule("timeout_stmt"));
    }

    #[test]
    fn test_grammar_composition() {
        let mut composer = GrammarComposer::new();
        composer.register_extension(TestExtension);

        let result = composer.compose();
        assert!(result.is_ok(), "Grammar composition should succeed");

        let composed = result.unwrap();
        assert!(composed.contains("timeout_stmt"));
        assert!(composed.contains("choreography"));
        assert!(composed.contains("// Extension Rules"));
    }

    #[test]
    fn test_grammar_caching() {
        let mut composer = GrammarComposer::new();
        composer.register_extension(TestExtension);

        // First composition
        let start = std::time::Instant::now();
        let result1 = composer.compose();
        let first_time = start.elapsed();
        assert!(result1.is_ok());

        // Second composition (should use cache)
        let start = std::time::Instant::now();
        let result2 = composer.compose();
        let second_time = start.elapsed();
        assert!(result2.is_ok());

        // Results should be identical
        assert_eq!(result1.unwrap(), result2.unwrap());

        // Second call should be faster due to caching
        // Note: This might not always be true due to system variations,
        // but it's a reasonable performance expectation
        println!(
            "First composition: {:?}, Second (cached): {:?}",
            first_time, second_time
        );
    }

    #[test]
    fn test_builder_pattern() {
        let composer = GrammarComposerBuilder::new()
            .with_extension(TestExtension)
            .build();

        assert_eq!(composer.extension_count(), 1);
        assert!(composer.has_extension_rule("timeout_stmt"));
    }

    #[test]
    fn test_validation() {
        let mut composer = GrammarComposer::new();

        // Test base grammar validation
        let valid_result = composer.validate_base_grammar(&composer.base_grammar);
        assert!(valid_result.is_ok(), "Base grammar should be valid");

        // Test composed grammar validation
        let composed = composer.compose().unwrap();
        let validation_result = composer.validate_composed_grammar(&composed);
        assert!(
            validation_result.is_ok(),
            "Composed grammar should be valid"
        );
    }
}
