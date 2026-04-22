//! Extension-aware parser that integrates with the existing parser
//!
//! This module provides a parser that can handle both standard choreographic
//! constructs and extension-defined syntax by leveraging the shared extension
//! registry and parser dispatch path.

use crate::compiler::grammar::GrammarCompositionError;
use crate::compiler::parser::{parse_choreography_str_with_extensions, ParseError};
use crate::extensions::{ExtensionRegistry, GrammarExtension, StatementParser};

/// Extension-aware parser that can handle both core and extension syntax
pub struct ExtensionParser {
    extension_registry: ExtensionRegistry,
    /// Pre-allocated buffer for parsing operations to reduce allocations
    parse_buffer: String,
}

impl ExtensionParser {
    /// Create a new extension parser
    pub fn new() -> Self {
        Self {
            extension_registry: ExtensionRegistry::new(),
            parse_buffer: String::with_capacity(1024), // Pre-allocate for common case
        }
    }

    /// Register an extension with both grammar and parsing support.
    ///
    /// # Errors
    ///
    /// Returns an error if the grammar extension cannot be registered.
    pub fn register_extension<G, P>(
        &mut self,
        grammar_ext: G,
        statement_parser: P,
    ) -> Result<(), crate::extensions::ParseError>
    where
        G: GrammarExtension + 'static,
        P: StatementParser + 'static,
    {
        let parser_id = grammar_ext.extension_id().to_string();
        self.extension_registry.register_grammar(grammar_ext)?;
        self.extension_registry
            .register_parser(statement_parser, parser_id);
        Ok(())
    }

    /// Parse a choreography string with extension support (optimized)
    pub fn parse_with_extensions(
        &mut self,
        input: &str,
    ) -> Result<crate::ast::Choreography, ExtensionParseError> {
        // Clear and reuse buffers to reduce allocations
        self.parse_buffer.clear();

        // Reserve capacity based on input size for efficient parsing
        self.parse_buffer.reserve(input.len());
        parse_choreography_str_with_extensions(input, &self.extension_registry)
            .map(|(choreography, _)| choreography)
            .map_err(ExtensionParseError::StandardParseError)
    }

    /// Check if an extension can handle a given statement
    pub fn can_handle_statement(&self, statement_type: &str) -> bool {
        self.extension_registry.can_handle(statement_type)
    }

    /// Get the composed grammar for debugging
    pub fn get_composed_grammar(&self) -> Result<String, GrammarCompositionError> {
        compose_grammar_from_registry(&self.extension_registry)
    }

    /// Get statistics about registered extensions
    pub fn extension_stats(&self) -> ExtensionStats {
        ExtensionStats {
            grammar_extensions: self.extension_registry.grammar_extensions().count(),
            statement_parsers: self.extension_registry.statement_parser_count(),
        }
    }
}

impl Default for ExtensionParser {
    fn default() -> Self {
        Self::new()
    }
}

fn compose_grammar_from_registry(
    registry: &ExtensionRegistry,
) -> Result<String, GrammarCompositionError> {
    let base_grammar = include_str!("choreography.pest");
    let extension_rules = registry.compose_grammar("");
    if extension_rules.trim().is_empty() {
        return Ok(base_grammar.to_string());
    }

    let statement_rules: Vec<_> = registry.statement_rules();
    let mut lines: Vec<String> = base_grammar.lines().map(ToOwned::to_owned).collect();
    let (stmt_start, stmt_end) = find_statement_rule_bounds(&lines)?;
    let indent = find_statement_indent(&lines, stmt_start, stmt_end);
    let insert_lines: Vec<String> = statement_rules
        .iter()
        .map(|rule| format!("{indent}| {rule}"))
        .collect();
    lines.splice(stmt_end..stmt_end, insert_lines);

    let mut composed = lines.join("\n");
    composed.push('\n');
    composed.push_str("// Extension Rules\n");
    composed.push_str(&extension_rules);
    Ok(composed)
}

fn find_statement_rule_bounds(lines: &[String]) -> Result<(usize, usize), GrammarCompositionError> {
    let start = lines
        .iter()
        .position(|line| line.trim_start().starts_with("statement = _{"))
        .ok_or_else(|| {
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

/// Statistics about registered extensions
#[derive(Debug, Clone)]
pub struct ExtensionStats {
    pub grammar_extensions: usize,
    pub statement_parsers: usize,
}

/// Errors that can occur during extension-aware parsing
#[derive(Debug, thiserror::Error)]
pub enum ExtensionParseError {
    #[error("Standard parsing failed: {0}")]
    StandardParseError(#[from] ParseError),

    #[error("Grammar composition failed: {0}")]
    GrammarComposition(#[from] GrammarCompositionError),

    #[error("Extension parsing failed: {0}")]
    ExtensionParsing(String),

    #[error("Unknown extension statement: {0}")]
    UnknownExtension(String),
}

/// Builder for extension parsers
pub struct ExtensionParserBuilder {
    parser: ExtensionParser,
}

impl ExtensionParserBuilder {
    pub fn new() -> Self {
        Self {
            parser: ExtensionParser::new(),
        }
    }

    pub fn with_extension<G, P>(
        mut self,
        grammar_ext: G,
        statement_parser: P,
    ) -> Result<Self, crate::extensions::ParseError>
    where
        G: crate::extensions::GrammarExtension + 'static,
        P: StatementParser + 'static,
    {
        self.parser
            .register_extension(grammar_ext, statement_parser)?;
        Ok(self)
    }

    pub fn build(self) -> ExtensionParser {
        self.parser
    }
}

impl Default for ExtensionParserBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Helper function to create an extension parser with common extensions
pub fn create_standard_extension_parser() -> ExtensionParser {
    ExtensionParserBuilder::new()
        // Add standard extensions here as they're developed
        .build()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::extensions::{GrammarExtension, ParseContext, StatementParser};

    #[derive(Debug)]
    struct TestGrammarExtension;

    impl GrammarExtension for TestGrammarExtension {
        fn grammar_rules(&self) -> &'static str {
            "test_extension_stmt = { \"test\" ~ ident }"
        }

        fn statement_rules(&self) -> Vec<&'static str> {
            vec!["test_extension_stmt"]
        }

        fn extension_id(&self) -> &'static str {
            "test_extension"
        }
    }

    #[derive(Debug)]
    struct TestStatementParser;

    impl StatementParser for TestStatementParser {
        fn can_parse(&self, rule_name: &str) -> bool {
            rule_name == "test_extension_stmt"
        }

        fn supported_rules(&self) -> Vec<String> {
            vec!["test_extension_stmt".to_string()]
        }

        fn parse_statement(
            &self,
            _rule_name: &str,
            _content: &str,
            _context: &ParseContext,
        ) -> Result<Box<dyn crate::extensions::ProtocolExtension>, crate::extensions::ParseError>
        {
            // This would normally parse the statement content
            Err(crate::extensions::ParseError::Syntax {
                message: "Test parser - not implemented".to_string(),
            })
        }
    }

    #[test]
    fn test_extension_parser_creation() {
        let parser = ExtensionParser::new();
        let stats = parser.extension_stats();
        assert_eq!(stats.grammar_extensions, 0);
    }

    #[test]
    fn test_extension_registration() {
        let mut parser = ExtensionParser::new();
        parser
            .register_extension(TestGrammarExtension, TestStatementParser)
            .expect("extension should register");

        let stats = parser.extension_stats();
        assert_eq!(stats.grammar_extensions, 1);
        assert!(parser.can_handle_statement("test_extension_stmt"));
    }

    #[test]
    fn test_builder_pattern() {
        let parser = ExtensionParserBuilder::new()
            .with_extension(TestGrammarExtension, TestStatementParser)
            .expect("test extension should register")
            .build();

        assert!(parser.can_handle_statement("test_extension_stmt"));
    }

    #[test]
    fn test_standard_parsing() {
        let mut parser = ExtensionParser::new();

        let input = "protocol TestProtocol =\n  roles Alice, Bob\n  Alice -> Bob : Message\n";

        let result = parser.parse_with_extensions(input);
        assert!(result.is_ok(), "Should parse standard choreography");
    }

    #[test]
    fn test_composed_grammar_generation() {
        let mut parser = ExtensionParser::new();
        parser
            .register_extension(TestGrammarExtension, TestStatementParser)
            .expect("extension should register");

        let result = parser.get_composed_grammar();
        assert!(result.is_ok(), "Should generate composed grammar");

        let grammar = result.unwrap();
        assert!(
            grammar.contains("test_extension_stmt"),
            "Should contain extension rule"
        );
        assert!(
            grammar.contains("choreography"),
            "Should contain base rules"
        );
    }
}
