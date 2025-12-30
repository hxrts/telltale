//! Extension-aware parser that integrates with the existing parser
//!
//! This module provides a parser that can handle both standard choreographic
//! constructs and extension-defined syntax by leveraging the grammar composition system.

use crate::ast::{Protocol, Role};
use crate::compiler::grammar::{GrammarComposer, GrammarCompositionError};
use crate::compiler::parser::{parse_choreography_str, ParseError};
use crate::extensions::StatementParser;

/// Extension-aware parser that can handle both core and extension syntax
pub struct ExtensionParser {
    grammar_composer: GrammarComposer,
    /// Pre-allocated buffer for parsing operations to reduce allocations
    parse_buffer: String,
    /// Pre-allocated HashMap for annotations to reduce allocations
    annotation_cache: std::collections::HashMap<String, String>,
}

impl ExtensionParser {
    /// Create a new extension parser
    pub fn new() -> Self {
        Self {
            grammar_composer: GrammarComposer::new(),
            parse_buffer: String::with_capacity(1024), // Pre-allocate for common case
            annotation_cache: std::collections::HashMap::with_capacity(16), // Pre-allocate for annotations
        }
    }

    /// Register an extension with both grammar and parsing support
    ///
    /// Note: Grammar extensions are fully supported and registered with the grammar composer.
    /// Statement parsers are accepted but not currently stored. Extension parsing passes
    /// through the standard parser - full extension statement dispatch is a planned feature.
    pub fn register_extension<G, P>(&mut self, grammar_ext: G, _statement_parser: P)
    where
        G: crate::extensions::GrammarExtension + 'static,
        P: StatementParser + 'static,
    {
        // Register grammar extension (this also registers the grammar rules for rule mapping)
        self.grammar_composer.register_extension(grammar_ext);

        // Statement parser registration is accepted but not stored.
        // Full extension statement dispatch will require extending GrammarComposer
        // to track parsers alongside grammar rules.
    }

    /// Parse a choreography string with extension support (optimized)
    pub fn parse_with_extensions(
        &mut self,
        input: &str,
    ) -> Result<crate::ast::Choreography, ExtensionParseError> {
        // Clear and reuse buffers to reduce allocations
        self.parse_buffer.clear();
        self.annotation_cache.clear();

        // Reserve capacity based on input size for efficient parsing
        self.parse_buffer.reserve(input.len());

        // For now, we'll use a hybrid approach:
        // 1. Try parsing with the standard parser first
        // 2. If successful, post-process to handle any extension statements

        let mut choreography =
            parse_choreography_str(input).map_err(ExtensionParseError::StandardParseError)?;

        // Post-process to identify and parse extension statements (optimized)
        choreography.protocol =
            self.process_extensions_optimized(choreography.protocol, input, &choreography.roles)?;

        Ok(choreography)
    }

    /// Process a protocol tree to identify and dispatch extension statements.
    ///
    /// Currently a pass-through - returns the protocol unchanged.
    /// Full extension statement dispatch will be implemented when extension parsing
    /// requirements are finalized. The implementation will:
    /// 1. Parse with the composed grammar
    /// 2. Identify extension statements in the parse tree
    /// 3. Dispatch to registered extension parsers
    fn process_extensions_optimized(
        &mut self,
        protocol: Protocol,
        _input: &str,
        _roles: &[Role],
    ) -> Result<Protocol, ExtensionParseError> {
        // Currently a pass-through. Extension statements are identified
        // by the grammar composer but not yet dispatched to parsers.
        Ok(protocol)
    }

    /// Check if an extension can handle a given statement
    pub fn can_handle_statement(&self, statement_type: &str) -> bool {
        self.grammar_composer.has_extension_rule(statement_type)
    }

    /// Get the composed grammar for debugging
    pub fn get_composed_grammar(&mut self) -> Result<String, GrammarCompositionError> {
        self.grammar_composer.compose()
    }

    /// Get statistics about registered extensions
    pub fn extension_stats(&self) -> ExtensionStats {
        ExtensionStats {
            grammar_extensions: self.grammar_composer.extension_count(),
            // Statement parsers are not stored separately (see register_extension doc)
            statement_parsers: 0,
        }
    }
}

impl Default for ExtensionParser {
    fn default() -> Self {
        Self::new()
    }
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

    pub fn with_extension<G, P>(mut self, grammar_ext: G, statement_parser: P) -> Self
    where
        G: crate::extensions::GrammarExtension + 'static,
        P: StatementParser + 'static,
    {
        self.parser
            .register_extension(grammar_ext, statement_parser);
        self
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
            "test_stmt = { \"test\" ~ ident }"
        }

        fn statement_rules(&self) -> Vec<&'static str> {
            vec!["test_stmt"]
        }

        fn extension_id(&self) -> &'static str {
            "test_extension"
        }
    }

    #[derive(Debug)]
    struct TestStatementParser;

    impl StatementParser for TestStatementParser {
        fn can_parse(&self, rule_name: &str) -> bool {
            rule_name == "test_stmt"
        }

        fn supported_rules(&self) -> Vec<String> {
            vec!["test_stmt".to_string()]
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
        parser.register_extension(TestGrammarExtension, TestStatementParser);

        let stats = parser.extension_stats();
        assert_eq!(stats.grammar_extensions, 1);
        assert!(parser.can_handle_statement("test_stmt"));
    }

    #[test]
    fn test_builder_pattern() {
        let parser = ExtensionParserBuilder::new()
            .with_extension(TestGrammarExtension, TestStatementParser)
            .build();

        assert!(parser.can_handle_statement("test_stmt"));
    }

    #[test]
    fn test_standard_parsing() {
        let mut parser = ExtensionParser::new();

        let input = r#"
            choreography TestProtocol {
                roles: Alice, Bob;
                Alice -> Bob: Message;
            }
        "#;

        let result = parser.parse_with_extensions(input);
        assert!(result.is_ok(), "Should parse standard choreography");
    }

    #[test]
    fn test_composed_grammar_generation() {
        let mut parser = ExtensionParser::new();
        parser.register_extension(TestGrammarExtension, TestStatementParser);

        let result = parser.get_composed_grammar();
        assert!(result.is_ok(), "Should generate composed grammar");

        let grammar = result.unwrap();
        assert!(
            grammar.contains("test_stmt"),
            "Should contain extension rule"
        );
        assert!(
            grammar.contains("choreography"),
            "Should contain base rules"
        );
    }
}
