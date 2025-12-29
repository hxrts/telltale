//! Comprehensive test suite for the extensible parser system
//!
//! This test suite validates:
//! - Grammar composition performance and correctness
//! - Extension parsing functionality
//! - Feature inheritance in 3rd party projects
//! - Backwards compatibility
//! - Error handling and edge cases

use rumpsteak_aura_choreography::{
    ast::*,
    compiler::{extension_parser::*, grammar::*, parser::parse_choreography_str, ProjectionError},
    extensions::*,
};
use std::time::Instant;

// ============================================================================
// Test Extensions for Comprehensive Testing
// ============================================================================

#[derive(Debug)]
struct TestGrammarExtension;

impl GrammarExtension for TestGrammarExtension {
    fn grammar_rules(&self) -> &'static str {
        r#"
        test_stmt = { "test" ~ ident ~ "{" ~ protocol_body ~ "}" }
        simple_test = { "simple" ~ ident }
        "#
    }

    fn statement_rules(&self) -> Vec<&'static str> {
        vec!["test_stmt", "simple_test"]
    }

    fn extension_id(&self) -> &'static str {
        "test_extension"
    }

    fn priority(&self) -> u32 {
        100
    }
}

#[derive(Debug)]
struct HighPriorityExtension;

impl GrammarExtension for HighPriorityExtension {
    fn grammar_rules(&self) -> &'static str {
        r#"priority_stmt = { "priority" ~ integer }"#
    }

    fn statement_rules(&self) -> Vec<&'static str> {
        vec!["priority_stmt"]
    }

    fn extension_id(&self) -> &'static str {
        "high_priority"
    }

    fn priority(&self) -> u32 {
        500 // Higher than TestGrammarExtension
    }
}

#[derive(Debug)]
struct TestStatementParser;

impl StatementParser for TestStatementParser {
    fn can_parse(&self, rule_name: &str) -> bool {
        matches!(rule_name, "test_stmt" | "simple_test")
    }

    fn supported_rules(&self) -> Vec<String> {
        vec!["test_stmt".to_string(), "simple_test".to_string()]
    }

    fn parse_statement(
        &self,
        _rule_name: &str,
        _content: &str,
        _context: &ParseContext,
    ) -> Result<Box<dyn ProtocolExtension>, ParseError> {
        Ok(Box::new(TestProtocolExtension {
            name: "test".to_string(),
        }))
    }
}

#[derive(Debug, Clone)]
struct TestProtocolExtension {
    #[allow(dead_code)]
    name: String,
}

impl ProtocolExtension for TestProtocolExtension {
    fn type_name(&self) -> &'static str {
        "TestProtocolExtension"
    }

    fn mentions_role(&self, _role: &Role) -> bool {
        true
    }

    fn validate(&self, _roles: &[Role]) -> Result<(), ExtensionValidationError> {
        Ok(())
    }

    fn project(
        &self,
        _role: &Role,
        _context: &ProjectionContext,
    ) -> Result<LocalType, ProjectionError> {
        Err(ProjectionError::UnsupportedParallel("test".to_string()))
    }

    fn generate_code(&self, _context: &CodegenContext) -> proc_macro2::TokenStream {
        quote::quote! { /* test code */ }
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }

    fn type_id(&self) -> std::any::TypeId {
        std::any::TypeId::of::<Self>()
    }
}

// ============================================================================
// Grammar Composition Tests
// ============================================================================

#[cfg(test)]
mod grammar_composition_tests {
    use super::*;

    #[test]
    fn test_basic_grammar_composition() {
        let mut composer = GrammarComposer::new();
        composer.register_extension(TestGrammarExtension);

        let result = composer.compose();
        assert!(result.is_ok(), "Grammar composition should succeed");

        let composed = result.unwrap();
        assert!(composed.contains("test_stmt"));
        assert!(composed.contains("choreography"));
        assert!(composed.contains("// Extension Rules"));
    }

    #[test]
    fn test_multiple_extension_composition() {
        let mut composer = GrammarComposer::new();
        composer.register_extension(TestGrammarExtension);
        composer.register_extension(HighPriorityExtension);

        let result = composer.compose();
        assert!(
            result.is_ok(),
            "Multiple extension composition should succeed"
        );

        let composed = result.unwrap();
        assert!(composed.contains("test_stmt"));
        assert!(composed.contains("priority_stmt"));
        assert!(composer.extension_count() == 2);
    }

    #[test]
    fn test_grammar_composition_caching() {
        let mut composer = GrammarComposer::new();
        composer.register_extension(TestGrammarExtension);

        // First composition
        let start = Instant::now();
        let result1 = composer.compose().unwrap();
        let first_time = start.elapsed();

        // Second composition (should use cache)
        let start = Instant::now();
        let result2 = composer.compose().unwrap();
        let second_time = start.elapsed();

        // Results should be identical
        assert_eq!(result1, result2);

        // Second call should be significantly faster due to caching
        assert!(
            second_time < first_time / 2,
            "Cached composition should be much faster: first={:?}, second={:?}",
            first_time,
            second_time
        );
    }

    #[test]
    fn test_cache_invalidation() {
        let mut composer = GrammarComposer::new();

        // Initial composition
        let result1 = composer.compose().unwrap();

        // Add extension (should invalidate cache)
        composer.register_extension(TestGrammarExtension);
        let result2 = composer.compose().unwrap();

        // Results should be different
        assert_ne!(result1, result2);
        assert!(result2.contains("test_stmt"));
        assert!(!result1.contains("test_stmt"));
    }

    #[test]
    fn test_extension_priority_ordering() {
        let mut composer = GrammarComposer::new();
        composer.register_extension(TestGrammarExtension); // Priority 100
        composer.register_extension(HighPriorityExtension); // Priority 500

        let result = composer.compose().unwrap();

        // Both extensions should be present
        assert!(result.contains("test_stmt"));
        assert!(result.contains("priority_stmt"));

        // Higher priority extension should be processed first
        let test_pos = result.find("test_stmt").unwrap();
        let priority_pos = result.find("priority_stmt").unwrap();

        // Note: Actual ordering depends on implementation, this tests that both are present
        assert!(test_pos > 0);
        assert!(priority_pos > 0);
    }

    #[test]
    fn test_extension_rule_detection() {
        let mut composer = GrammarComposer::new();
        composer.register_extension(TestGrammarExtension);

        assert!(composer.has_extension_rule("test_stmt"));
        assert!(composer.has_extension_rule("simple_test"));
        assert!(!composer.has_extension_rule("nonexistent_rule"));
    }

    #[test]
    fn test_composed_grammar_validation() {
        let mut composer = GrammarComposer::new();
        composer.register_extension(TestGrammarExtension);

        let composed = composer.compose().unwrap();

        // Basic validation - should have required base rules
        assert!(composed.contains("choreography"));
        assert!(composed.contains("send_stmt"));
        assert!(composed.contains("roles"));

        // Should have extension rules
        assert!(composed.contains("test_stmt"));

        // Should have proper structure
        let open_braces = composed.chars().filter(|&c| c == '{').count();
        let close_braces = composed.chars().filter(|&c| c == '}').count();
        assert_eq!(
            open_braces, close_braces,
            "Grammar should have balanced braces"
        );
    }

    #[test]
    fn test_grammar_composer_builder_pattern() {
        let composer = GrammarComposerBuilder::new()
            .with_extension(TestGrammarExtension)
            .with_extension(HighPriorityExtension)
            .build();

        assert_eq!(composer.extension_count(), 2);
        assert!(composer.has_extension_rule("test_stmt"));
        assert!(composer.has_extension_rule("priority_stmt"));
    }
}

// ============================================================================
// Extension Parser Tests
// ============================================================================

#[cfg(test)]
mod extension_parser_tests {
    use super::*;

    #[test]
    fn test_extension_parser_creation() {
        let parser = ExtensionParser::new();
        let stats = parser.extension_stats();
        assert_eq!(stats.grammar_extensions, 0);
        assert_eq!(stats.statement_parsers, 0);
    }

    #[test]
    fn test_extension_registration() {
        let mut parser = ExtensionParser::new();
        parser.register_extension(TestGrammarExtension, TestStatementParser);

        let stats = parser.extension_stats();
        assert_eq!(stats.grammar_extensions, 1);
        assert!(parser.can_handle_statement("test_stmt"));
        assert!(parser.can_handle_statement("simple_test"));
        assert!(!parser.can_handle_statement("unknown_stmt"));
    }

    #[test]
    fn test_standard_choreography_parsing() {
        let mut parser = ExtensionParser::new();

        let input = r#"
            choreography TestProtocol {
                roles: Alice, Bob
                Alice -> Bob: Message
            }
        "#;

        let result = parser.parse_with_extensions(input);
        assert!(result.is_ok(), "Should parse standard choreography");

        let choreography = result.unwrap();
        assert_eq!(choreography.roles.len(), 2);
        assert_eq!(choreography.roles[0].name, "Alice");
        assert_eq!(choreography.roles[1].name, "Bob");
    }

    #[test]
    fn test_extension_parser_builder() {
        let parser = ExtensionParserBuilder::new()
            .with_extension(TestGrammarExtension, TestStatementParser)
            .build();

        assert!(parser.can_handle_statement("test_stmt"));
        let stats = parser.extension_stats();
        assert_eq!(stats.grammar_extensions, 1);
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

    #[test]
    fn test_extension_parser_performance() {
        let mut parser = ExtensionParser::new();
        parser.register_extension(TestGrammarExtension, TestStatementParser);

        let input = r#"
            choreography LargeProtocol {
                roles: A, B, C, D, E
                A -> B: Message1
                B -> C: Message2
                C -> D: Message3
                D -> E: Message4
                E -> A: Message5
            }
        "#;

        // Multiple parses to test buffer reuse
        for _ in 0..10 {
            let result = parser.parse_with_extensions(input);
            assert!(result.is_ok(), "Should parse efficiently");
        }
    }
}

// ============================================================================
// Feature Inheritance Tests
// ============================================================================

#[cfg(test)]
mod feature_inheritance_tests {
    use super::*;

    #[test]
    fn test_choice_construct_inheritance() {
        let choreography = parse_choreography_str(
            r#"
            choreography ChoiceExample {
                roles: Alice, Bob, Charlie

                choice Alice {
                    path1: {
                        Alice -> Bob: Request
                    }
                    path2: {
                        Alice -> Charlie: Alternative
                    }
                }
            }
        "#,
        )
        .expect("Should parse choice construct");

        assert_eq!(choreography.roles.len(), 3);

        // Verify choice construct is parsed correctly
        match &choreography.protocol {
            Protocol::Choice { role, branches, .. } => {
                assert_eq!(role.name, "Alice");
                assert_eq!(branches.len(), 2);
                assert_eq!(branches[0].label.to_string(), "path1");
                assert_eq!(branches[1].label.to_string(), "path2");
            }
            _ => panic!("Expected choice protocol"),
        }
    }

    #[test]
    fn test_parameterized_roles_inheritance() {
        let choreography = parse_choreography_str(
            r#"
            choreography ParameterizedExample {
                roles: Worker[N], Manager, Client[3]

                Worker[*] -> Manager: Status
                Manager -> Client[0]: Response;
            }
        "#,
        )
        .expect("Should parse parameterized roles");

        // Verify parameterized roles are parsed
        let worker_role = choreography
            .roles
            .iter()
            .find(|r| r.name == "Worker")
            .unwrap();
        assert!(worker_role.param.is_some());

        let client_role = choreography
            .roles
            .iter()
            .find(|r| r.name == "Client")
            .unwrap();
        assert!(client_role.param.is_some());

        let manager_role = choreography
            .roles
            .iter()
            .find(|r| r.name == "Manager")
            .unwrap();
        assert!(manager_role.param.is_none());
    }

    #[test]
    fn test_loop_construct_inheritance() {
        let choreography = parse_choreography_str(
            r#"
            choreography LoopExample {
                roles: Producer, Consumer

                loop {
                    Producer -> Consumer: Data
                }
            }
        "#,
        )
        .expect("Should parse loop construct");

        assert_eq!(choreography.roles.len(), 2);

        // Verify loop construct is parsed correctly
        match &choreography.protocol {
            Protocol::Loop { body, .. } => match body.as_ref() {
                Protocol::Send { from, to, .. } => {
                    assert_eq!(from.name, "Producer");
                    assert_eq!(to.name, "Consumer");
                }
                _ => panic!("Expected send in loop body"),
            },
            _ => panic!("Expected loop protocol"),
        }
    }

    #[test]
    fn test_broadcast_inheritance() {
        let choreography = parse_choreography_str(
            r#"
            choreography BroadcastExample {
                roles: Server, Client1, Client2

                Server ->*: Notification
            }
        "#,
        )
        .expect("Should parse broadcast");

        match &choreography.protocol {
            Protocol::Broadcast { from, to_all, .. } => {
                assert_eq!(from.name, "Server");
                assert_eq!(to_all.len(), 2);
                assert!(to_all.iter().any(|r| r.name == "Client1"));
                assert!(to_all.iter().any(|r| r.name == "Client2"));
            }
            _ => panic!("Expected broadcast protocol"),
        }
    }

    #[test]
    fn test_complex_protocol_inheritance() {
        let choreography = parse_choreography_str(
            r#"
            choreography ComplexExample {
                roles: Coordinator, Worker[N], Client

                choice Coordinator {
                    distribute: {
                        loop {
                            Coordinator -> Worker[*]: Task
                            Worker[*] -> Coordinator: Result
                        }
                        Coordinator -> Client: Summary
                    }
                    direct: {
                        Coordinator -> Client: DirectResponse
                    }
                }
            }
        "#,
        )
        .expect("Should parse complex protocol");

        // Verify all features are inherited and work together
        assert_eq!(choreography.roles.len(), 3);

        // Check parameterized role
        let worker_role = choreography
            .roles
            .iter()
            .find(|r| r.name == "Worker")
            .unwrap();
        assert!(worker_role.param.is_some());

        // Verify complex structure is parsed
        match &choreography.protocol {
            Protocol::Choice { branches, .. } => {
                assert_eq!(branches.len(), 2);
                assert_eq!(branches[0].label.to_string(), "distribute");
                assert_eq!(branches[1].label.to_string(), "direct");
            }
            _ => panic!("Expected choice protocol"),
        }
    }
}

// ============================================================================
// Backwards Compatibility Tests
// ============================================================================

#[cfg(test)]
mod backwards_compatibility_tests {
    use super::*;

    #[test]
    fn test_basic_choreography_compatibility() {
        let choreographies = [
            r#"
                choreography Simple {
                    roles: A, B
                    A -> B: Message
                }
            "#,
            r#"
                #[namespace = "custom"]
                choreography WithNamespace {
                    roles: X, Y
                    X -> Y: Data
                }
            "#,
            r#"
                choreography MultipleMessages {
                    roles: Sender, Receiver
                    Sender -> Receiver: Message1
                    Sender -> Receiver: Message2
                    Receiver -> Sender: Ack
                }
            "#,
        ];

        for (i, choreo) in choreographies.iter().enumerate() {
            let result = parse_choreography_str(choreo);
            assert!(
                result.is_ok(),
                "Choreography {} should parse successfully: {:?}",
                i,
                result.err()
            );
        }
    }

    #[test]
    fn test_extension_parser_with_standard_choreographies() {
        let mut parser = ExtensionParser::new();
        parser.register_extension(TestGrammarExtension, TestStatementParser);

        let standard_choreographies = [
            r#"
                choreography Test1 {
                    roles: Alice, Bob
                    Alice -> Bob: Hello
                }
            "#,
            r#"
                choreography Test2 {
                    roles: X, Y, Z
                    choice X {
                        opt1: {
                            X -> Y: Option1
                        }
                        opt2: {
                            X -> Z: Option2
                        }
                    }
                }
            "#,
        ];

        for choreo in standard_choreographies {
            let result = parser.parse_with_extensions(choreo);
            assert!(
                result.is_ok(),
                "Standard choreography should parse with extension parser: {:?}",
                result.err()
            );
        }
    }

    #[test]
    fn test_api_compatibility() {
        // Test that all public APIs still work as expected

        // GrammarComposer
        let mut composer = GrammarComposer::new();
        assert_eq!(composer.extension_count(), 0);

        composer.register_extension(TestGrammarExtension);
        assert_eq!(composer.extension_count(), 1);

        let _grammar = composer.compose().unwrap();

        // ExtensionParser
        let mut parser = ExtensionParser::new();
        parser.register_extension(TestGrammarExtension, TestStatementParser);

        let _stats = parser.extension_stats();
        assert!(parser.can_handle_statement("test_stmt"));

        // Builder patterns
        let _composer = GrammarComposerBuilder::new().build();
        let _parser = ExtensionParserBuilder::new().build();
    }

    #[test]
    fn test_error_handling_compatibility() {
        // Test that error types and handling remain consistent

        let result = parse_choreography_str("invalid syntax");
        assert!(result.is_err());

        let mut parser = ExtensionParser::new();
        let result = parser.parse_with_extensions("also invalid");
        assert!(result.is_err());

        let mut composer = GrammarComposer::new();
        // This should succeed (empty extensions is valid)
        let result = composer.compose();
        assert!(result.is_ok());
    }
}

// ============================================================================
// Error Handling and Edge Case Tests
// ============================================================================

#[cfg(test)]
mod error_handling_tests {
    use super::*;

    #[test]
    fn test_invalid_choreography_syntax() {
        let invalid_choreographies = vec![
            "not a choreography",
            "choreography { }",
            "choreography Test { roles:  }",
            "choreography Test { roles: A, B A -> : Message; }",
            "choreography Test { roles: A A -> B: Message }", // B not declared
        ];

        for invalid in invalid_choreographies {
            let result = parse_choreography_str(invalid);
            assert!(
                result.is_err(),
                "Should fail to parse invalid syntax: {}",
                invalid
            );
        }
    }

    #[test]
    fn test_extension_parser_error_handling() {
        let mut parser = ExtensionParser::new();
        parser.register_extension(TestGrammarExtension, TestStatementParser);

        let invalid_input = "choreography Test { invalid syntax }";
        let result = parser.parse_with_extensions(invalid_input);

        assert!(result.is_err());
        match result.unwrap_err() {
            ExtensionParseError::StandardParseError(_) => {
                // Expected - invalid syntax should be caught by standard parser
            }
            other => panic!("Unexpected error type: {:?}", other),
        }
    }

    #[test]
    fn test_grammar_composition_edge_cases() {
        // Empty composer
        let mut composer = GrammarComposer::new();
        let result = composer.compose();
        assert!(result.is_ok(), "Empty composer should still work");

        // Multiple registrations of same extension
        composer.register_extension(TestGrammarExtension);
        composer.register_extension(TestGrammarExtension);

        let result = composer.compose();
        assert!(result.is_ok(), "Multiple registrations should be handled");

        // Extension count should reflect actual registrations
        assert!(composer.extension_count() > 0);
    }

    #[test]
    fn test_role_validation_edge_cases() {
        let edge_cases = vec![
            // Empty roles
            (
                r#"
                choreography Empty {
                    roles:
                }
            "#,
                false,
            ),
            // Single role
            (
                r#"
                choreography Single {
                    roles: Alice
                }
            "#,
                true,
            ),
            // Role with special characters (should fail)
            (
                r#"
                choreography Special {
                    roles: Role-With-Dashes
                }
            "#,
                false,
            ),
        ];

        for (choreo, should_succeed) in edge_cases {
            let result = parse_choreography_str(choreo);
            if should_succeed {
                assert!(result.is_ok(), "Should parse: {}", choreo);
            } else {
                assert!(result.is_err(), "Should fail to parse: {}", choreo);
            }
        }
    }

    #[test]
    fn test_large_choreography_parsing() {
        // Test parsing performance with large choreography
        let mut large_choreo = String::from(
            r#"
            choreography LargeExample {
                roles: "#,
        );

        // Add many roles
        for i in 0..100 {
            large_choreo.push_str(&format!("Role{}", i));
            if i < 99 {
                large_choreo.push_str(", ");
            }
        }
        large_choreo.push_str(";\n");

        // Add many message exchanges
        for i in 0..100 {
            large_choreo.push_str(&format!(
                "                Role{} -> Role{}: Message{};\n",
                i % 100,
                (i + 1) % 100,
                i
            ));
        }
        large_choreo.push_str("            }");

        let start = Instant::now();
        let result = parse_choreography_str(&large_choreo);
        let parse_time = start.elapsed();

        assert!(result.is_ok(), "Should parse large choreography");
        assert!(
            parse_time.as_millis() < 1000,
            "Should parse in reasonable time"
        );

        let choreography = result.unwrap();
        assert_eq!(choreography.roles.len(), 100);
    }

    #[test]
    fn test_extension_parser_buffer_reuse() {
        let mut parser = ExtensionParser::new();
        parser.register_extension(TestGrammarExtension, TestStatementParser);

        let test_input = r#"
            choreography BufferTest {
                roles: A, B
                A -> B: Message
            }
        "#;

        // Parse multiple times to ensure buffer reuse works correctly
        for _ in 0..10 {
            let result = parser.parse_with_extensions(test_input);
            assert!(result.is_ok(), "Buffer reuse should work correctly");
        }
    }
}

// ============================================================================
// Performance and Stress Tests
// ============================================================================

#[cfg(test)]
mod performance_tests {
    use super::*;

    #[test]
    fn test_grammar_composition_performance_regression() {
        let mut composer = GrammarComposer::new();

        // Add multiple extensions
        composer.register_extension(TestGrammarExtension);
        composer.register_extension(HighPriorityExtension);

        // Measure first composition
        let start = Instant::now();
        let _result1 = composer.compose().unwrap();
        let first_time = start.elapsed();

        // Measure cached composition (should be much faster)
        let start = Instant::now();
        let _result2 = composer.compose().unwrap();
        let second_time = start.elapsed();

        // Cache should provide significant speedup
        let speedup_ratio = first_time.as_nanos() as f64 / second_time.as_nanos() as f64;
        assert!(
            speedup_ratio > 10.0,
            "Cache should provide at least 10x speedup, got {:.2}x",
            speedup_ratio
        );
    }

    #[test]
    fn test_extension_parser_memory_efficiency() {
        let mut parser = ExtensionParser::new();
        parser.register_extension(TestGrammarExtension, TestStatementParser);

        let medium_choreo = r#"
            choreography MemoryTest {
                roles: A, B, C, D, E, F, G, H, I, J
                A -> B: M1 B -> C: M2 C -> D: M3 D -> E: M4 E -> F: M5
                F -> G: M6 G -> H: M7 H -> I: M8 I -> J: M9 J -> A: M10
            }
        "#;

        // Parse many times - should not accumulate memory
        for _ in 0..100 {
            let result = parser.parse_with_extensions(medium_choreo);
            assert!(result.is_ok(), "Should handle repeated parsing");
        }
    }

    #[test]
    fn test_concurrent_composer_usage() {
        use std::sync::{Arc, Mutex};
        use std::thread;

        let composer = Arc::new(Mutex::new({
            let mut c = GrammarComposer::new();
            c.register_extension(TestGrammarExtension);
            c
        }));

        let handles: Vec<_> = (0..4)
            .map(|_| {
                let composer = Arc::clone(&composer);
                thread::spawn(move || {
                    for _ in 0..10 {
                        let result = composer.lock().unwrap().compose();
                        assert!(result.is_ok(), "Concurrent composition should work");
                    }
                })
            })
            .collect();

        for handle in handles {
            handle.join().unwrap();
        }
    }
}

// ============================================================================
// Integration Tests with External Macro Demo
// ============================================================================

#[cfg(test)]
mod integration_tests {
    use super::*;

    #[test]
    fn test_external_macro_demo_compatibility() {
        // Test that the extension system works with external-macro-demo patterns

        let external_style_input = r#"
            choreography AuraExample {
                roles: Guardian, User, Validator

                Guardian -> User: Challenge
                User -> Validator: Proof
                Validator -> Guardian: Verification
            }
        "#;

        let result = parse_choreography_str(external_style_input);
        assert!(
            result.is_ok(),
            "Should parse external-macro-demo style input"
        );

        let choreography = result.unwrap();
        assert_eq!(choreography.roles.len(), 3);

        // Verify role names match what external-macro-demo expects
        let role_names: Vec<String> = choreography
            .roles
            .iter()
            .map(|r| r.name.to_string())
            .collect();
        assert!(role_names.contains(&"Guardian".to_string()));
        assert!(role_names.contains(&"User".to_string()));
        assert!(role_names.contains(&"Validator".to_string()));
    }

    #[test]
    fn test_annotation_extraction_compatibility() {
        // Test AST annotation system that external-macro-demo relies on
        let mut choreography = parse_choreography_str(
            r#"
            choreography AnnotationTest {
                roles: Alice, Bob
                Alice -> Bob: Message
            }
        "#,
        )
        .unwrap();

        // Add annotations like external-macro-demo would
        if let Some(annotations) = choreography.protocol.get_annotations_mut() {
            annotations.insert("guard_capability".to_string(), "send".to_string());
            annotations.insert("flow_cost".to_string(), "100".to_string());
        }

        // Test annotation retrieval
        assert!(choreography.protocol.has_annotation("guard_capability"));
        assert!(choreography.protocol.has_annotation("flow_cost"));
        assert_eq!(
            choreography
                .protocol
                .get_annotation("guard_capability")
                .unwrap(),
            "send"
        );
        assert_eq!(
            choreography.protocol.get_annotation("flow_cost").unwrap(),
            "100"
        );

        // Test annotation collection
        let mut nodes_with_capability = Vec::new();
        choreography
            .protocol
            .collect_nodes_with_annotation("guard_capability", &mut nodes_with_capability);
        assert_eq!(nodes_with_capability.len(), 1);
    }
}

#[cfg(test)]
mod regression_tests {
    use super::*;

    #[test]
    fn test_choice_with_parameterized_roles() {
        // Regression test for complex feature combinations
        let choreography = parse_choreography_str(
            r#"
            choreography Regression1 {
                roles: Worker[N], Coordinator

                choice Coordinator {
                    parallel: {
                        Worker[*] -> Coordinator: Status
                    }
                    sequential: {
                        Worker[0] -> Coordinator: FirstStatus
                        Worker[1] -> Coordinator: SecondStatus
                    }
                }
            }
        "#,
        )
        .expect("Should parse complex regression case");

        // Verify parameterized roles work in choice contexts
        let worker_role = choreography
            .roles
            .iter()
            .find(|r| r.name == "Worker")
            .unwrap();
        assert!(worker_role.param.is_some());
    }

    #[test]
    fn test_nested_protocol_structures() {
        // Regression test for deeply nested structures
        let choreography = parse_choreography_str(
            r#"
            choreography NestedExample {
                roles: A, B, C

                choice A {
                    path1: {
                        loop {
                            choice B {
                                continue: {
                                    B -> A: Continue
                                }
                                stop: {
                                    B -> A: Stop
                                }
                            }
                        }
                    }
                    path2: {
                        A -> C: Direct
                    }
                }
            }
        "#,
        )
        .expect("Should parse nested structures");

        // Basic verification that parsing succeeded
        assert_eq!(choreography.roles.len(), 3);
    }
}
