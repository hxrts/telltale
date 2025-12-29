//! Example demonstrating the DSL extension system
//!
//! This example shows how to create and use extensions to the choreographic DSL,
//! including custom grammar rules, parsers, and protocol behaviors.

use rumpsteak_aura_choreography::{
    ast::LocalType, compiler::projection::ProjectionError, CodegenContext, ExtensionParserBuilder,
    ExtensionRegistry, ExtensionValidationError, GrammarExtension, ParseContext, ParseError,
    ProjectionContext, ProtocolExtension, Role, StatementParser,
};
use std::any::{Any, TypeId};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("Rumpsteak-Aura DSL Extension System Demo");

    // Demo 1: Register timeout extension
    demo_timeout_extension()?;

    // Demo 2: Create custom annotation extension
    demo_annotation_extension()?;

    // Demo 3: Extension composition
    demo_extension_composition()?;

    println!("All extension demos completed successfully!");
    Ok(())
}

fn demo_timeout_extension() -> Result<(), Box<dyn std::error::Error>> {
    println!("\nDemo 1: Timeout Extension");

    // Register the built-in timeout extension
    let mut registry = ExtensionRegistry::new();
    rumpsteak_aura_choreography::extensions::timeout::register_timeout_extension(&mut registry);

    println!("Timeout extension registered");
    println!(
        "Can handle 'timeout_stmt': {}",
        registry.can_handle("timeout_stmt")
    );

    Ok(())
}

fn demo_annotation_extension() -> Result<(), Box<dyn std::error::Error>> {
    println!("\nDemo 2: Custom Annotation Extension");

    // Create a custom extension for priority annotations
    let parser = ExtensionParserBuilder::new()
        .with_extension(PriorityGrammarExtension, PriorityStatementParser)
        .build();

    // Test parsing a choreography with priority annotations
    let _choreography_with_priority = r#"
        choreography PriorityExample {
            roles: Client, Server;

            Client -> Server: Request;
            priority high Server -> Client: UrgentResponse;
        }
    "#;

    // This would normally parse if we had full integration
    // For now, we just show that the extension is registered
    println!("Priority extension registered");
    println!(
        "Can handle 'priority_stmt': {}",
        parser.can_handle_statement("priority_stmt")
    );

    Ok(())
}

fn demo_extension_composition() -> Result<(), Box<dyn std::error::Error>> {
    println!("\nDemo 3: Extension Composition");

    // Create a parser with multiple extensions
    let mut parser = ExtensionParserBuilder::new()
        .with_extension(PriorityGrammarExtension, PriorityStatementParser)
        .with_extension(LoggingGrammarExtension, LoggingStatementParser)
        .build();

    let stats = parser.extension_stats();
    println!("Registered {} grammar extensions", stats.grammar_extensions);

    // Show the composed grammar
    match parser.get_composed_grammar() {
        Ok(grammar) => {
            println!(
                "Successfully composed grammar with {} lines",
                grammar.lines().count()
            );

            // Show a sample of the composed grammar
            println!("Grammar sample (first 10 lines):");
            for (i, line) in grammar.lines().take(10).enumerate() {
                println!("   {}: {}", i + 1, line);
            }
            if grammar.lines().count() > 10 {
                println!("   ... ({} more lines)", grammar.lines().count() - 10);
            }
        }
        Err(e) => {
            println!("Grammar composition failed: {}", e);
        }
    }

    Ok(())
}

// === Custom Extension Implementations ===

/// Grammar extension for priority annotations
#[derive(Debug)]
struct PriorityGrammarExtension;

impl GrammarExtension for PriorityGrammarExtension {
    fn grammar_rules(&self) -> &'static str {
        r#"
priority_stmt = { "priority" ~ priority_level ~ send_stmt }
priority_level = { "high" | "medium" | "low" | "urgent" }
"#
    }

    fn statement_rules(&self) -> Vec<&'static str> {
        vec!["priority_stmt"]
    }

    fn priority(&self) -> u32 {
        150 // Medium priority
    }

    fn extension_id(&self) -> &'static str {
        "priority"
    }
}

/// Statement parser for priority annotations
#[derive(Debug)]
struct PriorityStatementParser;

impl StatementParser for PriorityStatementParser {
    fn can_parse(&self, rule_name: &str) -> bool {
        rule_name == "priority_stmt"
    }

    fn supported_rules(&self) -> Vec<String> {
        vec!["priority_stmt".to_string()]
    }

    fn parse_statement(
        &self,
        _rule_name: &str,
        content: &str,
        _context: &ParseContext,
    ) -> Result<Box<dyn ProtocolExtension>, ParseError> {
        let priority = self.extract_priority(content)?;

        Ok(Box::new(PriorityProtocol {
            level: priority,
            // In a real implementation, we'd parse the nested send statement
        }))
    }
}

impl PriorityStatementParser {
    fn extract_priority(&self, content: &str) -> Result<PriorityLevel, ParseError> {
        if content.contains("urgent") {
            Ok(PriorityLevel::Urgent)
        } else if content.contains("high") {
            Ok(PriorityLevel::High)
        } else if content.contains("medium") {
            Ok(PriorityLevel::Medium)
        } else if content.contains("low") {
            Ok(PriorityLevel::Low)
        } else {
            Err(ParseError::InvalidSyntax {
                details: "Unknown priority level".to_string(),
            })
        }
    }
}

/// Priority levels
#[derive(Debug, Clone, Copy)]
enum PriorityLevel {
    Urgent,
    High,
    Medium,
    Low,
}

/// Protocol extension for priority handling
#[derive(Debug, Clone)]
struct PriorityProtocol {
    level: PriorityLevel,
}

impl ProtocolExtension for PriorityProtocol {
    fn type_name(&self) -> &'static str {
        "PriorityProtocol"
    }

    fn mentions_role(&self, _role: &Role) -> bool {
        // Priority is meta-information, doesn't mention specific roles
        false
    }

    fn validate(&self, _roles: &[Role]) -> Result<(), ExtensionValidationError> {
        // Priority annotations are always valid
        Ok(())
    }

    fn project(
        &self,
        _role: &Role,
        _context: &ProjectionContext,
    ) -> Result<LocalType, ProjectionError> {
        // Priority doesn't affect projection, just adds metadata
        Ok(LocalType::End)
    }

    fn generate_code(&self, _context: &CodegenContext) -> proc_macro2::TokenStream {
        let priority_str = format!("{:?}", self.level);
        quote::quote! {
            .with_priority(#priority_str)
        }
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }
}

// === Logging Extension ===

#[derive(Debug)]
struct LoggingGrammarExtension;

impl GrammarExtension for LoggingGrammarExtension {
    fn grammar_rules(&self) -> &'static str {
        r#"
log_stmt = { "log" ~ log_level ~ string_literal }
log_level = { "debug" | "info" | "warn" | "error" }
string_literal = { "\"" ~ (!"\"" ~ ANY)* ~ "\"" }
"#
    }

    fn statement_rules(&self) -> Vec<&'static str> {
        vec!["log_stmt"]
    }

    fn extension_id(&self) -> &'static str {
        "logging"
    }
}

#[derive(Debug)]
struct LoggingStatementParser;

impl StatementParser for LoggingStatementParser {
    fn can_parse(&self, rule_name: &str) -> bool {
        rule_name == "log_stmt"
    }

    fn supported_rules(&self) -> Vec<String> {
        vec!["log_stmt".to_string()]
    }

    fn parse_statement(
        &self,
        _rule_name: &str,
        _content: &str,
        _context: &ParseContext,
    ) -> Result<Box<dyn ProtocolExtension>, ParseError> {
        Ok(Box::new(LoggingProtocol {
            message: "Example log message".to_string(),
        }))
    }
}

#[derive(Debug, Clone)]
struct LoggingProtocol {
    message: String,
}

impl ProtocolExtension for LoggingProtocol {
    fn type_name(&self) -> &'static str {
        "LoggingProtocol"
    }

    fn mentions_role(&self, _role: &Role) -> bool {
        false
    }

    fn validate(&self, _roles: &[Role]) -> Result<(), ExtensionValidationError> {
        Ok(())
    }

    fn project(
        &self,
        _role: &Role,
        _context: &ProjectionContext,
    ) -> Result<LocalType, ProjectionError> {
        Ok(LocalType::End)
    }

    fn generate_code(&self, _context: &CodegenContext) -> proc_macro2::TokenStream {
        let msg = &self.message;
        quote::quote! {
            .with_logging(#msg)
        }
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }

    fn type_id(&self) -> TypeId {
        TypeId::of::<Self>()
    }
}

/// Helper macro for creating simple extensions
#[allow(unused_macros)]
macro_rules! simple_extension {
    ($name:ident, $rule:literal, $code:expr) => {
        #[derive(Debug)]
        struct $name;

        impl GrammarExtension for $name {
            fn grammar_rules(&self) -> &'static str {
                $rule
            }

            fn statement_rules(&self) -> Vec<&'static str> {
                vec![stringify!($name)]
            }

            fn extension_id(&self) -> &'static str {
                stringify!($name)
            }
        }
    };
}

// Example usage of the macro (commented to avoid unused code warning)
// simple_extension!(
//     MetricsExtension,
//     "metrics_stmt = { \"metrics\" ~ ident }",
//     quote::quote! { .with_metrics() }
// );

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_priority_extension() {
        let ext = PriorityGrammarExtension;
        assert_eq!(ext.extension_id(), "priority");
        assert!(ext.statement_rules().contains(&"priority_stmt"));
    }

    #[test]
    fn test_logging_extension() {
        let ext = LoggingGrammarExtension;
        assert_eq!(ext.extension_id(), "logging");
        assert!(ext.statement_rules().contains(&"log_stmt"));
    }

    #[test]
    fn test_extension_parser_builder() {
        let parser = ExtensionParserBuilder::new()
            .with_extension(PriorityGrammarExtension, PriorityStatementParser)
            .with_extension(LoggingGrammarExtension, LoggingStatementParser)
            .build();

        assert!(parser.can_handle_statement("priority_stmt"));
        assert!(parser.can_handle_statement("log_stmt"));
        assert!(!parser.can_handle_statement("unknown_stmt"));
    }
}
