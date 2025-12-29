//! Example timeout extension for choreographic protocols
//!
//! This demonstrates how to create a complete extension that adds timeout
//! functionality to choreographic protocols.

use super::*;
use crate::ast::{LocalType, Role};
use crate::compiler::projection::ProjectionError;
use std::any::{Any, TypeId};
use std::time::Duration;

/// Grammar extension that adds timeout syntax
#[derive(Debug)]
pub struct TimeoutGrammarExtension;

impl GrammarExtension for TimeoutGrammarExtension {
    fn grammar_rules(&self) -> &'static str {
        r#"
timeout_stmt = { "timeout" ~ timeout_duration ~ timeout_roles ~ "{" ~ protocol_body ~ "}" }
timeout_duration = { integer ~ time_unit? }
time_unit = { "ms" | "s" | "m" | "h" }
timeout_roles = { "(" ~ role_list ~ ")" | role_ref }
"#
    }

    fn statement_rules(&self) -> Vec<&'static str> {
        vec!["timeout_stmt"]
    }

    fn priority(&self) -> u32 {
        200 // Higher than default to take precedence
    }

    fn extension_id(&self) -> &'static str {
        "timeout"
    }
}

/// Statement parser for timeout constructs
#[derive(Debug)]
pub struct TimeoutStatementParser;

impl StatementParser for TimeoutStatementParser {
    fn can_parse(&self, rule_name: &str) -> bool {
        rule_name == "timeout_stmt"
    }

    fn supported_rules(&self) -> Vec<String> {
        vec!["timeout_stmt".to_string()]
    }

    fn parse_statement(
        &self,
        rule_name: &str,
        _content: &str,
        context: &ParseContext,
    ) -> Result<Box<dyn ProtocolExtension>, ParseError> {
        if rule_name != "timeout_stmt" {
            return Err(ParseError::InvalidSyntax {
                details: format!("Expected timeout_stmt, got {}", rule_name),
            });
        }

        // Parse the timeout statement
        // This is a simplified parser - in practice, you'd use the Pest parse tree
        let timeout_protocol = self.parse_timeout_content(_content, context)?;
        Ok(Box::new(timeout_protocol))
    }
}

impl TimeoutStatementParser {
    fn parse_timeout_content(
        &self,
        content: &str,
        context: &ParseContext,
    ) -> Result<TimeoutProtocol, ParseError> {
        // Simplified parsing - extract duration and roles
        // In a real implementation, this would use the Pest parse tree

        let duration_ms = self.extract_duration(content)?;
        let roles = self.extract_roles(content, context)?;

        // For simplicity, assume the body is just an End protocol
        // In practice, you'd recursively parse the protocol body

        Ok(TimeoutProtocol {
            duration: Duration::from_millis(duration_ms),
            role_names: roles.iter().map(|r| r.name.to_string()).collect(),
            body_repr: "End".to_string(),
        })
    }

    fn extract_duration(&self, content: &str) -> Result<u64, ParseError> {
        // Simplified duration extraction
        // Look for numeric patterns
        let duration_str = content
            .split_whitespace()
            .find(|s| s.chars().all(|c| c.is_ascii_digit()))
            .ok_or_else(|| ParseError::InvalidSyntax {
                details: "Could not find timeout duration".to_string(),
            })?;

        duration_str.parse().map_err(|_| ParseError::InvalidSyntax {
            details: "Invalid timeout duration format".to_string(),
        })
    }

    fn extract_roles(
        &self,
        _content: &str,
        context: &ParseContext,
    ) -> Result<Vec<Role>, ParseError> {
        // Simplified role extraction
        // In practice, this would properly parse role references

        // For now, just return all declared roles
        Ok(context.declared_roles.to_vec())
    }
}

/// Protocol extension implementation for timeouts
#[derive(Debug, Clone)]
pub struct TimeoutProtocol {
    pub duration: Duration,
    pub role_names: Vec<String>, // Use simple strings instead of Role structs
    // Note: Storing the full Protocol AST would require fixing Send + Sync issues
    // For this example, we store a simplified representation
    pub body_repr: String,
}

impl ProtocolExtension for TimeoutProtocol {
    fn type_name(&self) -> &'static str {
        "TimeoutProtocol"
    }

    fn mentions_role(&self, role: &Role) -> bool {
        self.role_names
            .iter()
            .any(|name| name == &role.name.to_string())
    }

    fn validate(&self, all_roles: &[Role]) -> Result<(), ExtensionValidationError> {
        // Validate that all mentioned roles are declared
        for role_name in &self.role_names {
            if !all_roles.iter().any(|r| &r.name.to_string() == role_name) {
                return Err(ExtensionValidationError::UndeclaredRole {
                    role: role_name.clone(),
                });
            }
        }

        // Validate duration is reasonable
        if self.duration.is_zero() {
            return Err(ExtensionValidationError::InvalidStructure {
                reason: "Timeout duration cannot be zero".to_string(),
            });
        }

        if self.duration > Duration::from_secs(3600) {
            return Err(ExtensionValidationError::InvalidStructure {
                reason: "Timeout duration too long (max 1 hour)".to_string(),
            });
        }

        Ok(())
    }

    fn project(
        &self,
        role: &Role,
        _context: &ProjectionContext,
    ) -> Result<LocalType, ProjectionError> {
        if self
            .role_names
            .iter()
            .any(|name| name == &role.name.to_string())
        {
            // This role participates in the timeout
            // For now, just return a placeholder. In a real implementation,
            // we would need to create a new projection context to project the body
            Ok(LocalType::Timeout {
                duration: self.duration,
                body: Box::new(LocalType::End), // Placeholder
            })
        } else {
            // This role doesn't participate in timeout, return End
            Ok(LocalType::End)
        }
    }

    fn generate_code(&self, _context: &CodegenContext) -> proc_macro2::TokenStream {
        let duration_ms = self.duration.as_millis() as u64;
        let _role_names = &self.role_names;

        quote::quote! {
            // Generate timeout wrapper code
            .with_timeout(
                Duration::from_millis(#duration_ms),
                // Timeout applies to these roles: #(#role_names),*
            )
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

/// Convenience function to register the timeout extension
pub fn register_timeout_extension(registry: &mut ExtensionRegistry) {
    let _ = registry.register_grammar(TimeoutGrammarExtension);
    registry.register_parser(TimeoutStatementParser, "timeout".to_string());
}

/// Extend LocalType to support timeout
impl LocalType {
    pub fn timeout(duration: Duration, body: LocalType) -> Self {
        Self::Timeout {
            duration,
            body: Box::new(body),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_timeout_grammar_extension() {
        let ext = TimeoutGrammarExtension;
        assert_eq!(ext.extension_id(), "timeout");
        assert!(ext.statement_rules().contains(&"timeout_stmt"));
        assert!(ext.grammar_rules().contains("timeout_stmt"));
    }

    #[test]
    fn test_timeout_statement_parser() {
        let parser = TimeoutStatementParser;
        assert!(parser.can_parse("timeout_stmt"));
        assert!(!parser.can_parse("unknown_stmt"));
    }

    #[test]
    fn test_timeout_protocol() {
        let timeout_protocol = TimeoutProtocol {
            duration: Duration::from_millis(5000),
            role_names: vec!["Alice".to_string()],
            body_repr: "End".to_string(),
        };

        assert_eq!(timeout_protocol.type_name(), "TimeoutProtocol");

        use proc_macro2::Span;
        let alice = Role::new(proc_macro2::Ident::new("Alice", Span::call_site()));
        let bob = Role::new(proc_macro2::Ident::new("Bob", Span::call_site()));

        assert!(timeout_protocol.mentions_role(&alice));
        assert!(!timeout_protocol.mentions_role(&bob));
    }

    #[test]
    fn test_timeout_validation() {
        use proc_macro2::Span;
        let roles = vec![Role::new(proc_macro2::Ident::new(
            "Alice",
            Span::call_site(),
        ))];

        let valid_timeout = TimeoutProtocol {
            duration: Duration::from_millis(5000),
            role_names: roles.iter().map(|r| r.name.to_string()).collect(),
            body_repr: "End".to_string(),
        };

        assert!(valid_timeout.validate(&roles).is_ok());

        // Test invalid duration
        let invalid_timeout = TimeoutProtocol {
            duration: Duration::ZERO,
            role_names: roles.iter().map(|r| r.name.to_string()).collect(),
            body_repr: "End".to_string(),
        };

        assert!(invalid_timeout.validate(&roles).is_err());
    }

    #[test]
    fn test_extension_registration() {
        let mut registry = ExtensionRegistry::new();
        register_timeout_extension(&mut registry);

        assert!(registry.can_handle("timeout_stmt"));
    }
}
