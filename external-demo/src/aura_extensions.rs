//! Aura-specific choreography DSL extensions
//!
//! This module implements domain-specific extensions for Aura's choreographic programming,
//! including capability guards, flow cost management, journal facts, and audit logging.

use proc_macro2::TokenStream;
use quote::quote;
use std::any::{Any, TypeId};
use std::collections::HashMap;
use telltale_choreography::{
    ast::{LocalType, MessageType, Role},
    compiler::projection::ProjectionError,
    extensions::{
        CodegenContext, ExtensionValidationError, GrammarExtension, ParseContext, ParseError,
        ProjectionContext, ProtocolExtension, StatementParser,
    },
};

// ============================================================================
// Aura Grammar Extension
// ============================================================================

/// Grammar extension that adds support for Aura-specific annotations
#[derive(Debug)]
pub struct AuraGrammarExtension;

impl GrammarExtension for AuraGrammarExtension {
    fn grammar_rules(&self) -> &'static str {
        r#"
// Aura-specific statement types
aura_annotated_send = { role ~ aura_annotations ~ "->" ~ role ~ ":" ~ message_type ~ ";" }
aura_annotations = { "[" ~ aura_annotation ~ ("," ~ aura_annotation)* ~ "]" }
aura_annotation = { aura_annotation_name ~ "=" ~ aura_annotation_value }

// Annotation types
aura_annotation_name = { "guard_capability" | "flow_cost" | "journal_facts" | "journal_merge" | "audit_log" }
aura_annotation_value = { string_literal | number_literal | boolean_literal }

// Basic tokens
string_literal = { "\"" ~ (!"\"" ~ ANY)* ~ "\"" }
number_literal = @{ ASCII_DIGIT+ }
boolean_literal = { "true" | "false" }
message_type = { ident ~ ("(" ~ type_params? ~ ")")? }
type_params = { ident ~ ("," ~ ident)* }
role = { ident }
ident = @{ ASCII_ALPHA ~ (ASCII_ALPHANUMERIC | "_")* }
"#
    }

    fn statement_rules(&self) -> Vec<&'static str> {
        vec!["aura_annotated_send"]
    }

    fn priority(&self) -> u32 {
        200 // High priority to override default send statements
    }

    fn extension_id(&self) -> &'static str {
        "aura_annotations"
    }
}

// ============================================================================
// Aura Statement Parser
// ============================================================================

/// Parser for Aura-annotated statements
#[derive(Debug)]
pub struct AuraStatementParser;

impl StatementParser for AuraStatementParser {
    fn can_parse(&self, rule_name: &str) -> bool {
        rule_name == "aura_annotated_send"
    }

    fn supported_rules(&self) -> Vec<String> {
        vec!["aura_annotated_send".to_string()]
    }

    fn parse_statement(
        &self,
        rule_name: &str,
        content: &str,
        context: &ParseContext,
    ) -> Result<Box<dyn ProtocolExtension>, ParseError> {
        if rule_name != "aura_annotated_send" {
            return Err(ParseError::InvalidSyntax {
                details: format!("Unknown rule: {}", rule_name),
            });
        }

        // Parse the content to extract annotations and send information
        let parsed = self.parse_aura_send(content, context)?;
        Ok(Box::new(parsed))
    }
}

impl AuraStatementParser {
    fn parse_aura_send(
        &self,
        content: &str,
        _context: &ParseContext,
    ) -> Result<AuraAnnotatedSend, ParseError> {
        // This is a simplified parser - in a full implementation, we'd use pest
        // TODO: For now, we'll use regex-based parsing to extract the key components

        // Extract sender role
        let sender = self.extract_role_before_brackets(content)?;

        // Extract receiver role
        let receiver = self.extract_role_after_arrow(content)?;

        // Extract message type
        let message_type = self.extract_message_type(content)?;

        // Extract annotations
        let annotations = self.extract_annotations(content)?;

        Ok(AuraAnnotatedSend {
            sender,
            receiver,
            message_type,
            annotations,
        })
    }

    fn extract_role_before_brackets(&self, content: &str) -> Result<String, ParseError> {
        if let Some(bracket_pos) = content.find('[') {
            let before_bracket = content[..bracket_pos].trim();
            Ok(before_bracket.to_string())
        } else {
            Err(ParseError::InvalidSyntax {
                details: "No annotations found".to_string(),
            })
        }
    }

    fn extract_role_after_arrow(&self, content: &str) -> Result<String, ParseError> {
        if let Some(arrow_pos) = content.find("->") {
            let after_arrow = &content[arrow_pos + 2..];
            if let Some(colon_pos) = after_arrow.find(':') {
                let role = after_arrow[..colon_pos].trim();
                Ok(role.to_string())
            } else {
                Err(ParseError::InvalidSyntax {
                    details: "No message type found".to_string(),
                })
            }
        } else {
            Err(ParseError::InvalidSyntax {
                details: "No arrow found".to_string(),
            })
        }
    }

    fn extract_message_type(&self, content: &str) -> Result<String, ParseError> {
        if let Some(colon_pos) = content.find(':') {
            let after_colon = &content[colon_pos + 1..];
            if let Some(semi_pos) = after_colon.find(';') {
                let message_type = after_colon[..semi_pos].trim();
                Ok(message_type.to_string())
            } else {
                let message_type = after_colon.trim();
                Ok(message_type.to_string())
            }
        } else {
            Err(ParseError::InvalidSyntax {
                details: "No message type separator found".to_string(),
            })
        }
    }

    fn extract_annotations(&self, content: &str) -> Result<HashMap<String, String>, ParseError> {
        let mut annotations = HashMap::new();

        // Find the content between [ and ]
        if let Some(start) = content.find('[') {
            if let Some(end) = content.find(']') {
                let annotation_content = &content[start + 1..end];

                // Split by commas and parse each annotation
                for annotation in annotation_content.split(',') {
                    let annotation = annotation.trim();
                    if let Some(eq_pos) = annotation.find('=') {
                        let key = annotation[..eq_pos].trim().to_string();
                        let value = annotation[eq_pos + 1..].trim();

                        // Remove quotes if present
                        let value = if value.starts_with('"') && value.ends_with('"') {
                            value[1..value.len() - 1].to_string()
                        } else {
                            value.to_string()
                        };

                        annotations.insert(key, value);
                    }
                }
            }
        }

        Ok(annotations)
    }
}

// ============================================================================
// Aura Protocol Extension
// ============================================================================

/// Protocol extension representing an Aura-annotated send statement
#[derive(Debug, Clone)]
pub struct AuraAnnotatedSend {
    pub sender: String,
    pub receiver: String,
    pub message_type: String,
    pub annotations: HashMap<String, String>,
}

#[allow(clippy::cmp_owned)]
impl ProtocolExtension for AuraAnnotatedSend {
    fn type_name(&self) -> &'static str {
        "AuraAnnotatedSend"
    }

    fn mentions_role(&self, role: &Role) -> bool {
        role.name().to_string() == self.sender || role.name().to_string() == self.receiver
    }

    fn validate(&self, roles: &[Role]) -> Result<(), ExtensionValidationError> {
        // Check that sender and receiver roles exist
        let role_names: Vec<String> = roles.iter().map(|r| r.name.to_string()).collect();

        if !role_names.contains(&self.sender) {
            return Err(ExtensionValidationError::UndeclaredRole {
                role: self.sender.clone(),
            });
        }

        if !role_names.contains(&self.receiver) {
            return Err(ExtensionValidationError::UndeclaredRole {
                role: self.receiver.clone(),
            });
        }

        // Validate annotation values
        if let Some(flow_cost) = self.annotations.get("flow_cost") {
            if flow_cost.parse::<u64>().is_err() {
                return Err(ExtensionValidationError::ExtensionFailed {
                    message: format!("Invalid flow_cost value: {}", flow_cost),
                });
            }
        }

        Ok(())
    }

    fn project(
        &self,
        role: &Role,
        _context: &ProjectionContext,
    ) -> Result<LocalType, ProjectionError> {
        // Helper to create MessageType from string
        let create_message_type = |message_name: &str| MessageType {
            name: syn::Ident::new(message_name, proc_macro2::Span::call_site()),
            type_annotation: None,
            payload: None,
        };

        // Check if this role is the sender
        if role.name().to_string() == self.sender {
            // Sender role: Create annotated Send with message type
            Ok(LocalType::Send {
                to: Role::new(syn::Ident::new(
                    &self.receiver,
                    proc_macro2::Span::call_site(),
                )),
                message: create_message_type(&self.message_type),
                continuation: Box::new(LocalType::End),
            })
        }
        // Check if this role is the receiver
        else if role.name().to_string() == self.receiver {
            // Receiver role: Create annotated Receive
            Ok(LocalType::Receive {
                from: Role::new(syn::Ident::new(
                    &self.sender,
                    proc_macro2::Span::call_site(),
                )),
                message: create_message_type(&self.message_type),
                continuation: Box::new(LocalType::End),
            })
        }
        // Uninvolved role: return End (no continuation to project)
        else {
            Ok(LocalType::End)
        }
    }

    fn generate_code(&self, _context: &CodegenContext) -> TokenStream {
        // Generate code that includes the Aura effects
        let mut effects = Vec::new();

        // Add guard capability if present
        if let Some(capability) = self.annotations.get("guard_capability") {
            let sender_role = &self.sender;
            effects.push(quote! {
                .ext(ValidateCapability {
                    capability: #capability.to_string(),
                    role: AuraRole::#sender_role
                })
            });
        }

        // Add flow cost if present
        if let Some(cost_str) = self.annotations.get("flow_cost") {
            if let Ok(cost) = cost_str.parse::<u64>() {
                let sender_role = &self.sender;
                effects.push(quote! {
                    .ext(ChargeFlowCost {
                        cost: #cost,
                        role: AuraRole::#sender_role
                    })
                });
            }
        }

        // Add journal facts if present
        if let Some(facts) = self.annotations.get("journal_facts") {
            let sender_role = &self.sender;
            effects.push(quote! {
                .ext(RecordJournalFacts {
                    facts: #facts.to_string(),
                    role: AuraRole::#sender_role
                })
            });
        }

        // Add journal merge if present
        if self.annotations.contains_key("journal_merge") {
            let sender_role = &self.sender;
            effects.push(quote! {
                .ext(TriggerJournalMerge {
                    role: AuraRole::#sender_role
                })
            });
        }

        // Add audit log if present
        if let Some(audit_msg) = self.annotations.get("audit_log") {
            effects.push(quote! {
                .ext(AuditLog {
                    action: #audit_msg.to_string(),
                    metadata: std::collections::HashMap::new()
                })
            });
        }

        // Add the actual send operation
        let receiver = &self.receiver;
        let message = &self.message_type;
        effects.push(quote! {
            .send(AuraRole::#receiver, #message.to_string())
        });

        // Combine all effects
        quote! {
            #(#effects)*
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

// ============================================================================
// Public API
// ============================================================================

/// Register all Aura extensions with an extension registry
pub fn register_aura_extensions(
    registry: &mut telltale_choreography::extensions::ExtensionRegistry,
) {
    let _ = registry.register_grammar(AuraGrammarExtension);
    registry.register_parser(AuraStatementParser, "aura_statement_parser".to_string());
}

/// Create an extension registry with Aura extensions pre-registered
pub fn create_aura_extension_registry() -> telltale_choreography::extensions::ExtensionRegistry {
    let mut registry = telltale_choreography::extensions::ExtensionRegistry::new();
    register_aura_extensions(&mut registry);
    registry
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_aura_grammar_extension() {
        let ext = AuraGrammarExtension;
        assert_eq!(ext.extension_id(), "aura_annotations");
        assert!(ext.statement_rules().contains(&"aura_annotated_send"));
        assert_eq!(ext.priority(), 200);
    }

    #[test]
    fn test_annotation_parsing() {
        let parser = AuraStatementParser;
        let content =
            r#"Alice[guard_capability = "send_message", flow_cost = 100] -> Bob: Message;"#;

        let annotations = parser.extract_annotations(content).unwrap();
        assert_eq!(
            annotations.get("guard_capability"),
            Some(&"send_message".to_string())
        );
        assert_eq!(annotations.get("flow_cost"), Some(&"100".to_string()));
    }

    #[test]
    fn test_role_extraction() {
        let parser = AuraStatementParser;
        let content = r#"Alice[guard_capability = "send"] -> Bob: Message;"#;

        assert_eq!(
            parser.extract_role_before_brackets(content).unwrap(),
            "Alice"
        );
        assert_eq!(parser.extract_role_after_arrow(content).unwrap(), "Bob");
        assert_eq!(parser.extract_message_type(content).unwrap(), "Message");
    }
}
