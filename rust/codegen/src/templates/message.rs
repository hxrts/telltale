//! Message Type Template
//!
//! Generates message struct and enum definitions.

use super::Template;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// Template for generating a message type.
#[derive(Debug, Clone)]
pub struct MessageTemplate {
    /// Message name
    pub name: String,
    /// Payload type (as string)
    pub payload_type: Option<String>,
    /// Whether to derive Serialize/Deserialize
    pub derive_serde: bool,
}

impl MessageTemplate {
    /// Create a new message template.
    pub fn new(name: &str) -> Self {
        Self {
            name: name.to_string(),
            payload_type: None,
            derive_serde: true,
        }
    }

    /// Set the payload type.
    pub fn with_payload(mut self, payload: &str) -> Self {
        self.payload_type = Some(payload.to_string());
        self
    }

    /// Set whether to derive serde traits.
    pub fn with_serde(mut self, derive: bool) -> Self {
        self.derive_serde = derive;
        self
    }
}

impl Template for MessageTemplate {
    fn generate(&self) -> TokenStream {
        let msg_name = format_ident!("{}", self.name);

        let serde_derive = if self.derive_serde {
            quote! { #[derive(Debug, Clone, Serialize, Deserialize)] }
        } else {
            quote! { #[derive(Debug, Clone)] }
        };

        if let Some(ref payload) = self.payload_type {
            let payload_ident = format_ident!("{}", payload);
            quote! {
                #serde_derive
                pub struct #msg_name(pub #payload_ident);

                impl #msg_name {
                    pub fn new(payload: #payload_ident) -> Self {
                        Self(payload)
                    }

                    pub fn payload(&self) -> &#payload_ident {
                        &self.0
                    }

                    pub fn into_payload(self) -> #payload_ident {
                        self.0
                    }
                }
            }
        } else {
            quote! {
                #serde_derive
                pub struct #msg_name;

                impl #msg_name {
                    pub fn new() -> Self {
                        Self
                    }
                }

                impl Default for #msg_name {
                    fn default() -> Self {
                        Self::new()
                    }
                }
            }
        }
    }

    fn name(&self) -> &str {
        "Message Type"
    }

    fn description(&self) -> &str {
        "Generates a message struct with optional payload"
    }
}

/// Template for generating a message enum (for choices).
#[derive(Debug, Clone)]
pub struct MessageEnumTemplate {
    /// Enum name
    pub name: String,
    /// Variants with optional payloads
    pub variants: Vec<(String, Option<String>)>,
    /// Whether to derive Serialize/Deserialize
    pub derive_serde: bool,
}

impl MessageEnumTemplate {
    /// Create a new message enum template.
    pub fn new(name: &str, variants: Vec<(String, Option<String>)>) -> Self {
        Self {
            name: name.to_string(),
            variants,
            derive_serde: true,
        }
    }
}

impl Template for MessageEnumTemplate {
    fn generate(&self) -> TokenStream {
        let enum_name = format_ident!("{}", self.name);

        let serde_derive = if self.derive_serde {
            quote! { #[derive(Debug, Clone, Serialize, Deserialize)] }
        } else {
            quote! { #[derive(Debug, Clone)] }
        };

        let variants: Vec<TokenStream> = self
            .variants
            .iter()
            .map(|(name, payload)| {
                let variant_name = format_ident!("{}", name);
                if let Some(p) = payload {
                    let payload_ident = format_ident!("{}", p);
                    quote! { #variant_name(#payload_ident) }
                } else {
                    quote! { #variant_name }
                }
            })
            .collect();

        quote! {
            #serde_derive
            pub enum #enum_name {
                #(#variants),*
            }
        }
    }

    fn name(&self) -> &str {
        "Message Enum"
    }

    fn description(&self) -> &str {
        "Generates a message enum for protocol choices"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_message_template_simple() {
        let template = MessageTemplate::new("Ping");
        let code = template.generate();
        let code_str = code.to_string();

        assert!(code_str.contains("struct Ping"));
        assert!(code_str.contains("Serialize"));
    }

    #[test]
    fn test_message_template_with_payload() {
        let template = MessageTemplate::new("Request").with_payload("String");
        let code = template.generate();
        let code_str = code.to_string();

        assert!(code_str.contains("struct Request"));
        assert!(code_str.contains("String"));
        assert!(code_str.contains("payload"));
    }

    #[test]
    fn test_message_enum() {
        let variants = vec![("Add".into(), Some("i32".into())), ("Quit".into(), None)];
        let template = MessageEnumTemplate::new("Operation", variants);
        let code = template.generate();
        let code_str = code.to_string();

        assert!(code_str.contains("enum Operation"));
        assert!(code_str.contains("Add"));
        assert!(code_str.contains("Quit"));
    }
}
