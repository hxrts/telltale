//! Protocol Module Template
//!
//! Generates the overall protocol module structure.

use super::Template;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// Template for generating a protocol module.
#[derive(Debug, Clone)]
pub struct ProtocolTemplate {
    /// Protocol name
    pub name: String,
    /// Role names
    pub roles: Vec<String>,
    /// Whether to include runtime traits
    pub include_runtime: bool,
}

impl ProtocolTemplate {
    /// Create a new protocol template.
    pub fn new(name: &str, roles: Vec<String>) -> Self {
        Self {
            name: name.to_string(),
            roles,
            include_runtime: true,
        }
    }

    /// Set whether to include runtime traits.
    pub fn with_runtime(mut self, include: bool) -> Self {
        self.include_runtime = include;
        self
    }
}

impl Template for ProtocolTemplate {
    fn generate(&self) -> TokenStream {
        let mod_name = format_ident!("{}", self.name.to_lowercase());
        let _protocol_name = format_ident!("{}", self.name);

        let role_variants: Vec<TokenStream> = self
            .roles
            .iter()
            .map(|r| {
                let ident = format_ident!("{}", r);
                quote! { #ident }
            })
            .collect();

        let runtime_traits = if self.include_runtime {
            quote! {
                /// Adapter trait for protocol communication.
                pub trait Adapter {
                    type Error;

                    /// Send a message to a role.
                    async fn send<M: Send>(&mut self, to: RoleId, msg: M) -> Result<(), Self::Error>;

                    /// Receive a message from a role.
                    async fn recv<M>(&mut self, from: RoleId) -> Result<M, Self::Error>;

                    /// Make an internal choice.
                    async fn choose(&mut self, to: RoleId, label: &str) -> Result<(), Self::Error>;

                    /// Offer external choices.
                    async fn offer(&mut self, from: RoleId) -> Result<String, Self::Error>;
                }

                /// Role identifier.
                #[derive(Debug, Clone, PartialEq, Eq, Hash)]
                pub struct RoleId(String);

                impl RoleId {
                    pub fn new(name: &str) -> Self {
                        Self(name.to_string())
                    }

                    pub fn name(&self) -> &str {
                        &self.0
                    }
                }
            }
        } else {
            quote! {}
        };

        quote! {
            /// Protocol: #protocol_name
            pub mod #mod_name {
                use serde::{Serialize, Deserialize};

                /// Roles participating in this protocol.
                #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
                pub enum Role {
                    #(#role_variants),*
                }

                impl Role {
                    /// Get the role name.
                    pub fn name(&self) -> &'static str {
                        match self {
                            #(Role::#role_variants => stringify!(#role_variants)),*
                        }
                    }
                }

                #runtime_traits

                // Message types go here
                pub mod messages {
                    use super::*;
                    // Generated message types
                }

                // Session types go here
                pub mod session {
                    use super::*;
                    // Generated session types
                }

                // Runners go here
                pub mod runners {
                    use super::*;
                    // Generated runner functions
                }
            }
        }
    }

    fn name(&self) -> &str {
        "Protocol Module"
    }

    fn description(&self) -> &str {
        "Generates a complete protocol module with roles, messages, session types, and runners"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_protocol_template() {
        let template = ProtocolTemplate::new("Echo", vec!["Client".into(), "Server".into()]);
        let code = template.generate();
        let code_str = code.to_string();

        assert!(code_str.contains("mod echo"));
        assert!(code_str.contains("enum Role"));
        assert!(code_str.contains("Client"));
        assert!(code_str.contains("Server"));
        assert!(code_str.contains("trait Adapter"));
    }

    #[test]
    fn test_protocol_without_runtime() {
        let template =
            ProtocolTemplate::new("Simple", vec!["A".into(), "B".into()]).with_runtime(false);
        let code = template.generate();
        let code_str = code.to_string();

        assert!(!code_str.contains("trait Adapter"));
    }
}
