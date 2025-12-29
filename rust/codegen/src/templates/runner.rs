//! Runner Boilerplate Template
//!
//! Generates runner function boilerplate for protocol execution.

use super::Template;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// Template for generating a runner function.
#[derive(Debug, Clone)]
pub struct RunnerTemplate {
    /// Protocol name
    pub protocol_name: String,
    /// Role name
    pub role_name: String,
    /// Whether the role is indexed
    pub is_indexed: bool,
}

impl RunnerTemplate {
    /// Create a new runner template.
    pub fn new(protocol_name: &str, role_name: &str) -> Self {
        Self {
            protocol_name: protocol_name.to_string(),
            role_name: role_name.to_string(),
            is_indexed: false,
        }
    }

    /// Set whether the role is indexed.
    pub fn with_index(mut self, indexed: bool) -> Self {
        self.is_indexed = indexed;
        self
    }
}

impl Template for RunnerTemplate {
    fn generate(&self) -> TokenStream {
        let fn_name = format_ident!("run_{}", self.role_name.to_lowercase());
        let output_type = format_ident!("{}Output", self.role_name);
        let protocol_str = &self.protocol_name;
        let role_str = &self.role_name;

        let (signature, ctx_creation) = if self.is_indexed {
            (
                quote! {
                    pub async fn #fn_name<A: Adapter>(
                        adapter: &mut A,
                        index: u32,
                    ) -> Result<#output_type, A::Error>
                },
                quote! {
                    let _ctx = ProtocolContext::indexed(#protocol_str, #role_str, index);
                },
            )
        } else {
            (
                quote! {
                    pub async fn #fn_name<A: Adapter>(
                        adapter: &mut A,
                    ) -> Result<#output_type, A::Error>
                },
                quote! {
                    let _ctx = ProtocolContext::new(#protocol_str, #role_str);
                },
            )
        };

        quote! {
            /// Output type for the role.
            #[derive(Debug, Default)]
            pub struct #output_type {
                // Fields populated during execution
            }

            #signature {
                #ctx_creation

                // Protocol execution logic goes here
                // TODO: Generate from session type

                Ok(#output_type::default())
            }
        }
    }

    fn name(&self) -> &str {
        "Runner Function"
    }

    fn description(&self) -> &str {
        "Generates a runner function boilerplate for a protocol role"
    }
}

/// Template for generating an execute_as dispatch function.
#[derive(Debug, Clone)]
pub struct ExecuteAsTemplate {
    /// Protocol name
    pub protocol_name: String,
    /// Role names
    pub roles: Vec<String>,
}

impl ExecuteAsTemplate {
    /// Create a new execute_as template.
    pub fn new(protocol_name: &str, roles: Vec<String>) -> Self {
        Self {
            protocol_name: protocol_name.to_string(),
            roles,
        }
    }
}

impl Template for ExecuteAsTemplate {
    fn generate(&self) -> TokenStream {
        let role_enum = format_ident!("{}Role", self.protocol_name);

        let role_variants: Vec<TokenStream> = self
            .roles
            .iter()
            .map(|r| {
                let ident = format_ident!("{}", r);
                quote! { #ident }
            })
            .collect();

        let match_arms: Vec<TokenStream> = self
            .roles
            .iter()
            .map(|r| {
                let variant = format_ident!("{}", r);
                let fn_name = format_ident!("run_{}", r.to_lowercase());
                quote! {
                    #role_enum::#variant => #fn_name(adapter).await?
                }
            })
            .collect();

        quote! {
            /// Role enum for dispatch.
            #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
            pub enum #role_enum {
                #(#role_variants),*
            }

            /// Execute the protocol as a specific role.
            pub async fn execute_as<A: Adapter>(
                role: #role_enum,
                adapter: &mut A,
            ) -> Result<(), A::Error> {
                match role {
                    #(#match_arms),*
                }

                Ok(())
            }
        }
    }

    fn name(&self) -> &str {
        "Execute As"
    }

    fn description(&self) -> &str {
        "Generates an execute_as dispatch function for protocol roles"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_runner_template() {
        let template = RunnerTemplate::new("Echo", "Client");
        let code = template.generate();
        let code_str = code.to_string();

        assert!(code_str.contains("run_client"));
        assert!(code_str.contains("ClientOutput"));
        assert!(code_str.contains("async fn"));
    }

    #[test]
    fn test_indexed_runner() {
        let template = RunnerTemplate::new("Ring", "Node").with_index(true);
        let code = template.generate();
        let code_str = code.to_string();

        // quote! may render with different spacing
        assert!(
            code_str.contains("index") && code_str.contains("u32"),
            "Generated: {}",
            code_str
        );
        assert!(code_str.contains("indexed"));
    }

    #[test]
    fn test_execute_as_template() {
        let template = ExecuteAsTemplate::new("Echo", vec!["Client".into(), "Server".into()]);
        let code = template.generate();
        let code_str = code.to_string();

        assert!(code_str.contains("enum EchoRole"));
        assert!(code_str.contains("execute_as"));
        assert!(code_str.contains("run_client"));
        assert!(code_str.contains("run_server"));
    }
}
