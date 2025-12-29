//! Role Struct Template
//!
//! Generates role structs with associated session types.

use super::Template;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};

/// Template for generating a role struct.
#[derive(Debug, Clone)]
pub struct RoleTemplate {
    /// Role name
    pub name: String,
    /// Session type (as string for template)
    pub session_type: String,
    /// Partner roles
    pub partners: Vec<String>,
}

impl RoleTemplate {
    /// Create a new role template.
    pub fn new(name: &str, session_type: &str) -> Self {
        Self {
            name: name.to_string(),
            session_type: session_type.to_string(),
            partners: Vec::new(),
        }
    }

    /// Add partner roles.
    pub fn with_partners(mut self, partners: Vec<String>) -> Self {
        self.partners = partners;
        self
    }
}

impl Template for RoleTemplate {
    fn generate(&self) -> TokenStream {
        let role_name = format_ident!("{}", self.name);
        let _session_doc = &self.session_type;

        let partner_channels: Vec<TokenStream> = self
            .partners
            .iter()
            .map(|p| {
                let field_name = format_ident!("{}", p.to_lowercase());
                let channel_type = format_ident!("{}Channel", p);
                quote! {
                    pub #field_name: #channel_type
                }
            })
            .collect();

        let channel_struct = if partner_channels.is_empty() {
            quote! {}
        } else {
            quote! {
                /// Channel bundle for this role.
                pub struct #role_name Channels<C> {
                    #(#partner_channels),*
                }
            }
        };

        quote! {
            /// Role: #role_name
            ///
            /// Session type: #session_doc
            #[derive(Debug)]
            pub struct #role_name<S> {
                _session: std::marker::PhantomData<S>,
            }

            impl<S> #role_name<S> {
                /// Create a new role instance.
                pub fn new() -> Self {
                    Self {
                        _session: std::marker::PhantomData,
                    }
                }
            }

            impl<S> Default for #role_name<S> {
                fn default() -> Self {
                    Self::new()
                }
            }

            #channel_struct
        }
    }

    fn name(&self) -> &str {
        "Role Struct"
    }

    fn description(&self) -> &str {
        "Generates a role struct with session type parameter"
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_role_template() {
        let template = RoleTemplate::new(
            "Client",
            "Send<Server, Request, Recv<Server, Response, End>>",
        );
        let code = template.generate();
        let code_str = code.to_string();

        assert!(code_str.contains("struct Client"));
        assert!(code_str.contains("PhantomData"));
    }

    #[test]
    fn test_role_with_partners() {
        let template = RoleTemplate::new("Client", "End").with_partners(vec!["Server".into()]);
        let code = template.generate();
        let code_str = code.to_string();

        assert!(code_str.contains("Client"));
    }
}
