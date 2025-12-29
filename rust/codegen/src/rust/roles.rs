//! Role Code Generation
//!
//! Generates Rust structs and implementations for protocol roles.

use super::session::generate_session_type;
use crate::ir::RoleIR;
use proc_macro2::TokenStream;
use quote::quote;

/// Generate role struct and implementation
pub fn generate_role(role: &RoleIR) -> TokenStream {
    let name = syn::Ident::new(&role.name, proc_macro2::Span::call_site());
    let session_type = generate_session_type(&role.local_type);

    // Generate channel type parameters for each partner
    let partner_channels: Vec<TokenStream> = role
        .partners
        .iter()
        .map(|p| {
            let partner = syn::Ident::new(p, proc_macro2::Span::call_site());
            quote! { #partner: Channel }
        })
        .collect();

    quote! {
        /// Role: #name
        pub struct #name<#(#partner_channels),*> {
            _marker: std::marker::PhantomData<(#session_type)>,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rumpsteak_types::{Label, LocalTypeR};

    #[test]
    fn test_generate_role() {
        let lt = LocalTypeR::send("Server", Label::new("request"), LocalTypeR::End);
        let role = RoleIR::new("Client", lt);
        let code = generate_role(&role);

        let code_str = code.to_string();
        assert!(code_str.contains("Client"));
        assert!(code_str.contains("struct"));
    }
}
