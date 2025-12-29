//! Session Type Generation
//!
//! Generates Rust session types from LocalTypeR.

use proc_macro2::TokenStream;
use quote::quote;
use rumpsteak_types::LocalTypeR;

/// Generate session type code from a local type
pub fn generate_session_type(lt: &LocalTypeR) -> TokenStream {
    match lt {
        LocalTypeR::End => quote! { End },

        LocalTypeR::Send { partner, branches } => {
            let partner_ident = syn::Ident::new(partner, proc_macro2::Span::call_site());

            if branches.len() == 1 {
                let (label, cont) = &branches[0];
                let label_ident = syn::Ident::new(&label.name, proc_macro2::Span::call_site());
                let cont_type = generate_session_type(cont);
                quote! { Send<#partner_ident, #label_ident, #cont_type> }
            } else {
                let choices: Vec<TokenStream> = branches
                    .iter()
                    .map(|(label, cont)| {
                        let label_ident =
                            syn::Ident::new(&label.name, proc_macro2::Span::call_site());
                        let cont_type = generate_session_type(cont);
                        quote! { #label_ident(#cont_type) }
                    })
                    .collect();
                quote! { Choose<#partner_ident, (#(#choices),*)> }
            }
        }

        LocalTypeR::Recv { partner, branches } => {
            let partner_ident = syn::Ident::new(partner, proc_macro2::Span::call_site());

            if branches.len() == 1 {
                let (label, cont) = &branches[0];
                let label_ident = syn::Ident::new(&label.name, proc_macro2::Span::call_site());
                let cont_type = generate_session_type(cont);
                quote! { Recv<#partner_ident, #label_ident, #cont_type> }
            } else {
                let offers: Vec<TokenStream> = branches
                    .iter()
                    .map(|(label, cont)| {
                        let label_ident =
                            syn::Ident::new(&label.name, proc_macro2::Span::call_site());
                        let cont_type = generate_session_type(cont);
                        quote! { #label_ident(#cont_type) }
                    })
                    .collect();
                quote! { Offer<#partner_ident, (#(#offers),*)> }
            }
        }

        LocalTypeR::Mu { var, body } => {
            let var_ident = syn::Ident::new(var, proc_macro2::Span::call_site());
            let body_type = generate_session_type(body);
            quote! { Rec<#var_ident, #body_type> }
        }

        LocalTypeR::Var(var) => {
            let var_ident = syn::Ident::new(var, proc_macro2::Span::call_site());
            quote! { Var<#var_ident> }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rumpsteak_types::Label;

    #[test]
    fn test_generate_end() {
        let code = generate_session_type(&LocalTypeR::End);
        assert_eq!(code.to_string(), "End");
    }

    #[test]
    fn test_generate_send() {
        let lt = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let code = generate_session_type(&lt);
        let code_str = code.to_string();
        assert!(code_str.contains("Send"));
        assert!(code_str.contains("B"));
    }

    #[test]
    fn test_generate_recv() {
        let lt = LocalTypeR::recv("A", Label::new("data"), LocalTypeR::End);
        let code = generate_session_type(&lt);
        let code_str = code.to_string();
        assert!(code_str.contains("Recv"));
        assert!(code_str.contains("A"));
    }

    #[test]
    fn test_generate_recursive() {
        let lt = LocalTypeR::mu(
            "loop1",
            LocalTypeR::send("B", Label::new("ping"), LocalTypeR::var("loop1")),
        );
        let code = generate_session_type(&lt);
        let code_str = code.to_string();
        assert!(code_str.contains("Rec"));
        assert!(code_str.contains("Var"));
    }
}
