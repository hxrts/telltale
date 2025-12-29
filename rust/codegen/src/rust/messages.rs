//! Message Type Generation
//!
//! Generates Rust structs and enums for protocol messages.

use crate::ir::MessageIR;
use proc_macro2::TokenStream;
use quote::quote;

/// Generate message types for a protocol
pub fn generate_messages(messages: &[MessageIR]) -> TokenStream {
    let message_types: Vec<TokenStream> = messages
        .iter()
        .map(|m| {
            let name = syn::Ident::new(&m.label.name, proc_macro2::Span::call_site());
            let rust_type = m.rust_type();
            let type_ident: TokenStream = rust_type.parse().unwrap_or_else(|_| quote! { () });

            if m.is_choice {
                // Choice labels become unit structs
                quote! {
                    /// Choice label: #name
                    #[derive(Debug, Clone, Copy)]
                    pub struct #name;
                }
            } else {
                // Message labels become structs with payload
                quote! {
                    /// Message: #name
                    #[derive(Debug, Clone)]
                    pub struct #name(pub #type_ident);
                }
            }
        })
        .collect();

    quote! {
        #(#message_types)*
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rumpsteak_types::{Label, PayloadSort};

    #[test]
    fn test_generate_unit_message() {
        let msg = MessageIR::new(Label::new("ping"), false);
        let messages = vec![msg];
        let code = generate_messages(&messages);

        let code_str = code.to_string();
        assert!(code_str.contains("ping"));
        assert!(code_str.contains("struct"));
    }

    #[test]
    fn test_generate_typed_message() {
        let msg = MessageIR::new(Label::with_sort("data", PayloadSort::Nat), false);
        let messages = vec![msg];
        let code = generate_messages(&messages);

        let code_str = code.to_string();
        assert!(code_str.contains("data"));
        assert!(code_str.contains("u64"));
    }

    #[test]
    fn test_generate_choice_label() {
        let msg = MessageIR::new(Label::new("left"), true);
        let messages = vec![msg];
        let code = generate_messages(&messages);

        let code_str = code.to_string();
        assert!(code_str.contains("left"));
        assert!(code_str.contains("Copy"));
    }

    #[test]
    fn test_generate_multiple_messages() {
        let messages = vec![
            MessageIR::new(Label::new("request"), false),
            MessageIR::new(Label::with_sort("response", PayloadSort::String), false),
        ];
        let code = generate_messages(&messages);

        let code_str = code.to_string();
        assert!(code_str.contains("request"));
        assert!(code_str.contains("response"));
        assert!(code_str.contains("String"));
    }
}
