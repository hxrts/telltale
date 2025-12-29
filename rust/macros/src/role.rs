//! Implementation of the `Role` derive macro.
//!
//! Provides automatic implementation of the `Role` trait and `Route` traits
//! for role types in session-typed protocols.

use crate::parse;
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{parse2, spanned::Spanned, Data, DeriveInput, Error, Index, Result, Type};

/// Implements the `Role` and `Route` traits for the given type.
///
/// Requires `#[message(...)]` attribute and `#[route(...)]` attributes on fields.
pub fn role(input: TokenStream) -> Result<TokenStream> {
    let input = parse2::<DeriveInput>(input)?;

    let message = parse::attribute::<Type>(&input.attrs, "message", input.span())?;

    let ident = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let fields = match &input.data {
        Data::Struct(input) => Ok(&input.fields),
        _ => Err(Error::new_spanned(&input, "expected a struct")),
    }?;

    // Collect field identifiers for seal/is_sealed implementations
    let mut field_idents = Vec::new();

    for (i, field) in fields.iter().enumerate() {
        let field_ident = match &field.ident {
            Some(ident) => ident.to_token_stream(),
            None => Index::from(i).to_token_stream(),
        };
        field_idents.push(field_ident);
    }

    let mut output = quote! {
        impl #impl_generics ::rumpsteak_aura::Role for #ident #ty_generics #where_clause {
            type Message = #message;

            fn seal(&mut self) {
                #(
                    ::rumpsteak_aura::Sealable::seal(&mut self.#field_idents);
                )*
            }

            fn is_sealed(&self) -> bool {
                // Return true if any route is sealed
                #(
                    if ::rumpsteak_aura::Sealable::is_sealed(&self.#field_idents) {
                        return true;
                    }
                )*
                false
            }
        }
    };

    for (i, field) in fields.iter().enumerate() {
        let route = parse::attribute::<Type>(&field.attrs, "route", field.span())?;

        let field_ty = &field.ty;
        let field_ident = match &field.ident {
            Some(ident) => ident.to_token_stream(),
            None => Index::from(i).to_token_stream(),
        };

        output.extend(quote! {
            impl #impl_generics ::rumpsteak_aura::Route<#route> for #ident #ty_generics #where_clause {
                type Route = #field_ty;

                fn route(&mut self) -> &mut Self::Route {
                    &mut self.#field_ident
                }
            }
        });
    }

    Ok(output)
}
