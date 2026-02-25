//! Implementation of the `Role` derive macro.
//!
//! Provides automatic implementation of the `Role` trait and `Route` traits
//! for role types in session-typed protocols.

use crate::parse;
use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use syn::{parse2, spanned::Spanned, Data, DeriveInput, Error, Index, Result, Type};

fn field_token(field: &syn::Field, index: usize) -> TokenStream {
    match &field.ident {
        Some(ident) => ident.to_token_stream(),
        None => Index::from(index).to_token_stream(),
    }
}

fn collect_field_idents(fields: &syn::Fields) -> Vec<TokenStream> {
    fields
        .iter()
        .enumerate()
        .map(|(i, field)| field_token(field, i))
        .collect()
}

fn generate_role_impl(
    ident: &syn::Ident,
    impl_generics: &impl quote::ToTokens,
    ty_generics: &impl quote::ToTokens,
    where_clause: Option<&syn::WhereClause>,
    message: &Type,
    field_idents: &[TokenStream],
) -> TokenStream {
    quote! {
        impl #impl_generics ::telltale::Role for #ident #ty_generics #where_clause {
            type Message = #message;

            fn seal(&mut self) {
                #(
                    ::telltale::Sealable::seal(&mut self.#field_idents);
                )*
            }

            fn is_sealed(&self) -> bool {
                #(
                    if ::telltale::Sealable::is_sealed(&self.#field_idents) {
                        return true;
                    }
                )*
                false
            }
        }
    }
}

fn generate_route_impls(
    fields: &syn::Fields,
    ident: &syn::Ident,
    impl_generics: &impl quote::ToTokens,
    ty_generics: &impl quote::ToTokens,
    where_clause: Option<&syn::WhereClause>,
) -> Result<TokenStream> {
    let mut output = TokenStream::new();
    for (i, field) in fields.iter().enumerate() {
        let route = parse::attribute::<Type>(&field.attrs, "route", field.span())?;
        let field_ty = &field.ty;
        let field_ident = field_token(field, i);

        output.extend(quote! {
            impl #impl_generics ::telltale::Route<#route> for #ident #ty_generics #where_clause {
                type Route = #field_ty;

                fn route(&mut self) -> &mut Self::Route {
                    &mut self.#field_ident
                }
            }
        });
    }
    Ok(output)
}

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

    let field_idents = collect_field_idents(fields);
    let mut output = generate_role_impl(
        ident,
        &impl_generics,
        &ty_generics,
        where_clause,
        &message,
        &field_idents,
    );
    output.extend(generate_route_impls(
        fields,
        ident,
        &impl_generics,
        &ty_generics,
        where_clause,
    )?);
    Ok(output)
}
