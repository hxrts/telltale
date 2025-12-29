//! Implementation of the `Message` derive macro.
//!
//! Provides automatic implementation of the `Message` trait for message types
//! used in session-typed protocols.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse2, Data, DeriveInput, Error, Fields, Result};

/// Implements the `Message` trait for the given type.
///
/// For structs, implements identity conversions. For enums, implements
/// conversions for each variant.
pub fn message(input: TokenStream) -> Result<TokenStream> {
    let input = parse2::<DeriveInput>(input)?;

    let ident = &input.ident;
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    if let Data::Struct(_) = &input.data {
        return Ok(quote! {
            impl #impl_generics ::rumpsteak_aura::Message<Self> for #ident #ty_generics #where_clause {
                fn upcast(label: Self) -> Self {
                    label
                }

                fn downcast(self) -> ::core::result::Result<Self, Self> {
                    ::core::result::Result::Ok(self)
                }
            }
        });
    }

    let variants = match &input.data {
        Data::Enum(input) => Ok(&input.variants),
        _ => Err(Error::new_spanned(&input, "expected a struct or enum")),
    }?;

    let mut output = TokenStream::new();
    for variant in variants {
        let variant_ident = &variant.ident;
        let fields = match &variant.fields {
            Fields::Unnamed(fields) => Ok(&fields.unnamed),
            _ => Err(Error::new_spanned(&variant.fields, "expected tuple fields")),
        }?;

        let mut fields_iter = fields.iter();
        let field = if let (Some(field), None) = (fields_iter.next(), fields_iter.next()) {
            Ok(field)
        } else {
            let message = "expected exactly one field per variant";
            Err(Error::new_spanned(fields, message))
        }?;

        let ty = &field.ty;
        output.extend(quote! {
            impl #impl_generics ::rumpsteak_aura::Message<#ty> for #ident #ty_generics #where_clause {
                fn upcast(label: #ty) -> Self {
                    Self::#variant_ident(label)
                }

                fn downcast(self) -> ::core::result::Result<#ty, Self> {
                    match self {
                        Self::#variant_ident(label) => ::core::result::Result::Ok(label),
                        _ => ::core::result::Result::Err(self),
                    }
                }
            }
        });
    }

    Ok(output)
}
