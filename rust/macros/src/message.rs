//! Implementation of the `Message` derive macro.
//!
//! Provides automatic implementation of the `Message` trait for message types
//! used in session-typed protocols.

use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use std::collections::BTreeMap;
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
        return Ok(derive_struct_message_impl(
            ident,
            &impl_generics,
            &ty_generics,
            where_clause,
        ));
    }

    let variants = match &input.data {
        Data::Enum(input) => Ok(&input.variants),
        _ => Err(Error::new_spanned(&input, "expected a struct or enum")),
    }?;

    derive_enum_message_impl(variants, ident, &impl_generics, &ty_generics, where_clause)
}

fn derive_struct_message_impl(
    ident: &syn::Ident,
    impl_generics: &impl quote::ToTokens,
    ty_generics: &impl quote::ToTokens,
    where_clause: Option<&syn::WhereClause>,
) -> TokenStream {
    quote! {
        impl #impl_generics ::telltale::Message<Self> for #ident #ty_generics #where_clause {
            fn upcast(label: Self) -> Self {
                label
            }

            fn downcast(self) -> ::core::result::Result<Self, Self> {
                ::core::result::Result::Ok(self)
            }
        }
    }
}

fn derive_enum_message_impl(
    variants: &syn::punctuated::Punctuated<syn::Variant, syn::token::Comma>,
    ident: &syn::Ident,
    impl_generics: &impl quote::ToTokens,
    ty_generics: &impl quote::ToTokens,
    where_clause: Option<&syn::WhereClause>,
) -> Result<TokenStream> {
    let mut output = TokenStream::new();
    let mut payload_types: BTreeMap<String, syn::Ident> = BTreeMap::new();
    for variant in variants {
        let (variant_ident, ty) = parse_variant_payload(variant)?;
        ensure_unique_payload_type(&mut payload_types, variant, variant_ident, ty)?;
        output.extend(quote! {
            impl #impl_generics ::telltale::Message<#ty> for #ident #ty_generics #where_clause {
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

fn parse_variant_payload(variant: &syn::Variant) -> Result<(&syn::Ident, &syn::Type)> {
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
    Ok((variant_ident, &field.ty))
}

fn ensure_unique_payload_type(
    payload_types: &mut BTreeMap<String, syn::Ident>,
    variant: &syn::Variant,
    variant_ident: &syn::Ident,
    ty: &syn::Type,
) -> Result<()> {
    let ty_key = ty.to_token_stream().to_string();
    if let Some(existing_variant) = payload_types.get(&ty_key) {
        return Err(Error::new_spanned(
            variant,
            format!(
                "duplicate payload type for Message derive: variants '{}' and '{}' both use type `{}`",
                existing_variant, variant_ident, ty_key
            ),
        ));
    }
    payload_types.insert(ty_key, variant_ident.clone());
    Ok(())
}
