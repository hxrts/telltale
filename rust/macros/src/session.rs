//! Implementation of the `#[session]` attribute macro.
//!
//! Transforms session type definitions by adding lifetime parameters and
//! generating trait implementations for working with session types.

use proc_macro2::TokenStream;
use quote::{quote, ToTokens};
use std::{collections::HashSet, mem};
use syn::{
    parse::Nothing, parse2, parse_quote, punctuated::Punctuated, Error, Fields, GenericArgument,
    GenericParam, Ident, Index, Item, ItemEnum, ItemStruct, ItemType, PathArguments, Result, Type,
};

/// Extracts type parameter identifiers from generic parameters.
fn idents_set<P>(params: &Punctuated<GenericParam, P>) -> HashSet<Ident> {
    let idents = params.iter().filter_map(|param| match param {
        GenericParam::Type(ty) => Some(ty.ident.clone()),
        _ => None,
    });
    idents.collect::<HashSet<_>>()
}

/// Prepends items from `right` to `left` in a punctuated list.
fn punctuated_prepend<T, P: Default>(left: &mut Punctuated<T, P>, mut right: Punctuated<T, P>) {
    right.extend(mem::take(left));
    *left = right;
}

/// Unwraps grouped or parenthesized types to get the inner type.
fn unroll_type(mut ty: &mut Type) -> &mut Type {
    loop {
        ty = match ty {
            Type::Group(ty) => ty.elem.as_mut(),
            Type::Paren(ty) => ty.elem.as_mut(),
            _ => break,
        }
    }

    ty
}

/// Augments a type with lifetime and role parameters for session types.
///
/// Recursively adds `'__r` and `__R` parameters to session type constructors
/// while excluding types that are already parameterized.
fn augment_type(mut ty: &mut Type, exclude: &HashSet<Ident>) {
    while let Type::Path(path) = unroll_type(ty) {
        // Check if this is a "Self" type path
        if path.path.segments.len() == 1 && path.path.segments.first().unwrap().ident == "Self" {
            break;
        }

        let Some(segment) = path.path.segments.last_mut() else {
            break;
        };

        if let PathArguments::None = segment.arguments {
            if exclude.contains(&segment.ident) {
                break;
            }

            segment.arguments = PathArguments::AngleBracketed(parse_quote!(<>));
        }

        let args = match &mut segment.arguments {
            PathArguments::AngleBracketed(args) => &mut args.args,
            _ => break,
        };

        let is_empty = args.is_empty();
        punctuated_prepend(args, parse_quote!('__r, __R));

        if is_empty {
            break;
        }

        ty = match args.last_mut() {
            Some(GenericArgument::Type(ty)) => ty,
            _ => break,
        };
    }
}

/// Transforms a type alias into a session type with lifetime parameters.
fn session_type(mut input: ItemType) -> TokenStream {
    let exclude = idents_set(&input.generics.params);
    punctuated_prepend(
        &mut input.generics.params,
        parse_quote!('__r, __R: ::rumpsteak_aura::Role),
    );
    augment_type(&mut input.ty, &exclude);
    input.into_token_stream()
}

/// Transforms a struct into a session type with necessary trait implementations.
fn session_struct(mut input: ItemStruct) -> Result<TokenStream> {
    let ident = &input.ident;
    let exclude = idents_set(&input.generics.params);

    punctuated_prepend(
        &mut input.generics.params,
        parse_quote!('__r, __R: ::rumpsteak_aura::Role),
    );
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    if input.fields.len() != 1 {
        let message = "expected exactly one field";
        return Err(Error::new_spanned(&input.fields, message));
    }

    let field = input.fields.iter_mut().next().unwrap();
    augment_type(&mut field.ty, &exclude);

    let field_ty = &field.ty;
    let field_ident = match &field.ident {
        Some(ident) => ident.to_token_stream(),
        None => Index::from(0).to_token_stream(),
    };

    let mut output = TokenStream::new();
    output.extend(quote! {
        impl #impl_generics ::rumpsteak_aura::FromState<'__r> for #ident #ty_generics #where_clause {
            type Role = __R;

            fn from_state(state: ::rumpsteak_aura::State<'__r, Self::Role>) -> Self {
                Self { #field_ident: ::rumpsteak_aura::FromState::from_state(state) }
            }
        }

        impl #impl_generics ::rumpsteak_aura::IntoSession<'__r> for #ident #ty_generics #where_clause {
            type Session = #field_ty;

            fn into_session(self) -> Self::Session {
                self.#field_ident
            }
        }
    });

    #[cfg(feature = "serialize")]
    {
        let mut where_clause = where_clause.cloned().unwrap_or_else(|| parse_quote!(where));
        where_clause.predicates.push(parse_quote!(Self: 'static));

        output.extend(quote! {
            impl #impl_generics ::rumpsteak_aura::serialize::Serialize for #ident #ty_generics #where_clause {
                fn serialize(s: &mut ::rumpsteak_aura::serialize::Serializer) {
                    <#field_ty as ::rumpsteak_aura::serialize::Serialize>::serialize(s);
                }
            }
        });
    }

    Ok(quote!(#input #output))
}

/// Transforms an enum into a choice type with necessary trait implementations.
fn session_enum(mut input: ItemEnum) -> Result<TokenStream> {
    if input.variants.is_empty() {
        let message = "expected at least one variant";
        return Err(Error::new_spanned(&input.variants, message));
    }

    let ident = &input.ident;
    let exclude = idents_set(&input.generics.params);

    let mut generics = input.generics.clone();
    punctuated_prepend(
        &mut generics.params,
        parse_quote!('__q, '__r, __R: ::rumpsteak_aura::Role + '__r),
    );
    let (impl_generics, _, _) = generics.split_for_impl();

    let mut generics = input.generics.clone();
    punctuated_prepend(
        &mut generics.params,
        parse_quote!('__q, __R: ::rumpsteak_aura::Role),
    );
    let (_, ty_generics, where_clause) = generics.split_for_impl();

    let mut idents = Vec::with_capacity(input.variants.len());
    let mut labels = Vec::with_capacity(input.variants.len());
    let mut tys = Vec::with_capacity(input.variants.len());

    for variant in &mut input.variants {
        idents.push(&variant.ident);
        let fields = match &mut variant.fields {
            Fields::Unnamed(fields) => Ok(&mut fields.unnamed),
            fields => Err(Error::new_spanned(fields, "expected tuple variants")),
        }?;

        if fields.len() != 2 {
            let message = "expected exactly two fields per variant";
            return Err(Error::new_spanned(fields, message));
        }

        let mut fields = fields.iter_mut();

        let label = &fields.next().unwrap().ty;
        labels.push(label);

        let ty = &mut fields.next().unwrap().ty;
        augment_type(ty, &exclude);
        tys.push(&*ty);
    }

    let mut output = TokenStream::new();
    for (label, ty) in labels.iter().zip(&tys) {
        output.extend(quote! {
            impl #impl_generics ::rumpsteak_aura::Choice<'__r, #label> for #ident #ty_generics #where_clause {
                type Session = #ty;
            }
        });
    }

    punctuated_prepend(
        &mut input.generics.params,
        parse_quote!('__r, __R: ::rumpsteak_aura::Role),
    );
    let (impl_generics, ty_generics, _) = input.generics.split_for_impl();

    #[cfg(feature = "serialize")]
    {
        let mut where_clause = where_clause.cloned().unwrap_or_else(|| parse_quote!(where));
        where_clause.predicates.push(parse_quote!(Self: 'static));

        output.extend(quote! {
            impl #impl_generics ::rumpsteak_aura::serialize::SerializeChoices for #ident #ty_generics #where_clause {
                fn serialize_choices(mut s: ::rumpsteak_aura::serialize::ChoicesSerializer<'_>) {
                    #(s.serialize_choice::<#labels, #tys>();)*
                }
            }
        });
    }

    let mut generics = input.generics.clone();
    generics.make_where_clause().predicates.push(parse_quote! {
        __R::Message: #(::rumpsteak_aura::Message<#labels> +)*
    });

    let (_, _, where_clause) = generics.split_for_impl();
    output.extend(quote! {
        impl #impl_generics ::rumpsteak_aura::Choices<'__r> for #ident #ty_generics #where_clause {
            type Role = __R;

            fn downcast(
                state: ::rumpsteak_aura::State<'__r, Self::Role>,
                message: <Self::Role as Role>::Message,
            ) -> ::core::result::Result<Self, <Self::Role as Role>::Message> {
                #(let message = match ::rumpsteak_aura::Message::downcast(message) {
                    Ok(label) => {
                        return Ok(Self::#idents(
                            label,
                            ::rumpsteak_aura::FromState::from_state(state)
                        ));
                    }
                    Err(message) => message
                };)*

                Err(message)
            }
        }
    });

    Ok(quote!(#input #output))
}

/// Main entry point for the `#[session]` attribute macro.
///
/// Handles type aliases, structs, and enums, transforming them into
/// session types with appropriate trait implementations.
pub fn session(attr: TokenStream, input: TokenStream) -> Result<TokenStream> {
    let Nothing = parse2(attr)?;
    match parse2::<Item>(input)? {
        Item::Type(input) => Ok(session_type(input)),
        Item::Struct(input) => session_struct(input),
        Item::Enum(input) => session_enum(input),
        item => Err(Error::new_spanned(item, "expected a type, struct or enum")),
    }
}
