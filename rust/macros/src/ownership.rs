//! Ownership-annotation attribute macros for protocol authority.

use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse2, Item, LitStr};

pub(crate) fn observed_only(attr: TokenStream, input: TokenStream) -> syn::Result<TokenStream> {
    if !attr.is_empty() {
        return Err(syn::Error::new_spanned(
            attr,
            "#[observed_only] does not accept arguments",
        ));
    }
    passthrough_item(
        "observed_only",
        input,
        &["fn", "struct", "enum", "mod", "impl", "type"],
    )
}

pub(crate) fn actor_owned(attr: TokenStream, input: TokenStream) -> syn::Result<TokenStream> {
    labeled_item(
        "actor_owned",
        attr,
        input,
        &["fn", "struct", "mod", "impl", "type"],
    )
}

pub(crate) fn authoritative_source(
    attr: TokenStream,
    input: TokenStream,
) -> syn::Result<TokenStream> {
    labeled_item(
        "authoritative_source",
        attr,
        input,
        &["fn", "mod", "impl", "type"],
    )
}

pub(crate) fn strong_reference(attr: TokenStream, input: TokenStream) -> syn::Result<TokenStream> {
    labeled_item(
        "strong_reference",
        attr,
        input,
        &["struct", "enum", "type", "fn"],
    )
}

pub(crate) fn weak_identifier(attr: TokenStream, input: TokenStream) -> syn::Result<TokenStream> {
    labeled_item(
        "weak_identifier",
        attr,
        input,
        &["struct", "enum", "type", "fn"],
    )
}

fn passthrough_item(
    marker: &str,
    input: TokenStream,
    allowed_kinds: &[&str],
) -> syn::Result<TokenStream> {
    let item = parse2::<Item>(input)?;
    ensure_allowed(marker, &item, allowed_kinds)?;
    Ok(quote!(#item))
}

fn labeled_item(
    marker: &str,
    attr: TokenStream,
    input: TokenStream,
    allowed_kinds: &[&str],
) -> syn::Result<TokenStream> {
    let _label = parse2::<LitStr>(attr).map_err(|_| {
        syn::Error::new(
            proc_macro2::Span::call_site(),
            format!("#[{marker}(\"...\")] requires one string label"),
        )
    })?;
    passthrough_item(marker, input, allowed_kinds)
}

fn ensure_allowed(marker: &str, item: &Item, allowed_kinds: &[&str]) -> syn::Result<()> {
    let kind = item_kind(item);
    if allowed_kinds.iter().any(|allowed| *allowed == kind) {
        return Ok(());
    }
    Err(syn::Error::new_spanned(
        item,
        format!(
            "#[{marker}] is only supported on {} items, not {kind}",
            allowed_kinds.join(", ")
        ),
    ))
}

fn item_kind(item: &Item) -> &'static str {
    match item {
        Item::Const(_) => "const",
        Item::Enum(_) => "enum",
        Item::ExternCrate(_) => "extern_crate",
        Item::Fn(_) => "fn",
        Item::ForeignMod(_) => "foreign_mod",
        Item::Impl(_) => "impl",
        Item::Macro(_) => "macro",
        Item::Mod(_) => "mod",
        Item::Static(_) => "static",
        Item::Struct(_) => "struct",
        Item::Trait(_) => "trait",
        Item::TraitAlias(_) => "trait_alias",
        Item::Type(_) => "type",
        Item::Union(_) => "union",
        Item::Use(_) => "use",
        _ => "item",
    }
}
