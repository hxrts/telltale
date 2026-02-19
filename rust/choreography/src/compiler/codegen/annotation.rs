//! Annotation code generation utilities.
//!
//! Handles generation of documentation, metadata structures, and runtime
//! accessors for protocol annotations.

use crate::ast::Protocol;
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashMap;

fn is_valid_field_ident(candidate: &str) -> bool {
    if candidate.is_empty() {
        return false;
    }
    let mut chars = candidate.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first == '_' || first.is_ascii_alphabetic()) {
        return false;
    }
    chars.all(|c| c == '_' || c.is_ascii_alphanumeric())
}

/// Generate documentation comments from annotations
pub(crate) fn generate_annotation_docs(annotations: &HashMap<String, String>) -> TokenStream {
    if annotations.is_empty() {
        return quote! {};
    }

    let doc_lines: Vec<TokenStream> = annotations
        .iter()
        .map(|(key, value)| {
            if value == "true" {
                quote! { #[doc = concat!("@", #key)] }
            } else {
                quote! { #[doc = concat!("@", #key, ": ", #value)] }
            }
        })
        .collect();

    quote! { #(#doc_lines)* }
}

/// Generate metadata structure for annotations
pub(crate) fn generate_annotation_metadata(
    name: &str,
    annotations: &HashMap<String, String>,
) -> TokenStream {
    if annotations.is_empty() {
        return quote! {};
    }

    let supported: Vec<(&str, &String)> = annotations
        .iter()
        .filter_map(|(key, value)| {
            let normalized = key.to_lowercase();
            if is_valid_field_ident(&normalized) {
                Some((key.as_str(), value))
            } else {
                None
            }
        })
        .collect();
    if supported.is_empty() {
        return quote! {};
    }

    let metadata_name = format_ident!("{}Annotations", name);
    let annotation_fields: Vec<TokenStream> = supported
        .iter()
        .map(|(key, _)| {
            let field_name = format_ident!("{}", key.to_lowercase());
            quote! {
                pub #field_name: &'static str,
            }
        })
        .collect();

    let annotation_values: Vec<TokenStream> = supported
        .iter()
        .map(|(key, value)| {
            let field_name = format_ident!("{}", key.to_lowercase());
            quote! {
                #field_name: #value,
            }
        })
        .collect();

    quote! {
        /// Generated annotation metadata
        #[derive(Debug, Clone, Copy)]
        pub struct #metadata_name {
            #(#annotation_fields)*
        }

        impl #metadata_name {
            pub const INSTANCE: Self = Self {
                #(#annotation_values)*
            };
        }
    }
}

/// Generate attributes from specific annotation keys
///
/// Reserved for future annotation-to-attribute mapping when code generation
/// supports priority, timeout, and async annotations on generated types.
#[allow(dead_code)] // Reserved for future annotation support
pub(crate) fn generate_annotation_attributes(annotations: &crate::ast::Annotations) -> TokenStream {
    let mut attrs = Vec::new();

    // Handle common annotation patterns using typed accessors
    if let Some(priority) = annotations.priority() {
        let p = priority.to_string();
        attrs.push(quote! { #[priority = #p] });
    }

    // For timeout/async/retry, fall back to string-based lookup for now
    // as these aren't yet typed variants
    if let Some(timeout) = annotations.get("timeout") {
        attrs.push(quote! { #[timeout = #timeout] });
    }

    if annotations.get("async").is_some_and(|v| v == "true") {
        attrs.push(quote! { #[async_trait] });
    }

    if let Some(retry_count) = annotations.get("retry") {
        attrs.push(quote! { #[retry = #retry_count] });
    }

    quote! { #(#attrs)* }
}

/// Generate runtime annotation accessor for a protocol node
pub(crate) fn generate_runtime_annotation_access(name: &str, protocol: &Protocol) -> TokenStream {
    let fn_name = format_ident!("get_{}_annotations", name.to_lowercase());
    let all_annotations = protocol.get_annotations();

    if all_annotations.is_empty() {
        return quote! {};
    }

    // Convert to legacy map for code generation
    let legacy_map = all_annotations.to_legacy_map();
    let annotation_map: Vec<TokenStream> = legacy_map
        .iter()
        .map(|(key, value)| {
            quote! { map.insert(#key.to_string(), #value.to_string()); }
        })
        .collect();

    quote! {
        /// Get runtime annotations for this protocol node
        pub fn #fn_name() -> std::collections::HashMap<String, String> {
            let mut map = std::collections::HashMap::new();
            #(#annotation_map)*
            map
        }
    }
}
