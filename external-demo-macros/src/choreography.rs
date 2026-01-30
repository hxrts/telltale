//! Full-featured choreography! macro implementation
//!
//! This module provides the full-featured choreography! macro that bridges
//! the advanced parser capabilities with the proc macro interface.

use proc_macro2::TokenStream;
use telltale_choreography::{extensions::ExtensionRegistry, parse_and_generate_with_extensions};

/// Implementation of the full-featured choreography! macro
pub fn choreography_impl(input: TokenStream) -> Result<TokenStream, syn::Error> {
    // Convert token stream to string for parsing
    let input_str = input.to_string();

    // Create empty extension registry to avoid the buggy timeout extension
    // TODO: Once the timeout extension's generate_code() method is fixed,
    // this can be changed back to ExtensionRegistry::with_builtin_extensions()
    let registry = ExtensionRegistry::new();

    // Parse and generate code with full extension support
    match parse_and_generate_with_extensions(&input_str, &registry) {
        Ok(tokens) => Ok(tokens),
        Err(err) => {
            let error_msg = err.to_string();
            Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                format!("Choreography compilation error: {}", error_msg),
            ))
        }
    }
}
