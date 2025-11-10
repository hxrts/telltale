//! Attribute parsing utilities for derive macros.
//!
//! Provides helper functions for extracting and validating attributes
//! on derive macro inputs.

use proc_macro2::Span;
use syn::{parse::Parse, Attribute, Error, Result};

/// Parses an optional attribute from a list of attributes.
///
/// Returns `None` if the attribute is not present, or an error if the
/// attribute appears multiple times.
pub fn optional_attribute<T: Parse>(attrs: &[Attribute], ident: &str) -> Result<Option<T>> {
    let mut output = None;
    for attr in attrs {
        if !attr.path().is_ident(ident) {
            continue;
        }

        if output.is_some() {
            return Err(Error::new_spanned(
                attr,
                format_args!("duplicate #[{ident}(...)] attribute"),
            ));
        }

        output = Some(attr.parse_args()?);
    }

    Ok(output)
}

/// Parses a required attribute from a list of attributes.
///
/// Returns an error if the attribute is not present or appears multiple times.
pub fn attribute<T: Parse>(attrs: &[Attribute], ident: &str, span: Span) -> Result<T> {
    optional_attribute(attrs, ident)?
        .ok_or_else(|| Error::new(span, format_args!("expected #[{ident}(...)] attribute")))
}
