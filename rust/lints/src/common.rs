//! Shared utilities used across all lint modes.
//! Provides path normalization, violation formatting, and AST
//! predicates for type classification and attribute inspection.

use std::env;
use std::path::Path;

use proc_macro2::Span;
use quote::ToTokens;
use syn::{Expr, ReturnType, Type};

/// Strip the repo root prefix so violations print relative paths.
pub(crate) fn display_path(file: &Path) -> String {
    if let Ok(root) = env::current_dir() {
        if let Ok(relative) = file.strip_prefix(&root) {
            return relative.to_string_lossy().into_owned();
        }
    }
    file.to_string_lossy().into_owned()
}

/// Test-like paths are excluded from most lint modes since test
/// code intentionally exercises patterns the lints forbid.
pub(crate) fn is_test_like_path(path: &str) -> bool {
    path.contains("/tests/")
        || path.contains("/benches/")
        || path.contains("/examples/")
        || path.ends_with("/tests.rs")
        || path.ends_with("_tests.rs")
        || path.ends_with("_test.rs")
}

pub(crate) fn has_must_use(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| attr.path().is_ident("must_use"))
}

/// Format a violation with file:line:col location from a proc_macro2 span.
pub(crate) fn format_violation(file: &Path, span: Span, message: impl Into<String>) -> String {
    let start = span.start();
    format!(
        "{}:{}:{}: {}",
        display_path(file),
        start.line,
        start.column + 1,
        message.into()
    )
}

pub(crate) fn is_integer_literal(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(_),
            ..
        })
    )
}

pub(crate) fn is_integer_type(ty: &Type) -> bool {
    match ty {
        Type::Path(path) => path
            .path
            .segments
            .last()
            .map(|segment| {
                let ident = segment.ident.to_string();
                matches!(
                    ident.as_str(),
                    "u8" | "u16"
                        | "u32"
                        | "u64"
                        | "u128"
                        | "usize"
                        | "i8"
                        | "i16"
                        | "i32"
                        | "i64"
                        | "i128"
                        | "isize"
                )
            })
            .unwrap_or(false),
        _ => false,
    }
}

/// Constants with these suffixes carry their units in their name,
/// so the constant-units lint does not flag them.
pub(crate) fn has_allowed_constant_suffix(name: &str) -> bool {
    const ALLOWED_SUFFIXES: &[&str] = &[
        "_MS",
        "_SECS",
        "_COUNT",
        "_BITS",
        "_BYTE",
        "_BYTES",
        "_SIZE",
        "_CAPACITY",
        "_OFFSET",
        "_INDEX",
        "_PRIME",
        "_SCALE",
        "_VERSION",
        "_LEN",
    ];

    ALLOWED_SUFFIXES.iter().any(|suffix| name.ends_with(suffix))
}

/// Extract the fully-qualified call path from a function call expression,
/// collapsing whitespace so `std :: thread :: sleep` becomes `std::thread::sleep`.
pub(crate) fn call_path_string(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Path(path) => Some(path.path.to_token_stream().to_string().replace(' ', "")),
        Expr::Paren(inner) => call_path_string(&inner.expr),
        Expr::Group(inner) => call_path_string(&inner.expr),
        _ => None,
    }
}

pub(crate) fn returns_non_unit(sig: &syn::Signature) -> bool {
    !matches!(sig.output, ReturnType::Default)
}

/// Result and Option already carry implicit must-use semantics,
/// so builder methods returning them do not need an extra annotation.
pub(crate) fn return_type_is_already_must_use(sig: &syn::Signature) -> bool {
    match &sig.output {
        ReturnType::Type(_, ty) => match ty.as_ref() {
            Type::Path(type_path) => type_path
                .path
                .segments
                .last()
                .map(|segment| matches!(segment.ident.to_string().as_str(), "Result" | "Option"))
                .unwrap_or(false),
            _ => false,
        },
        ReturnType::Default => false,
    }
}

pub(crate) fn file_matches_suffix(file: &Path, suffixes: &[&str]) -> bool {
    let path = display_path(file);
    suffixes.iter().any(|suffix| path.ends_with(suffix))
}
