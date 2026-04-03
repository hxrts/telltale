//! Style boundary lints.
//! Enforces serialization hygiene, blocking lock boundaries,
//! builder method annotations, and constant naming conventions.

use std::path::Path;

use proc_macro2::Span;
use quote::ToTokens;
use syn::spanned::Spanned;
use syn::visit::{self, Visit};
use syn::{ExprCall, ImplItem, ImplItemFn, Item, ItemConst, ItemEnum, ItemImpl};

use crate::common::{
    call_path_string, display_path, file_matches_suffix, format_violation,
    has_allowed_constant_suffix, has_must_use, is_integer_literal, is_integer_type,
    is_test_like_path, return_type_is_already_must_use, returns_non_unit,
};

/// Dispatch all style sub-checks for a single file. Each sub-check
/// applies its own scope filter, so the dispatch itself only skips
/// test-like paths that no sub-check cares about.
pub(crate) fn scan(file: &Path, source: &str, syntax: &syn::File) -> Vec<String> {
    let path = display_path(file);
    let mut violations = Vec::new();

    if !is_test_like_path(&path) {
        // Bincode calls must go through the canonical serialization
        // module to keep wire format changes centralized.
        if path.starts_with("rust/machine/src/")
            && !path.ends_with("rust/machine/src/serialization.rs")
        {
            violations.extend(scan_canonical_bincode(file, syntax));
        }

        violations.extend(scan_blocking_lock_boundaries(file, source));
        violations.extend(scan_serialized_usize(file, syntax));
        violations.extend(scan_builder_must_use(file, syntax));
        violations.extend(scan_constant_units(file, syntax));
    }

    violations
}

// ── Blocking lock boundaries ─────────────────────────────────────
// Mutex and RwLock types break determinism in the single-threaded
// protocol machine. Only the threaded backend and a few simulator
// modules may use them.

fn scan_blocking_lock_boundaries(file: &Path, source: &str) -> Vec<String> {
    const ALLOWED_PREFIXES: &[&str] = &["rust/machine/src/threaded/"];
    const ALLOWED_SUFFIXES: &[&str] = &[
        "rust/machine/src/nested.rs",
        "rust/machine/src/effect/runtime_types.rs",
        "rust/simulator/src/network.rs",
        "rust/simulator/src/fault.rs",
        "rust/simulator/src/reconfiguration.rs",
        "rust/simulator/src/field_handlers/continuum.rs",
        "rust/simulator/src/field_handlers/hamiltonian.rs",
    ];
    const BLOCKED_PATTERNS: &[&str] = &[
        "std::sync::Mutex",
        "std::sync::RwLock",
        "parking_lot::Mutex",
        "parking_lot::RwLock",
    ];

    let path = display_path(file);
    if !(path.starts_with("rust/machine/src/") || path.starts_with("rust/simulator/src/")) {
        return Vec::new();
    }
    if ALLOWED_PREFIXES
        .iter()
        .any(|prefix| path.starts_with(prefix))
        || file_matches_suffix(file, ALLOWED_SUFFIXES)
    {
        return Vec::new();
    }

    let mut violations = Vec::new();
    for (index, line) in source.lines().enumerate() {
        for pattern in BLOCKED_PATTERNS {
            if line.contains(pattern) {
                violations.push(format!(
                    "{}:{}:1: blocking lock type `{pattern}` escaped the sanctioned deterministic runtime boundary",
                    path,
                    index + 1
                ));
            }
        }
    }
    violations
}

// ── Canonical bincode ────────────────────────────────────────────
// All bincode calls must route through the crate::serialization
// module so wire-format versioning stays in one place.

fn scan_canonical_bincode(file: &Path, syntax: &syn::File) -> Vec<String> {
    struct Visitor<'a> {
        file: &'a Path,
        violations: Vec<String>,
    }

    impl Visitor<'_> {
        fn push(&mut self, span: Span, message: impl Into<String>) {
            self.violations
                .push(format_violation(self.file, span, message.into()));
        }
    }

    impl<'ast> Visit<'ast> for Visitor<'_> {
        fn visit_expr_call(&mut self, node: &'ast ExprCall) {
            if let Some(path) = call_path_string(&node.func) {
                if matches!(
                    path.as_str(),
                    "bincode::serialize" | "bincode::deserialize" | "bincode::serialized_size"
                ) {
                    self.push(
                        node.span(),
                        format!(
                            "direct `{path}` use is forbidden; route through crate::serialization"
                        ),
                    );
                }
            }
            visit::visit_expr_call(self, node);
        }
    }

    let mut visitor = Visitor {
        file,
        violations: Vec::new(),
    };
    visitor.visit_file(syntax);
    visitor.violations
}

// ── Serialized usize ─────────────────────────────────────────────
// usize is platform-dependent and must not appear in serialized
// types. Cross-target parity requires fixed-width integers.

fn scan_serialized_usize(file: &Path, syntax: &syn::File) -> Vec<String> {
    const SERIALIZED_USIZE_SCOPE: &[&str] = &[
        "rust/bridge/src/protocol_machine_export.rs",
        "rust/simulator/src/bin/run.rs",
    ];

    if !file_matches_suffix(file, SERIALIZED_USIZE_SCOPE) {
        return Vec::new();
    }

    let mut violations = Vec::new();
    for item in &syntax.items {
        match item {
            Item::Struct(item_struct) => {
                if !has_serde_derive(&item_struct.attrs)
                    || !matches!(item_struct.vis, syn::Visibility::Public(_))
                {
                    continue;
                }
                for field in &item_struct.fields {
                    if field_is_usize(&field.ty) {
                        violations.push(format_violation(
                            file,
                            field.ty.span(),
                            format!(
                                "serialized struct `{}` may not use `usize` fields; use a fixed-width integer",
                                item_struct.ident
                            ),
                        ));
                    }
                }
            }
            Item::Enum(item_enum) => {
                if !has_serde_derive(&item_enum.attrs)
                    || !matches!(item_enum.vis, syn::Visibility::Public(_))
                {
                    continue;
                }
                scan_serialized_enum(file, item_enum, &mut violations);
            }
            _ => {}
        }
    }
    violations
}

fn scan_serialized_enum(file: &Path, item_enum: &ItemEnum, violations: &mut Vec<String>) {
    for variant in &item_enum.variants {
        for field in &variant.fields {
            if field_is_usize(&field.ty) {
                violations.push(format_violation(
                    file,
                    field.ty.span(),
                    format!(
                        "serialized enum `{}` variant `{}` may not use `usize` fields; use a fixed-width integer",
                        item_enum.ident, variant.ident
                    ),
                ));
            }
        }
    }
}

fn field_is_usize(ty: &syn::Type) -> bool {
    matches!(ty, syn::Type::Path(type_path) if type_path.path.is_ident("usize"))
}

fn has_serde_derive(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| {
        if !attr.path().is_ident("derive") {
            return false;
        }
        attr.meta
            .to_token_stream()
            .to_string()
            .contains("Serialize")
            || attr
                .meta
                .to_token_stream()
                .to_string()
                .contains("Deserialize")
    })
}

// ── Builder #[must_use] ──────────────────────────────────────────
// Public builder methods (with_* / try_with_*) that return a value
// must be annotated #[must_use] to prevent silent configuration drops.

fn scan_builder_must_use(file: &Path, syntax: &syn::File) -> Vec<String> {
    let mut violations = Vec::new();
    for item in &syntax.items {
        if let Item::Impl(item_impl) = item {
            scan_builder_methods(file, item_impl, &mut violations);
        }
    }
    violations
}

fn scan_builder_methods(file: &Path, item_impl: &ItemImpl, violations: &mut Vec<String>) {
    for impl_item in &item_impl.items {
        if let ImplItem::Fn(method) = impl_item {
            maybe_flag_builder_method_without_must_use(file, method, violations);
        }
    }
}

fn maybe_flag_builder_method_without_must_use(
    file: &Path,
    method: &ImplItemFn,
    violations: &mut Vec<String>,
) {
    let name = method.sig.ident.to_string();
    let looks_like_builder = name.starts_with("with_") || name.starts_with("try_with_");
    if !looks_like_builder || !matches!(method.vis, syn::Visibility::Public(_)) {
        return;
    }
    if !returns_non_unit(&method.sig)
        || has_must_use(&method.attrs)
        || return_type_is_already_must_use(&method.sig)
    {
        return;
    }

    violations.push(format_violation(
        file,
        method.sig.ident.span(),
        format!("builder `{name}` must be marked #[must_use]"),
    ));
}

// ── Constant unit suffixes ───────────────────────────────────────
// SCREAMING_CASE integer constants must carry a unit suffix like
// _MS, _BYTES, or _COUNT to prevent ambiguous magic numbers.

fn scan_constant_units(file: &Path, syntax: &syn::File) -> Vec<String> {
    let mut violations = Vec::new();
    for item in &syntax.items {
        if let Item::Const(item_const) = item {
            maybe_flag_constant_without_units(file, item_const, &mut violations);
        }
    }
    violations
}

fn maybe_flag_constant_without_units(
    file: &Path,
    item_const: &ItemConst,
    violations: &mut Vec<String>,
) {
    let name = item_const.ident.to_string();
    if !name
        .chars()
        .all(|ch| ch.is_ascii_uppercase() || ch.is_ascii_digit() || ch == '_')
    {
        return;
    }
    if !is_integer_type(&item_const.ty) || !is_integer_literal(&item_const.expr) {
        return;
    }
    if has_allowed_constant_suffix(&name) {
        return;
    }

    violations.push(format_violation(
        file,
        item_const.ident.span(),
        format!("constant `{name}` must include an explicit unit/count suffix"),
    ));
}
