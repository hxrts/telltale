//! Repo-local AST lint checks for Telltale boundary policies.

use std::env;
use std::ffi::OsStr;
use std::fs;
use std::path::{Path, PathBuf};

use proc_macro2::Span;
use quote::ToTokens;
use syn::spanned::Spanned;
use syn::visit::{self, Visit};
use syn::{
    Expr, ExprCall, ExprMethodCall, File, ImplItem, ImplItemFn, Item, ItemConst, ItemEnum,
    ItemImpl, ReturnType, Type,
};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    SessionIngress,
    TimeDomain,
    Style,
}

impl Mode {
    fn parse(raw: &str) -> Result<Self, String> {
        match raw {
            "session-ingress" => Ok(Self::SessionIngress),
            "time-domain" => Ok(Self::TimeDomain),
            "style" => Ok(Self::Style),
            other => Err(format!("unknown lint mode: {other}")),
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::SessionIngress => "session-ingress",
            Self::TimeDomain => "time-domain",
            Self::Style => "style",
        }
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut args = env::args().skip(1);
    let mode = args
        .next()
        .ok_or_else(|| "usage: telltale-lint-checks <mode> <path> [<path> ...]".to_string())
        .and_then(|value| Mode::parse(&value))?;
    let paths = args.map(PathBuf::from).collect::<Vec<_>>();
    if paths.is_empty() {
        return Err("expected at least one path to scan".to_string());
    }

    let mut rust_files = Vec::new();
    for path in &paths {
        collect_rust_files(path, &mut rust_files)?;
    }
    rust_files.sort();
    rust_files.dedup();

    let mut violations = Vec::new();
    for file in &rust_files {
        let source = fs::read_to_string(file)
            .map_err(|error| format!("failed to read {}: {error}", file.display()))?;
        let syntax = syn::parse_file(&source)
            .map_err(|error| format!("failed to parse {}: {error}", file.display()))?;
        violations.extend(scan_file(mode, file, &source, &syntax));
    }

    if !violations.is_empty() {
        for violation in violations {
            eprintln!("{violation}");
        }
        return Err(format!("{} violations remain", mode.name()));
    }

    println!("{}: clean", mode.name());
    Ok(())
}

fn collect_rust_files(path: &Path, files: &mut Vec<PathBuf>) -> Result<(), String> {
    if path.is_file() {
        if path.extension() == Some(OsStr::new("rs")) {
            files.push(path.to_path_buf());
        }
        return Ok(());
    }
    if !path.is_dir() {
        return Err(format!("path does not exist: {}", path.display()));
    }

    for entry in fs::read_dir(path)
        .map_err(|error| format!("failed to read directory {}: {error}", path.display()))?
    {
        let entry = entry.map_err(|error| {
            format!("failed to read directory entry {}: {error}", path.display())
        })?;
        let entry_path = entry.path();
        if entry_path.is_dir() {
            collect_rust_files(&entry_path, files)?;
        } else if entry_path.extension() == Some(OsStr::new("rs")) {
            files.push(entry_path);
        }
    }

    Ok(())
}

fn scan_file(mode: Mode, file: &Path, source: &str, syntax: &File) -> Vec<String> {
    match mode {
        Mode::SessionIngress => scan_session_ingress(file, syntax),
        Mode::TimeDomain => scan_time_domain(file, syntax),
        Mode::Style => scan_style(file, source, syntax),
    }
}

fn display_path(file: &Path) -> String {
    if let Ok(root) = env::current_dir() {
        if let Ok(relative) = file.strip_prefix(&root) {
            return relative.to_string_lossy().into_owned();
        }
    }
    file.to_string_lossy().into_owned()
}

fn is_test_like_path(path: &str) -> bool {
    path.contains("/tests/")
        || path.contains("/benches/")
        || path.contains("/examples/")
        || path.ends_with("/tests.rs")
        || path.ends_with("_tests.rs")
        || path.ends_with("_test.rs")
}

fn has_must_use(attrs: &[syn::Attribute]) -> bool {
    attrs.iter().any(|attr| attr.path().is_ident("must_use"))
}

fn format_violation(file: &Path, span: Span, message: impl Into<String>) -> String {
    let start = span.start();
    format!(
        "{}:{}:{}: {}",
        display_path(file),
        start.line,
        start.column + 1,
        message.into()
    )
}

fn is_integer_literal(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Lit(syn::ExprLit {
            lit: syn::Lit::Int(_),
            ..
        })
    )
}

fn is_integer_type(ty: &Type) -> bool {
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

fn has_allowed_constant_suffix(name: &str) -> bool {
    const ALLOWED_SUFFIXES: &[&str] = &[
        "_MS",
        "_SECS",
        "_COUNT",
        "_BITS",
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

fn call_path_string(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Path(path) => Some(path.path.to_token_stream().to_string().replace(' ', "")),
        Expr::Paren(inner) => call_path_string(&inner.expr),
        Expr::Group(inner) => call_path_string(&inner.expr),
        _ => None,
    }
}

fn returns_non_unit(sig: &syn::Signature) -> bool {
    !matches!(sig.output, ReturnType::Default)
}

fn return_type_is_already_must_use(sig: &syn::Signature) -> bool {
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

fn file_matches_suffix(file: &Path, suffixes: &[&str]) -> bool {
    let path = display_path(file);
    suffixes.iter().any(|suffix| path.ends_with(suffix))
}

fn scan_session_ingress(file: &Path, syntax: &File) -> Vec<String> {
    const ALLOWED_SUFFIXES: &[&str] = &[
        "rust/vm/src/owned.rs",
        "rust/vm/src/session/store.rs",
        "rust/vm/src/session/tests.rs",
        "rust/vm/src/threaded/runtime_and_scheduling.rs",
        "rust/vm/src/vm/topology_and_dispatch.rs",
        "rust/vm/src/vm/validation.rs",
    ];

    if is_test_like_path(&display_path(file)) || file_matches_suffix(file, ALLOWED_SUFFIXES) {
        return Vec::new();
    }

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
        fn visit_expr_method_call(&mut self, node: &'ast ExprMethodCall) {
            const RAW_METHODS: &[&str] = &[
                "sessions_mut",
                "claim_ownership",
                "release_ownership",
                "attenuate_ownership_scope",
                "apply_owned_session_mutation",
                "begin_ownership_transfer",
                "commit_ownership_transfer",
                "rollback_ownership_transfer",
                "cancel_abandoned_transfer",
                "fault_failed_transfer_commit",
            ];

            if RAW_METHODS.contains(&node.method.to_string().as_str()) {
                self.push(
                    node.span(),
                    format!(
                        "raw session ownership/ingress method `{}` escaped the owned-session boundary",
                        node.method
                    ),
                );
            }
            visit::visit_expr_method_call(self, node);
        }
    }

    let mut visitor = Visitor {
        file,
        violations: Vec::new(),
    };
    visitor.visit_file(syntax);
    visitor.violations
}

fn scan_time_domain(file: &Path, syntax: &File) -> Vec<String> {
    const ALLOWED_SUFFIXES: &[&str] = &[
        "rust/lean-bridge/src/runner.rs",
        "rust/lean-bridge/src/vm_runner.rs",
    ];

    if file_matches_suffix(file, ALLOWED_SUFFIXES) {
        return Vec::new();
    }

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
                    "tokio::time::sleep"
                        | "tokio::time::timeout"
                        | "tokio::time::interval"
                        | "std::thread::sleep"
                        | "thread::sleep"
                        | "SystemTime::now"
                        | "std::time::SystemTime::now"
                        | "Instant::now"
                        | "std::time::Instant::now"
                ) {
                    self.push(
                        node.span(),
                        format!("direct time primitive in deterministic runtime scope: {path}"),
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

fn scan_style(file: &Path, source: &str, syntax: &File) -> Vec<String> {
    let path = display_path(file);
    let mut violations = Vec::new();

    if !is_test_like_path(&path) {
        if path.starts_with("rust/vm/src/") && !path.ends_with("rust/vm/src/serialization.rs") {
            violations.extend(scan_canonical_bincode(file, syntax));
        }

        violations.extend(scan_blocking_lock_boundaries(file, source));
        violations.extend(scan_serialized_usize(file, syntax));
        violations.extend(scan_builder_must_use(file, syntax));
        violations.extend(scan_constant_units(file, syntax));
    }

    // Keep source referenced so the mode signature remains stable when more
    // line-based style checks are added later.
    let _ = source;

    violations
}

fn scan_blocking_lock_boundaries(file: &Path, source: &str) -> Vec<String> {
    const ALLOWED_PREFIXES: &[&str] = &["rust/vm/src/threaded/"];
    const ALLOWED_SUFFIXES: &[&str] = &[
        "rust/vm/src/nested.rs",
        "rust/vm/src/effect/runtime_types.rs",
        "rust/simulator/src/network.rs",
        "rust/simulator/src/fault.rs",
        "rust/simulator/src/material_handlers/continuum.rs",
        "rust/simulator/src/material_handlers/hamiltonian.rs",
    ];
    const BLOCKED_PATTERNS: &[&str] = &[
        "std::sync::Mutex",
        "std::sync::RwLock",
        "parking_lot::Mutex",
        "parking_lot::RwLock",
    ];

    let path = display_path(file);
    if !(path.starts_with("rust/vm/src/") || path.starts_with("rust/simulator/src/")) {
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

fn scan_canonical_bincode(file: &Path, syntax: &File) -> Vec<String> {
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

fn scan_serialized_usize(file: &Path, syntax: &File) -> Vec<String> {
    const SERIALIZED_USIZE_SCOPE: &[&str] = &[
        "rust/lean-bridge/src/vm_export.rs",
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

fn field_is_usize(ty: &Type) -> bool {
    matches!(ty, Type::Path(type_path) if type_path.path.is_ident("usize"))
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

fn scan_builder_must_use(file: &Path, syntax: &File) -> Vec<String> {
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

fn scan_constant_units(file: &Path, syntax: &File) -> Vec<String> {
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
