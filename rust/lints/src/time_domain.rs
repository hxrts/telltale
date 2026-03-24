//! Time domain boundary lint.
//! Flags direct wall-clock and timer primitives in deterministic
//! runtime paths where time must be injected through effects.

use std::path::Path;

use proc_macro2::Span;
use syn::spanned::Spanned;
use syn::visit::{self, Visit};
use syn::ExprCall;

use crate::common::{call_path_string, file_matches_suffix, format_violation};

/// Walk the AST looking for function calls that read the system
/// clock or create timers. The protocol machine and simulator must
/// receive time through explicit effect injection so that replay
/// and cross-target equivalence are preserved.
pub(crate) fn scan(file: &Path, syntax: &syn::File) -> Vec<String> {
    // Bridge runner files legitimately interact with wall-clock time
    // to drive the Lean binary subprocess.
    const ALLOWED_SUFFIXES: &[&str] = &[
        "rust/bridge/src/runner.rs",
        "rust/bridge/src/protocol_machine_runner.rs",
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
            // Match both fully-qualified and short forms of clock/timer calls.
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
