//! Session ingress boundary lint.
//! Flags raw session-store ownership mutation outside the sanctioned
//! entry points that form the owned-session boundary.

use std::path::Path;

use proc_macro2::Span;
use syn::spanned::Spanned;
use syn::visit::{self, Visit};
use syn::ExprMethodCall;

use crate::common::{display_path, file_matches_suffix, format_violation, is_test_like_path};

/// Walk the AST looking for method calls that directly mutate
/// session ownership state. Only a small set of files in the
/// protocol machine crate are permitted to use these methods.
pub(crate) fn scan(file: &Path, syntax: &syn::File) -> Vec<String> {
    // Files that implement the ownership boundary itself.
    const ALLOWED_SUFFIXES: &[&str] = &[
        "rust/machine/src/owned.rs",
        "rust/machine/src/session/store.rs",
        "rust/machine/src/session/tests.rs",
        "rust/machine/src/threaded/runtime_and_scheduling.rs",
        "rust/machine/src/engine/topology_and_dispatch.rs",
        "rust/machine/src/engine/validation.rs",
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
            // These methods bypass the typed ownership API and operate
            // directly on the session store. Any call outside the
            // allowed files is a boundary violation.
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
