//! Session ingress boundary lint.
//! Flags raw session-store ownership mutation outside the sanctioned
//! entry points that form the owned-session boundary.

use std::path::Path;

use proc_macro2::Span;
use quote::ToTokens;
use syn::spanned::Spanned;
use syn::visit::{self, Visit};
use syn::{ExprMethodCall, ImplItemFn, ItemFn, ItemImpl, ItemMod, Meta};

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

    if test_only(&syntax.attrs)
        || is_test_like_path(&display_path(file))
        || file_matches_suffix(file, ALLOWED_SUFFIXES)
    {
        return Vec::new();
    }

    struct Visitor<'a> {
        file: &'a Path,
        violations: Vec<String>,
        private_threaded_store: bool,
    }

    impl Visitor<'_> {
        fn push(&mut self, span: Span, message: impl Into<String>) {
            self.violations
                .push(format_violation(self.file, span, message.into()));
        }
    }

    impl<'ast> Visit<'ast> for Visitor<'_> {
        fn visit_item_mod(&mut self, node: &'ast ItemMod) {
            if !test_only(&node.attrs) {
                visit::visit_item_mod(self, node);
            }
        }

        fn visit_item_fn(&mut self, node: &'ast ItemFn) {
            if !test_only(&node.attrs) {
                visit::visit_item_fn(self, node);
            }
        }

        fn visit_item_impl(&mut self, node: &'ast ItemImpl) {
            if test_only(&node.attrs) {
                return;
            }
            let receiver = node.self_ty.to_token_stream().to_string();
            // The sealed trait requires an issued OwnedSession at every owned
            // operation. Permit only its actual backend implementation, not
            // unrelated helpers placed in the same source file.
            if file_matches_suffix(self.file, &["rust/machine/src/threaded/owned.rs"])
                && receiver == "ThreadedProtocolMachine"
                && node.trait_.as_ref().is_some_and(|(_, path, _)| {
                    path.to_token_stream().to_string().replace(' ', "")
                        == "crate::owned::OwnedSessionMachine"
                })
            {
                return;
            }
            let previous = self.private_threaded_store;
            self.private_threaded_store = node.trait_.is_none()
                && receiver == "ThreadedSessionStore"
                && file_matches_suffix(self.file, &["rust/machine/src/threaded/prelude.rs"]);
            visit::visit_item_impl(self, node);
            self.private_threaded_store = previous;
        }

        fn visit_impl_item_fn(&mut self, node: &'ast ImplItemFn) {
            if test_only(&node.attrs) {
                return;
            }
            if self.private_threaded_store
                && node.sig.ident == "claim_ownership"
                && matches!(node.vis, syn::Visibility::Inherited)
            {
                return;
            }
            visit::visit_impl_item_fn(self, node);
        }

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
        private_threaded_store: false,
    };
    visitor.visit_file(syntax);
    visitor.violations
}

// A mixed predicate can admit production code. A test-like module name or an
// unrelated test item never exempts later production declarations.
fn test_only(attrs: &[syn::Attribute]) -> bool {
    fn requires_test(meta: &Meta) -> bool {
        match meta {
            Meta::Path(path) => path.is_ident("test"),
            Meta::List(list) if list.path.is_ident("all") || list.path.is_ident("any") => {
                let Ok(items) = list.parse_args_with(
                    syn::punctuated::Punctuated::<Meta, syn::Token![,]>::parse_terminated,
                ) else {
                    return false;
                };
                if list.path.is_ident("all") {
                    items.iter().any(requires_test)
                } else {
                    !items.is_empty() && items.iter().all(requires_test)
                }
            }
            _ => false,
        }
    }
    attrs.iter().any(|attr| {
        attr.path().is_ident("cfg")
            && attr
                .parse_args::<Meta>()
                .is_ok_and(|meta| requires_test(&meta))
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn violations(file: &str, source: &str) -> Vec<String> {
        scan(Path::new(file), &syn::parse_file(source).unwrap())
    }

    #[test]
    fn test_scopes_require_positive_predicates() {
        let source = r#"
            #[cfg(test)] mod fixtures { fn helper() { state.claim_ownership(); } }
            #[cfg(all(unix, test))] fn fixture() { state.claim_ownership(); }
            #[cfg(any(test, feature = "live"))] fn mixed() { state.claim_ownership(); }
            #[cfg(not(test))] fn production() { state.claim_ownership(); }
            mod tests { fn production() { state.claim_ownership(); } }
            fn after_tests() { state.release_ownership(); }
            fn diagnostics() { log!("state.claim_ownership()"); }
        "#;
        assert_eq!(violations("rust/machine/src/consumer.rs", source).len(), 4);
        assert!(violations(
            "rust/machine/src/consumer.rs",
            "#![cfg(test)] fn fixture() { state.claim_ownership(); }"
        )
        .is_empty());
    }

    #[test]
    fn threaded_adapter_requires_exact_trait_receiver_and_item() {
        let source = r#"
            impl crate::owned::OwnedSessionMachine for ThreadedProtocolMachine {
                fn transfer(&mut self) { state.begin_ownership_transfer(); }
            }
            fn unrelated() { state.begin_ownership_transfer(); }
        "#;
        let file = "rust/machine/src/threaded/owned.rs";
        assert_eq!(violations(file, source).len(), 1);
        assert_eq!(violations("rust/machine/src/consumer.rs", source).len(), 2);
        assert_eq!(
            violations(
                file,
                &source.replace(
                    "crate::owned::OwnedSessionMachine",
                    "other::OwnedSessionMachine"
                )
            )
            .len(),
            2
        );
        assert_eq!(
            violations(
                file,
                &source.replace("for ThreadedProtocolMachine", "for OtherMachine")
            )
            .len(),
            2
        );
    }

    #[test]
    fn threaded_claim_requires_private_original_store_method() {
        let source = r#"
            impl ThreadedSessionStore {
                fn claim_ownership(&self) { state.claim_ownership(); }
                fn unrelated(&self) { state.claim_ownership(); }
            }
            fn claim_ownership() { state.claim_ownership(); }
        "#;
        let file = "rust/machine/src/threaded/prelude.rs";
        assert_eq!(violations(file, source).len(), 2);
        assert_eq!(
            violations(
                file,
                &source.replace("fn claim_ownership(&self)", "pub fn claim_ownership(&self)")
            )
            .len(),
            3
        );
        assert_eq!(
            violations(
                file,
                &source.replace("impl ThreadedSessionStore", "impl OtherStore")
            )
            .len(),
            3
        );
        assert_eq!(violations("rust/machine/src/consumer.rs", source).len(), 3);
    }

    #[test]
    fn actual_canonical_backend_and_preflight_sources_pass() {
        for (file, source) in [
            (
                "rust/machine/src/threaded/owned.rs",
                include_str!("../../machine/src/threaded/owned.rs"),
            ),
            (
                "rust/machine/src/threaded/prelude.rs",
                include_str!("../../machine/src/threaded/prelude.rs"),
            ),
            (
                "rust/machine/src/session/ownership.rs",
                include_str!("../../machine/src/session/ownership.rs"),
            ),
        ] {
            let found = violations(file, source);
            assert!(found.is_empty(), "{file}: {found:?}");
        }
    }
}
