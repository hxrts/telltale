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
        "rust/bridge/src/heap_parity_runner.rs",
        "rust/bridge/src/protocol_machine_runner.rs",
        // Shared owner of those runners' original physical subprocess deadline
        // and acknowledged process/pipe settlement; never a model clock.
        "rust/bridge/src/process_custody.rs",
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

#[cfg(test)]
mod tests {
    use super::*;

    fn direct_calls() -> syn::File {
        syn::parse_file("fn host() { Instant::now(); thread::sleep(duration); }").unwrap()
    }

    #[test]
    fn physical_subprocess_owners_retain_host_time() {
        for owner in [
            "runner",
            "heap_parity_runner",
            "protocol_machine_runner",
            "process_custody",
        ] {
            let path = format!("/checkout/rust/bridge/src/{owner}.rs");
            assert!(scan(Path::new(&path), &direct_calls()).is_empty(), "{path}");
        }
    }

    #[test]
    fn other_scopes_cannot_acquire_host_clock_permission() {
        for path in [
            "rust/machine/src/process_custody.rs",
            "rust/simulator/src/process_custody.rs",
            "rust/bridge/src/unrelated.rs",
            "rust/bridge/src/process_custody.rs.backup",
            "rust/bridge/src/nested/process_custody.rs",
        ] {
            let violations = scan(Path::new(path), &direct_calls());
            assert_eq!(violations.len(), 2, "{path}: {violations:?}");
            assert!(violations[0].contains("Instant::now"));
            assert!(violations[1].contains("thread::sleep"));
        }
    }

    #[test]
    fn deterministic_scopes_reject_other_native_and_async_time_calls() {
        let syntax = syn::parse_file(
            "fn deterministic() { std::time::SystemTime::now(); std::time::Instant::now(); tokio::time::timeout(limit, work); tokio::time::interval(period); tokio::time::sleep(delay); std::thread::sleep(delay); }",
        )
        .unwrap();
        for path in ["rust/machine/src/exec.rs", "rust/simulator/src/runtime.rs"] {
            assert_eq!(scan(Path::new(path), &syntax).len(), 6, "{path}");
        }
    }
}
