use std::{collections::BTreeSet, fs, path::Path, process::Command};

use anyhow::{bail, Context, Result};
use syn::visit::Visit;

struct RequiredSuite {
    source: &'static str,
    prefix: &'static str,
    filter: &'static str,
    names: &'static [&'static str],
}

const SUITES: &[RequiredSuite] = &[
    RequiredSuite {
        source: "rust/machine/tests/unit/protocol_machine/tests_runtime_progress.rs",
        prefix: "engine::tests::",
        filter: "required_cooperative_reap",
        names: &[
            "required_cooperative_reap_removes_target_and_preserves_other_sessions",
            "required_cooperative_reap_validates_deserialized_stable_ids",
            "required_cooperative_reap_preserves_natural_terminal_epoch",
            "required_cooperative_reap_rejects_active_epoch_exhaustion_before_mutation",
        ],
    },
    RequiredSuite {
        source: "rust/machine/tests/unit/threaded_runtime_tests.rs",
        prefix: "threaded::tests::",
        filter: "required_threaded_reap",
        names: &[
            "required_threaded_reap_preserves_other_sessions_and_stable_ids",
            "required_threaded_reap_rejects_epoch_and_index_faults_before_mutation",
            "required_threaded_reap_preserves_actual_poison_failure",
            "required_threaded_reap_acknowledges_completed_worker_scope",
            "required_threaded_reap_preserves_natural_terminal_epoch",
        ],
    },
    RequiredSuite {
        source: "rust/machine/tests/unit/threaded_runtime_tests.rs",
        prefix: "threaded::tests::",
        filter: "required_disposal_cooperative_threaded_summaries_match",
        names: &["required_disposal_cooperative_threaded_summaries_match"],
    },
];

fn ignored(meta: &syn::Meta) -> bool {
    if meta.path().is_ident("ignore") {
        return true;
    }
    if !meta.path().is_ident("cfg_attr") {
        return false;
    }
    let syn::Meta::List(list) = meta else {
        return true;
    };
    match list
        .parse_args_with(syn::punctuated::Punctuated::<syn::Meta, syn::Token![,]>::parse_terminated)
    {
        Ok(arguments) => arguments.iter().skip(1).any(ignored),
        Err(_) => true,
    }
}

fn require_source_tests(source: &str, required: &[&str]) -> Result<()> {
    struct Inventory {
        required: BTreeSet<String>,
        observed: BTreeSet<String>,
    }
    impl<'ast> Visit<'ast> for Inventory {
        fn visit_item_fn(&mut self, function: &'ast syn::ItemFn) {
            let name = function.sig.ident.to_string();
            if self.required.contains(&name)
                && function
                    .attrs
                    .iter()
                    .any(|attr| attr.path().is_ident("test"))
                && !function.attrs.iter().any(|attr| ignored(&attr.meta))
            {
                self.observed.insert(name);
            }
            syn::visit::visit_item_fn(self, function);
        }
    }
    let syntax = syn::parse_file(source).context("parse required disposal test inventory")?;
    let mut inventory = Inventory {
        required: required.iter().map(|name| (*name).to_owned()).collect(),
        observed: BTreeSet::new(),
    };
    inventory.visit_file(&syntax);
    let missing: Vec<_> = inventory.required.difference(&inventory.observed).collect();
    if !missing.is_empty() {
        bail!("session-disposal: required nonignored source tests missing: {missing:?}");
    }
    Ok(())
}

fn require_harness_tests(listing: &str, suite: &RequiredSuite) -> Result<()> {
    let actual: BTreeSet<_> = listing
        .lines()
        .filter_map(|line| line.strip_suffix(": test"))
        .collect();
    for name in suite.names {
        let exact = format!("{}{name}", suite.prefix);
        if !exact.contains(suite.filter) || !actual.contains(exact.as_str()) {
            bail!("session-disposal: required test absent from actual filtered harness: {exact}");
        }
    }
    Ok(())
}

fn require_passed_tests(output: &str, suite: &RequiredSuite) -> Result<()> {
    let passed: BTreeSet<_> = output
        .lines()
        .filter_map(|line| {
            line.strip_prefix("test ")
                .and_then(|line| line.strip_suffix(" ... ok"))
        })
        .collect();
    for name in suite.names {
        let exact = format!("{}{name}", suite.prefix);
        if !passed.contains(exact.as_str()) {
            bail!("session-disposal: required test did not execute successfully: {exact}");
        }
    }
    Ok(())
}

fn cargo_output(root: &Path, tail: &[&str]) -> Result<String> {
    let output = Command::new("cargo")
        .current_dir(root)
        .env("CARGO_TERM_COLOR", "never")
        .args([
            "test",
            "-p",
            "telltale-machine",
            "--features",
            "multi-thread",
            "--lib",
        ])
        .args(tail)
        .output()
        .context("run actual session disposal test harness")?;
    let stdout = String::from_utf8(output.stdout).context("decode test harness output")?;
    let stderr = String::from_utf8(output.stderr).context("decode cargo diagnostics")?;
    print!("{stdout}");
    eprint!("{stderr}");
    if !output.status.success() {
        bail!(
            "session-disposal: actual cargo test harness failed: {}",
            output.status
        );
    }
    Ok(stdout)
}

pub fn run(root: &Path) -> Result<()> {
    for suite in SUITES {
        let source = fs::read_to_string(root.join(suite.source))
            .with_context(|| format!("read required tests {}", suite.source))?;
        require_source_tests(&source, suite.names)?;
    }
    let listing = cargo_output(root, &["--", "--list", "--color", "never"])?;
    for suite in SUITES {
        require_harness_tests(&listing, suite)?;
    }
    for suite in SUITES {
        let output = cargo_output(root, &[suite.filter, "--", "--color", "never"])?;
        require_passed_tests(&output, suite)?;
    }
    println!("session-disposal: all ten required tests executed successfully");
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_inventory_rejects_missing_ignored_nested_and_fabricated_tests() {
        assert!(require_source_tests("#[test] fn target() {}", &["target"]).is_ok());
        for source in [
            "#[test] fn other() {}",
            "#[test] #[ignore] fn target() {}",
            "#[test] #[cfg_attr(any(), ignore)] fn target() {}",
            "#[test] #[cfg_attr(any(), cfg_attr(any(), ignore))] fn target() {}",
            "#[test] #[cfg_attr(any(), cfg_attr(any(), ignore = \"optional\"))] fn target() {}",
            "#[fake::test] fn target() {}",
            "// #[test] fn target() {}",
        ] {
            assert!(
                require_source_tests(source, &["target"]).is_err(),
                "{source}"
            );
        }
    }

    #[test]
    fn harness_inventory_rejects_zero_missing_and_wrong_module_tests() {
        let suite = RequiredSuite {
            source: "fixture",
            prefix: "owner::",
            filter: "target",
            names: &["target"],
        };
        assert!(require_harness_tests("owner::target: test\n", &suite).is_ok());
        for listing in [
            "0 tests, 0 benchmarks",
            "owner::other: test",
            "foreign::target: test",
        ] {
            assert!(require_harness_tests(listing, &suite).is_err());
        }
    }

    #[test]
    fn execution_inventory_rejects_missing_ignored_and_failed_results() {
        let suite = RequiredSuite {
            source: "fixture",
            prefix: "owner::",
            filter: "target",
            names: &["target"],
        };
        assert!(require_passed_tests("test owner::target ... ok\n", &suite).is_ok());
        for output in [
            "test result: ok. 0 passed; 0 failed; 0 ignored",
            "test owner::target ... ignored",
            "test owner::target ... FAILED",
            "test foreign::target ... ok",
        ] {
            assert!(require_passed_tests(output, &suite).is_err());
        }
    }
}
