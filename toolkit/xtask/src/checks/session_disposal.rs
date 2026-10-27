use std::{collections::BTreeSet, fs, path::Path, process::Command};

use anyhow::{bail, Context, Result};
use syn::visit::Visit;

struct RequiredSuite {
    source: &'static str,
    target: &'static str,
    prefix: &'static str,
    filter: &'static str,
    names: &'static [&'static str],
}

const SUITES: &[RequiredSuite] = &[
    RequiredSuite {
        source: "rust/machine/src/threaded/worker_pool.rs",
        target: "lib",
        prefix: "threaded::worker_pool::tests::",
        filter: "threaded::worker_pool::tests::",
        names: &[
            "first_worker_refusal_retains_actual_source_and_zero_worker_settlement",
            "partial_worker_refusal_retains_actual_worker_until_explicit_original_join",
            "normal_pool_shutdown_joins_every_original_worker_before_acknowledgment",
            "original_worker_panic_payload_survives_acknowledged_join",
            "machine_shutdown_consumes_actual_private_pool_and_issues_join_receipt",
            "shutdown_from_actual_original_worker_returns_untouched_machine_for_external_retry",
            "normal_pool_join_unwind_retains_untouched_handles_without_acknowledgment",
            "failed_constructor_join_unwind_retains_prior_causes_and_pending_original_retry",
            "resident_settlement_refuses_actual_original_worker_before_consuming_handles",
            "pending_join_allows_original_worker_observation_and_reentrant_refusal",
            "unproven_consumed_original_worker_is_refused_before_untouched_retry",
        ],
    },
    RequiredSuite {
        source: "rust/machine/tests/unit/protocol_machine/tests_runtime_progress.rs",
        target: "lib",
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
        target: "lib",
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
        target: "lib",
        prefix: "threaded::tests::",
        filter: "required_disposal_cooperative_threaded_summaries_match",
        names: &["required_disposal_cooperative_threaded_summaries_match"],
    },
    RequiredSuite {
        source: "rust/machine/src/session/ownership.rs",
        target: "lib",
        prefix: "session::ownership_preflight_tests::",
        filter: "ownership_preflight_tests",
        names: &[
            "ownership_release_reclaim_never_reactivates_an_old_generation",
            "ownership_scope_transfer_and_attenuation_cannot_escalate",
            "ownership_identifier_exhaustion_is_preflight_only",
            "ownership_witness_exhaustion_preserves_original_pending_owner",
            "ownership_host_mutation_rejects_foreign_session_edges",
        ],
    },
    RequiredSuite {
        source: "rust/machine/src/threaded/owned.rs",
        target: "lib",
        prefix: "threaded::ownership_lock_tests::",
        filter: "ownership_lock_tests",
        names: &[
            "ownership_poisoned_session_refuses_mutation_without_replacement",
            "ownership_poisoned_audit_refuses_transition_before_state_mutation",
        ],
    },
    RequiredSuite {
        source: "rust/machine/tests/owned_backend_parity.rs",
        target: "owned_backend_parity",
        prefix: "",
        filter: "",
        names: &[
            "cooperative_owned_transactions_retain_real_audit_after_disposal",
            "threaded_owned_transactions_match_cooperative_evidence",
            "ownership_contract_error_retains_the_actual_typed_cause",
            "cooperative_terminal_ownership_checks_current_handle_and_receipt",
            "threaded_terminal_ownership_matches_cooperative_ordering",
            "cooperative_failed_commit_preserves_unrelated_owner",
            "threaded_failed_commit_matches_cooperative_terminal_evidence",
        ],
    },
    RequiredSuite {
        source: "rust/machine/tests/unit/effect_outcome_acceptance.rs",
        target: "lib",
        prefix: "effect::outcome_acceptance_tests::",
        filter: "effect::outcome_acceptance_tests::",
        names: &[
            "all_nine_request_kinds_require_their_exact_success_response",
            "typed_state_extraction_preserves_original_failure_before_attached_response",
            "unit_conversion_cannot_accept_a_different_unit_like_response",
            "replay_state_updates_require_the_original_successful_response",
        ],
    },
    RequiredSuite {
        source: "rust/machine/tests/unit/effect_outcome_acceptance.rs",
        target: "lib",
        prefix: "effect::outcome_acceptance_tests::concurrent_recording::",
        filter: "effect::outcome_acceptance_tests::concurrent_recording::",
        names: &["actual_interleaved_recording_never_substitutes_the_other_returned_state"],
    },
    RequiredSuite {
        source: "rust/machine/tests/unit/invoke_outcome_atomicity.rs",
        target: "lib",
        prefix: "engine::invoke_outcome_tests::",
        filter: "engine::invoke_outcome_tests::",
        names: &[
            "valid_invoke_commits_exact_state_and_advances_only_original_continuation",
            "invalid_invoke_never_mutates_original_registers_or_unrelated_continuation",
            "actual_receive_state_and_continuation_require_exact_success",
            "disabled_observability_never_replaces_original_failure_or_blocked_behavior",
            "all_vm_state_replacers_require_actual_configured_width_before_publication",
            "original_guard_and_send_outcomes_survive_every_retention_policy",
        ],
    },
    RequiredSuite {
        source: "rust/machine/tests/unit/invoke_outcome_atomicity.rs",
        target: "lib",
        prefix: "threaded::invoke_outcome_tests::",
        filter: "threaded::invoke_outcome_tests::",
        names: &[
            "valid_invoke_commits_exact_state_and_advances_only_original_continuation",
            "invalid_invoke_never_mutates_original_registers_or_unrelated_continuation",
            "actual_receive_state_and_continuation_require_exact_success",
            "disabled_observability_never_replaces_original_failure_or_blocked_behavior",
            "all_vm_state_replacers_require_actual_configured_width_before_publication",
            "original_guard_and_send_outcomes_survive_every_retention_policy",
        ],
    },
    RequiredSuite {
        source: "rust/machine/tests/unit/live_effect_retention.rs",
        target: "lib",
        prefix: "engine::live_effect_retention_tests::",
        filter: "engine::live_effect_retention_tests::",
        names: &[
            "actual_blocked_acquire_survives_topology_and_preserves_enforcement",
            "actual_session_settlement_prunes_only_terminal_history",
            "actual_wal_sync_keeps_original_resident_terminal_evidence_across_retention_modes",
        ],
    },
    RequiredSuite {
        source: "rust/machine/tests/unit/live_effect_retention.rs",
        target: "lib",
        prefix: "threaded::live_effect_retention_tests::",
        filter: "threaded::live_effect_retention_tests::",
        names: &[
            "actual_blocked_acquire_survives_topology_and_preserves_enforcement",
            "actual_session_settlement_prunes_only_terminal_history",
            "actual_wal_sync_keeps_original_resident_terminal_evidence_across_retention_modes",
        ],
    },
    RequiredSuite {
        source: "rust/machine/tests/unit/send_capacity_retention.rs",
        target: "lib",
        prefix: "engine::invoke_outcome_tests::",
        filter: "actual_full_send_queue_keeps_original_capacity_obligation_with_disabled_history",
        names: &["actual_full_send_queue_keeps_original_capacity_obligation_with_disabled_history"],
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

fn native_test_attribute(attribute: &syn::Attribute) -> bool {
    if attribute.path().is_ident("test") {
        return true;
    }
    let path: Vec<_> = attribute
        .path()
        .segments
        .iter()
        .map(|segment| segment.ident.to_string())
        .collect();
    if path != ["wasm_bindgen_test", "wasm_bindgen_test"] {
        return false;
    }
    matches!(attribute.parse_args::<syn::Meta>(), Ok(syn::Meta::NameValue(value))
        if value.path.is_ident("unsupported")
        && matches!(value.value, syn::Expr::Path(ref expression) if expression.path.is_ident("test")))
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
                && function.attrs.iter().any(native_test_attribute)
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

fn cargo_output(root: &Path, target: &str, tail: &[&str]) -> Result<String> {
    let mut command = Command::new("cargo");
    command
        .current_dir(root)
        .env("CARGO_TERM_COLOR", "never")
        .args([
            "test",
            "-p",
            "telltale-machine",
            "--features",
            "multi-thread",
        ]);
    if target == "lib" {
        command.arg("--lib");
    } else {
        command.args(["--test", target]);
    }
    let output = command
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
    let targets: BTreeSet<_> = SUITES.iter().map(|suite| suite.target).collect();
    for target in targets {
        let listing = cargo_output(root, target, &["--", "--list", "--color", "never"])?;
        for suite in SUITES.iter().filter(|suite| suite.target == target) {
            require_harness_tests(&listing, suite)?;
        }
    }
    for suite in SUITES {
        let output = cargo_output(
            root,
            suite.target,
            &[suite.filter, "--", "--color", "never"],
        )?;
        require_passed_tests(&output, suite)?;
    }
    println!(
        "session-disposal: all {} required ownership/disposal tests executed successfully",
        SUITES.iter().map(|suite| suite.names.len()).sum::<usize>()
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn composite_outcome_retention_inventory_requires_all_twenty_four_actual_names() {
        let new_sources = [
            "rust/machine/tests/unit/effect_outcome_acceptance.rs",
            "rust/machine/tests/unit/invoke_outcome_atomicity.rs",
            "rust/machine/tests/unit/live_effect_retention.rs",
            "rust/machine/tests/unit/send_capacity_retention.rs",
        ];
        let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
        let suites: Vec<_> = SUITES
            .iter()
            .filter(|suite| new_sources.contains(&suite.source))
            .collect();
        assert_eq!(
            suites.iter().map(|suite| suite.names.len()).sum::<usize>(),
            24
        );
        assert_eq!(
            SUITES.iter().map(|suite| suite.names.len()).sum::<usize>(),
            59
        );
        let all: BTreeSet<_> = SUITES
            .iter()
            .flat_map(|suite| {
                suite
                    .names
                    .iter()
                    .map(move |name| format!("{}{name}", suite.prefix))
            })
            .collect();
        assert_eq!(all.len(), 59, "no duplicate required canonical names");
        for suite in suites {
            assert_eq!(suite.target, "lib");
            let source = fs::read_to_string(root.join(suite.source)).unwrap();
            assert!(require_source_tests(&source, suite.names).is_ok());
            let listing = suite
                .names
                .iter()
                .map(|name| format!("{}{name}: test\n", suite.prefix))
                .collect::<String>();
            let output = suite
                .names
                .iter()
                .map(|name| format!("test {}{name} ... ok\n", suite.prefix))
                .collect::<String>();
            assert!(require_harness_tests(&listing, suite).is_ok());
            assert!(require_passed_tests(&output, suite).is_ok());
            assert!(require_harness_tests("0 tests, 0 benchmarks", suite).is_err());
            assert!(require_passed_tests("test result: ok. 0 passed", suite).is_err());
            for name in suite.names {
                let ignored =
                    source.replace(&format!("fn {name}("), &format!("#[ignore] fn {name}("));
                assert!(require_source_tests(&ignored, suite.names).is_err());
                let missing = output.replace(&format!("test {}{name} ... ok\n", suite.prefix), "");
                assert!(require_passed_tests(&missing, suite).is_err());
            }
        }
    }

    #[test]
    fn native_worker_pool_inventory_requires_actual_source_and_all_eleven_harness_outcomes() {
        let suite = SUITES
            .iter()
            .find(|suite| suite.source == "rust/machine/src/threaded/worker_pool.rs")
            .expect("canonical required native worker-pool suite");
        assert_eq!(suite.names.len(), 11);
        assert_eq!(suite.target, "lib");
        assert_eq!(suite.prefix, "threaded::worker_pool::tests::");
        assert_eq!(suite.filter, suite.prefix);
        let source = include_str!("../../../../rust/machine/src/threaded/worker_pool.rs");
        assert!(require_source_tests(source, suite.names).is_ok());
        let listing = suite
            .names
            .iter()
            .map(|name| format!("{}{name}: test\n", suite.prefix))
            .collect::<String>();
        let execution = suite
            .names
            .iter()
            .map(|name| format!("test {}{name} ... ok\n", suite.prefix))
            .collect::<String>();
        assert!(require_harness_tests(&listing, suite).is_ok());
        assert!(require_passed_tests(&execution, suite).is_ok());
        assert!(require_harness_tests("0 tests, 0 benchmarks", suite).is_err());
        assert!(
            require_passed_tests("test result: ok. 0 passed; 0 failed; 0 ignored", suite).is_err()
        );
        assert!(require_harness_tests(&listing.replace(suite.prefix, "foreign::"), suite).is_err());
        for name in suite.names {
            let ignored_source =
                source.replace(&format!("fn {name}("), &format!("#[ignore] fn {name}("));
            assert!(
                require_source_tests(&ignored_source, suite.names).is_err(),
                "source ignore must refuse {name}"
            );
            let ignored_execution = execution.replace(
                &format!("test {}{name} ... ok", suite.prefix),
                &format!("test {}{name} ... ignored", suite.prefix),
            );
            assert!(
                require_passed_tests(&ignored_execution, suite).is_err(),
                "ignored harness must refuse {name}"
            );
            let missing_listing = listing.replace(&format!("{}{name}: test\n", suite.prefix), "");
            assert!(
                require_harness_tests(&missing_listing, suite).is_err(),
                "missing actual name must refuse {name}"
            );
        }
    }

    #[test]
    fn source_inventory_rejects_missing_ignored_nested_and_fabricated_tests() {
        assert!(require_source_tests("#[test] fn target() {}", &["target"]).is_ok());
        assert!(require_source_tests(
            "#[wasm_bindgen_test::wasm_bindgen_test(unsupported = test)] fn target() {}",
            &["target"]
        )
        .is_ok());
        for source in [
            "#[wasm_bindgen_test::wasm_bindgen_test] fn target() {}",
            "#[fake::wasm_bindgen_test(unsupported = test)] fn target() {}",
            "#[wasm_bindgen_test::wasm_bindgen_test(unsupported = bench)] fn target() {}",
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
            target: "lib",
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
            target: "lib",
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
