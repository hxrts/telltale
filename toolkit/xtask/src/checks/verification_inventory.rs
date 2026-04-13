use std::fs;
use std::path::Path;

use anyhow::{bail, Result};

fn metric_value(inventory: &str, name: &str) -> Result<u64> {
    let mut found: Vec<u64> = Vec::new();
    for line in inventory.lines() {
        if !line.starts_with('|') {
            continue;
        }
        let cols: Vec<&str> = line.split('|').map(str::trim).collect();
        if cols.len() < 4 {
            continue;
        }
        let metric = cols[1];
        if metric == name {
            let raw = cols[2];
            let digits: String = raw.chars().filter(|c| c.is_ascii_digit()).collect();
            let val: u64 = digits
                .parse()
                .map_err(|_| anyhow::anyhow!("could not parse metric value for {name}: {raw}"))?;
            found.push(val);
        }
    }
    match found.len() {
        0 => bail!("missing metric row in docs/902_verification_inventory.md: {name}"),
        1 => Ok(found[0]),
        _ => bail!("duplicate metric rows in docs/902_verification_inventory.md: {name}"),
    }
}

fn recipe_command_count(justfile: &str, recipe: &str) -> Result<usize> {
    let mut in_recipe = false;
    let mut count = 0usize;
    for line in justfile.lines() {
        if in_recipe {
            if line.starts_with(' ') || line.starts_with('\t') {
                let stripped = line.trim();
                if !stripped.is_empty() && !stripped.starts_with('#') {
                    count += 1;
                }
                continue;
            } else {
                break;
            }
        }
        // Match recipe header: "name:" or "name arg:"
        if line.starts_with(recipe) {
            let rest = &line[recipe.len()..];
            if rest.starts_with(':') || rest.starts_with(' ') {
                in_recipe = true;
            }
        }
    }
    if !in_recipe {
        bail!("missing just recipe: {recipe}");
    }
    Ok(count)
}

fn count_list(items: &[&str]) -> u64 {
    items.len() as u64
}

pub fn run(repo_root: &Path) -> Result<()> {
    let inventory_path = repo_root.join("docs/902_verification_inventory.md");
    let inventory = fs::read_to_string(&inventory_path)?;
    let justfile = fs::read_to_string(repo_root.join("justfile"))?;
    let code_map = fs::read_to_string(repo_root.join("lean/CODE_MAP.md"))?;

    let mut errors: Vec<String> = Vec::new();

    let check_metric = |name: &str, actual: u64, errors: &mut Vec<String>| match metric_value(
        &inventory, name,
    ) {
        Ok(documented) if documented != actual => {
            errors.push(format!(
                    "docs/902_verification_inventory.md: metric `{name}` documents {documented} but actual is {actual}"
                ));
        }
        Err(e) => errors.push(e.to_string()),
        Ok(_) => {}
    };

    // ── Lean CODE_MAP.md total metrics ───────────────────────

    let (actual_files, actual_lines) = {
        let mut files = None;
        let mut lines = None;
        for line in code_map.lines() {
            if line.contains("**Total**") && line.contains("**") {
                let cleaned = line.replace('*', "").replace(',', "");
                let cols: Vec<&str> = cleaned.split('|').map(str::trim).collect();
                if cols.len() >= 4 {
                    let f: String = cols[2].chars().filter(|c| c.is_ascii_digit()).collect();
                    let l: String = cols[3].chars().filter(|c| c.is_ascii_digit()).collect();
                    if let (Ok(fv), Ok(lv)) = (f.parse::<u64>(), l.parse::<u64>()) {
                        files = Some(fv);
                        lines = Some(lv);
                    }
                }
                break;
            }
        }
        match (files, lines) {
            (Some(f), Some(l)) => (f, l),
            _ => {
                bail!("failed to parse lean/CODE_MAP.md total metrics");
            }
        }
    };

    let actual_search_fairness_inventory = {
        let inventory_lean_path = repo_root.join("lean/Runtime/Proofs/Search/Inventory.lean");
        if inventory_lean_path.exists() {
            let text = fs::read_to_string(&inventory_lean_path)?;
            text.lines()
                .filter(|l| l.contains("name := \"search_"))
                .count() as u64
        } else {
            0
        }
    };

    check_metric("Lean core-library files", actual_files, &mut errors);
    check_metric("Lean core-library lines", actual_lines, &mut errors);
    check_metric(
        "Lean-backed search fairness inventory entries",
        actual_search_fairness_inventory,
        &mut errors,
    );

    // ── Justfile recipe command counts ──────────────────────

    let actual_ownership = match recipe_command_count(&justfile, "check-ownership-contracts") {
        Ok(v) => v as u64,
        Err(e) => {
            errors.push(e.to_string());
            0
        }
    };
    let actual_aura = match recipe_command_count(&justfile, "check-aura-borrowed-lints") {
        Ok(v) => v as u64,
        Err(e) => {
            errors.push(e.to_string());
            0
        }
    };

    check_metric(
        "Ownership contract gate commands",
        actual_ownership,
        &mut errors,
    );
    check_metric("Aura-derived boundary checks", actual_aura, &mut errors);

    // ── Static list counts ──────────────────────────────────

    let explicit_failure_timeout_events: &[&str] = &[
        "TimeoutIssued",
        "CancellationRequested",
        "Cancelled",
        "FailureBranchEntered",
        "SessionTerminal",
    ];

    let authority_ownership_suites: &[&str] = &[
        "rust/machine/tests/ownership_contracts.rs",
        "rust/simulator/tests/ownership_faults.rs",
    ];

    let lean_correspondence_strict_suites: &[&str] = &[
        "rust/bridge/tests/lean_trace_validation.rs",
        "rust/bridge/tests/property_tests.rs",
        "rust/bridge/tests/protocol_bundle_admission_contracts.rs",
        "rust/bridge/tests/protocol_machine_correspondence_tests.rs",
        "rust/bridge/tests/protocol_machine_differential_steps.rs",
        "rust/bridge/tests/capability_model_correspondence.rs",
        "rust/bridge/tests/heap_lean_parity.rs",
        "rust/simulator/tests/lean_reference_parity.rs",
    ];

    let identity_replay_suites: &[&str] = &[
        "rust/machine/tests/serialization_replay.rs",
        "rust/machine/tests/replay_persistence_identity.rs",
        "rust/bridge/tests/semantic_object_roundtrip.rs",
        "rust/bridge/tests/protocol_machine_cross_target_tests.rs",
        "rust/bridge/tests/reconfiguration_recovery_harness.rs",
    ];

    let commitment_progress_suites: &[&str] = &[
        "rust/machine/tests/unit/protocol_machine/tests_semantic_state.rs",
        "rust/machine/tests/conformance_lean.rs",
        "rust/machine/tests/threaded_equivalence.rs",
        "rust/machine/src/runtime_contracts.rs",
    ];

    let cross_mode_semantic_parity_suites: &[&str] = &[
        "rust/machine/tests/threaded_equivalence.rs",
        "rust/machine/tests/wasm_trace_equivalence.rs",
        "rust/bridge/tests/semantic_object_roundtrip.rs",
        "rust/bridge/tests/protocol_machine_cross_target_tests.rs",
    ];

    let fail_closed_lowering_admission_suites: &[&str] = &[
        "rust/language/src/compiler/parser/mod.rs",
        "rust/runtime/tests/authority_compile_fail.rs",
        "rust/runtime/tests/authority_control_flow_corpus.rs",
        "rust/machine/src/runtime_contracts.rs",
        "rust/machine/src/composition.rs",
    ];

    let structure_reconfiguration_suites: &[&str] = &[
        "rust/machine/src/engine/runtime_exec/semantic_state.rs",
        "rust/machine/tests/ownership_contracts.rs",
        "rust/machine/src/composition.rs",
        "rust/bridge/tests/protocol_bundle_admission_contracts.rs",
        "rust/runtime/tests/generated_topology_public_path.rs",
    ];

    let semantic_lifecycle_invariant_suites: &[&str] =
        &["rust/machine/src/engine/runtime_exec/semantic_state.rs"];

    let adversarial_lifecycle_cases: &[&str] = &[
        "stale_late_result_after_handoff",
        "owner_crash_before_handoff",
        "owner_crash_after_handoff",
        "timeout_vs_cancellation_race",
        "retry_after_terminalization",
        "duplicate_publication_attempt",
        "observed_read_use_on_authoritative_path",
        "missing_canonical_handle_on_parity_critical_path",
        "blocked_progress_escalation",
        "immediate_effect_misuse",
    ];

    let dsl_runtime_semantics_suites: &[&str] = &["rust/tests/dsl_runtime_semantics_tests.rs"];

    let simulator_semantic_contract_categories: &[&str] = &[
        "parity_progress_contracts",
        "exact_once_effect_resolution",
        "canonical_publication_uniqueness",
        "authoritative_observed_separation",
        "progress_escalation_visibility",
        "semantic_object_coherence",
    ];

    let theorem_pack_admission_suites: &[&str] = &[
        "rust/bridge/tests/protocol_bundle_admission_contracts.rs",
        "rust/bridge/tests/invariant_verification.rs",
        "rust/machine/src/runtime_contracts.rs",
        "rust/tests/dsl_runtime_semantics_tests.rs",
    ];

    let distributed_topology_semantic_harness_suites: &[&str] = &[
        "rust/simulator/tests/distributed.rs",
        "rust/machine/tests/topology_effect_ingress.rs",
        "rust/runtime/tests/generated_topology_public_path.rs",
    ];

    let agreement_composition_runtime_semantic_suites: &[&str] = &[
        "rust/machine/src/effect/core_types.rs",
        "rust/machine/src/semantic_objects.rs",
        "rust/machine/tests/threaded_equivalence.rs",
        "rust/tests/dsl_runtime_semantics_tests.rs",
    ];

    let extension_middleware_semantic_hardening_suites: &[&str] = &[
        "rust/runtime/tests/extension_integration.rs",
        "rust/runtime/tests/middleware_semantic_hardening.rs",
    ];

    let generated_topology_transport_public_path_suites: &[&str] =
        &["rust/runtime/tests/generated_topology_public_path.rs"];

    let runtime_substrate_boundary_suites: &[&str] = &[
        "rust/runtime/tests/runtime_substrate_contracts.rs",
        "rust/runtime/tests/wasm_compat.rs",
    ];

    let handler_contract_boundary_suites: &[&str] = &[
        "rust/runtime/tests/handler_contracts.rs",
        "rust/runtime/tests/transport_contracts.rs",
    ];

    let long_horizon_recovery_harness_suites: &[&str] =
        &["rust/bridge/tests/reconfiguration_recovery_harness.rs"];

    let artifact_release_assurance_suites: &[&str] = &[
        "toolkit/xtask/src/checks/package_artifacts.rs",
        "toolkit/xtask/src/checks/package_provenance.rs",
        "toolkit/xtask/src/checks/durable_boundaries (via _toolkit-check)",
        "toolkit/xtask/src/checks/release_recovery.rs",
    ];

    let mutation_fail_closed_assurance_suites: &[&str] = &[
        "rust/machine/src/runtime_contracts.rs",
        "toolkit/xtask/src/checks/fail_closed_mutations.rs",
    ];

    let concrete_protocol_machine_refinement_suites: &[&str] = &[
        "rust/bridge/tests/protocol_machine_differential_steps.rs",
        "rust/machine/tests/lean_protocol_machine_equivalence.rs",
        "rust/machine/tests/threaded_equivalence.rs",
    ];

    let compiler_serialization_pipeline_suites: &[&str] = &[
        "rust/bridge/tests/compiler_pipeline_conformance.rs",
        "rust/bridge/tests/projection_equivalence.rs",
        "rust/bridge/tests/proptest_json_roundtrip.rs",
        "rust/bridge/tests/lean_integration_tests.rs",
        "rust/bridge/tests/merge_semantics_tests.rs",
    ];

    let deadlock_automation_fragment_suites: &[&str] = &[
        "rust/types/src/local.rs",
        "rust/bridge/tests/regular_practical_fragment_checks.rs",
        "rust/tests/dsl_runtime_semantics_tests.rs",
    ];

    let docs_as_contract_assurance_suites: &[&str] = &[
        "rust/bridge/tests/docs_contract_tests.rs",
        "toolkit/xtask/src/checks/verification_inventory.rs",
        "toolkit/xtask/src/checks/bridge_normalization_ledger.rs",
    ];

    let deterministic_scale_budget_assurance_suites: &[&str] =
        &["rust/bridge/tests/scale_budget_contracts.rs"];

    let explicit_unsupported_fail_closed_notes: &[&str] = &[];

    // Compute property bucket coverage
    fn has_coverage(n: u64) -> u64 {
        if n > 0 {
            1
        } else {
            0
        }
    }

    let actual_authority_ownership = count_list(authority_ownership_suites);
    let actual_lean_correspondence_strict = count_list(lean_correspondence_strict_suites);
    let actual_identity_replay = count_list(identity_replay_suites);
    let actual_commitment_progress = count_list(commitment_progress_suites);
    let actual_cross_mode_semantic_parity = count_list(cross_mode_semantic_parity_suites);
    let actual_fail_closed_lowering_admission = count_list(fail_closed_lowering_admission_suites);
    let actual_structure_reconfiguration = count_list(structure_reconfiguration_suites);
    let actual_semantic_lifecycle_invariant = count_list(semantic_lifecycle_invariant_suites);
    let actual_adversarial_lifecycle = count_list(adversarial_lifecycle_cases);
    let actual_dsl_runtime_semantics = count_list(dsl_runtime_semantics_suites);
    let actual_simulator_semantic_contract = count_list(simulator_semantic_contract_categories);
    let actual_theorem_pack_admission = count_list(theorem_pack_admission_suites);
    let actual_distributed_topology = count_list(distributed_topology_semantic_harness_suites);
    let actual_agreement_composition = count_list(agreement_composition_runtime_semantic_suites);
    let actual_extension_middleware = count_list(extension_middleware_semantic_hardening_suites);
    let actual_generated_topology = count_list(generated_topology_transport_public_path_suites);
    let actual_runtime_substrate = count_list(runtime_substrate_boundary_suites);
    let actual_handler_contract = count_list(handler_contract_boundary_suites);
    let actual_long_horizon_recovery = count_list(long_horizon_recovery_harness_suites);
    let actual_artifact_release = count_list(artifact_release_assurance_suites);
    let actual_mutation_fail_closed = count_list(mutation_fail_closed_assurance_suites);
    let actual_concrete_refinement = count_list(concrete_protocol_machine_refinement_suites);
    let actual_compiler_serialization = count_list(compiler_serialization_pipeline_suites);
    let actual_deadlock_automation = count_list(deadlock_automation_fragment_suites);
    let actual_docs_as_contract = count_list(docs_as_contract_assurance_suites);
    let actual_deterministic_scale_budget = count_list(deterministic_scale_budget_assurance_suites);
    let actual_explicit_unsupported = count_list(explicit_unsupported_fail_closed_notes);

    let actual_executable_buckets = has_coverage(actual_authority_ownership)
        + has_coverage(actual_lean_correspondence_strict)
        + has_coverage(actual_identity_replay)
        + has_coverage(actual_commitment_progress)
        + has_coverage(actual_cross_mode_semantic_parity)
        + has_coverage(actual_fail_closed_lowering_admission)
        + has_coverage(actual_structure_reconfiguration)
        + has_coverage(actual_theorem_pack_admission)
        + has_coverage(actual_distributed_topology)
        + has_coverage(actual_agreement_composition)
        + has_coverage(actual_extension_middleware)
        + has_coverage(actual_generated_topology)
        + has_coverage(actual_runtime_substrate)
        + has_coverage(actual_handler_contract)
        + has_coverage(actual_long_horizon_recovery)
        + has_coverage(actual_artifact_release)
        + has_coverage(actual_mutation_fail_closed)
        + has_coverage(actual_concrete_refinement)
        + has_coverage(actual_compiler_serialization)
        + has_coverage(actual_deadlock_automation)
        + has_coverage(actual_docs_as_contract)
        + has_coverage(actual_deterministic_scale_budget);

    let actual_lacking_buckets = 22 - actual_executable_buckets;

    let macro_ui_file = repo_root.join("rust/macros/tests/macro_ui.rs");
    let macro_ui_text = fs::read_to_string(&macro_ui_file)?;
    let actual_pass = macro_ui_text
        .lines()
        .filter(|l| l.contains("t.pass("))
        .count() as u64;
    let actual_fail = macro_ui_text
        .lines()
        .filter(|l| l.contains("t.compile_fail("))
        .count() as u64;

    check_metric(
        "Explicit failure/timeout observable event kinds",
        count_list(explicit_failure_timeout_events),
        &mut errors,
    );
    check_metric("Macro UI pass fixtures", actual_pass, &mut errors);
    check_metric("Macro UI compile-fail fixtures", actual_fail, &mut errors);
    check_metric(
        "Property buckets with executable assurance suites",
        actual_executable_buckets,
        &mut errors,
    );
    check_metric(
        "Property buckets currently lacking executable assurance suites",
        actual_lacking_buckets,
        &mut errors,
    );
    check_metric(
        "Authority and ownership semantic assurance suites",
        actual_authority_ownership,
        &mut errors,
    );
    check_metric(
        "Lean-backed correspondence strict suites",
        actual_lean_correspondence_strict,
        &mut errors,
    );
    check_metric(
        "Identity and replay semantic assurance suites",
        actual_identity_replay,
        &mut errors,
    );
    check_metric(
        "Commitment and progress semantic assurance suites",
        actual_commitment_progress,
        &mut errors,
    );
    check_metric(
        "Cross-mode semantic parity suites",
        actual_cross_mode_semantic_parity,
        &mut errors,
    );
    check_metric(
        "Fail-closed lowering and admission gate suites",
        actual_fail_closed_lowering_admission,
        &mut errors,
    );
    check_metric(
        "Structural locality and reconfiguration executable assurance suites",
        actual_structure_reconfiguration,
        &mut errors,
    );
    check_metric(
        "Semantic lifecycle invariant suites",
        actual_semantic_lifecycle_invariant,
        &mut errors,
    );
    check_metric(
        "Deterministic adversarial lifecycle scenarios",
        actual_adversarial_lifecycle,
        &mut errors,
    );
    check_metric(
        "End-to-end DSL runtime semantic conformance suites",
        actual_dsl_runtime_semantics,
        &mut errors,
    );
    check_metric(
        "Simulator semantic contract categories enforced automatically",
        actual_simulator_semantic_contract,
        &mut errors,
    );
    check_metric(
        "Theorem-pack and admission executable assurance suites",
        actual_theorem_pack_admission,
        &mut errors,
    );
    check_metric(
        "Distributed and topology semantic harness suites",
        actual_distributed_topology,
        &mut errors,
    );
    check_metric(
        "Agreement and composition runtime semantic suites",
        actual_agreement_composition,
        &mut errors,
    );
    check_metric(
        "Extension and middleware semantic hardening suites",
        actual_extension_middleware,
        &mut errors,
    );
    check_metric(
        "Generated topology and transport public-path suites",
        actual_generated_topology,
        &mut errors,
    );
    check_metric(
        "Runtime substrate boundary assurance suites",
        actual_runtime_substrate,
        &mut errors,
    );
    check_metric(
        "Handler contract boundary assurance suites",
        actual_handler_contract,
        &mut errors,
    );
    check_metric(
        "Long-horizon recovery differential harness suites",
        actual_long_horizon_recovery,
        &mut errors,
    );
    check_metric(
        "Artifact and release assurance suites",
        actual_artifact_release,
        &mut errors,
    );
    check_metric(
        "Mutation fail-closed assurance suites",
        actual_mutation_fail_closed,
        &mut errors,
    );
    check_metric(
        "Concrete protocol-machine refinement suites",
        actual_concrete_refinement,
        &mut errors,
    );
    check_metric(
        "Compiler and serialization pipeline suites",
        actual_compiler_serialization,
        &mut errors,
    );
    check_metric(
        "Deadlock automation fragment assurance suites",
        actual_deadlock_automation,
        &mut errors,
    );
    check_metric(
        "Docs-as-contract assurance suites",
        actual_docs_as_contract,
        &mut errors,
    );
    check_metric(
        "Deterministic scale and budget assurance suites",
        actual_deterministic_scale_budget,
        &mut errors,
    );
    check_metric(
        "Explicit unsupported or fail-closed property notes",
        actual_explicit_unsupported,
        &mut errors,
    );

    // Forbidden phrases
    let forbidden_phrases = &[
        "not yet as a full semantic lifecycle harness",
        "still incomplete",
        "load-only Lean output",
        "fail-closed placeholder",
    ];
    for phrase in forbidden_phrases {
        if inventory.contains(phrase) {
            errors.push(format!(
                "docs/902_verification_inventory.md: stale gap phrase remains in inventory: {phrase}"
            ));
        }
    }

    // Gate ownership section
    if !inventory.contains("## Gate Ownership") {
        errors.push(
            "docs/902_verification_inventory.md: missing 'Gate Ownership' section".to_string(),
        );
    }

    let gate_ownership_recipes = &[
        "check-fast-structure",
        "check-focused-assurance",
        "check-package-artifacts",
        "check-pr-critical",
        "check-deep-assurance",
    ];

    for recipe in gate_ownership_recipes {
        // Verify recipe exists in justfile
        if !justfile.contains(&format!("{recipe}:")) {
            errors.push(format!("missing just recipe: {recipe}"));
        }
        let code_span = format!("`just {recipe}`");
        if !inventory.contains(&code_span) {
            errors.push(format!(
                "docs/902_verification_inventory.md: missing gate ownership entry for {recipe}"
            ));
        }
    }

    if !errors.is_empty() {
        let detail = errors.join("\n");
        bail!(
            "verification-inventory: {} error(s)\n{detail}",
            errors.len()
        );
    }

    println!("verification inventory check passed");
    Ok(())
}
