//! Tests for scenario parsing and validation.

use super::*;

#[test]
fn test_parse_mean_field_scenario() {
    // Note: FixedQ32 values must be quoted strings in TOML for deterministic parsing
    let toml = r#"
            name = "mean_field_ising"
            roles = ["A", "B"]
            steps = 1000
            seed = 42

            [field]
            layer = "mean_field"

            [field.params]
            beta = "1.5"
            species = ["up", "down"]
            initial_state = ["0.6", "0.4"]
            step_size = "0.01"
        "#;

    let scenario = Scenario::parse(toml).expect("parse scenario");
    assert_eq!(scenario.name, "mean_field_ising");
    assert_eq!(scenario.roles, vec!["A", "B"]);
    assert_eq!(scenario.steps, 1000);
    assert_eq!(scenario.seed, 42);
    match scenario.field.as_ref().expect("field should parse") {
        FieldSpec::MeanField(mf) => {
            let expected = FixedQ32::from_ratio(3, 2).expect("1.5");
            let eps = FixedQ32::from_ratio(1, 1_000_000).expect("epsilon");
            assert!((mf.beta - expected).abs() < eps);
        }
        _ => panic!("expected MeanField"),
    }
}

#[test]
fn test_default_seed_when_missing() {
    // Note: FixedQ32 values must be quoted strings in TOML for deterministic parsing
    let toml = r#"
            name = "default_seed"
            roles = ["A", "B"]
            steps = 1

            [field]
            layer = "mean_field"

            [field.params]
            beta = "1.0"
            species = ["up", "down"]
            initial_state = ["0.5", "0.5"]
            step_size = "0.01"
        "#;

    let scenario = Scenario::parse(toml).expect("parse scenario");
    assert_eq!(scenario.seed, 0);
    let execution = scenario.resolved_execution().expect("resolve execution");
    assert_eq!(execution.backend, ResolvedExecutionBackend::Canonical);
    assert_eq!(
        execution.scheduler_policy,
        ResolvedSchedulerPolicy::Cooperative
    );
    assert_eq!(execution.scheduler_concurrency, 1);
    assert_eq!(execution.worker_threads, 1);
    assert_eq!(execution.regime(), ExecutionRegime::CanonicalExact);
    let theorem = scenario
        .resolved_theorem_profile()
        .expect("resolve theorem profile");
    assert_eq!(
        theorem.scheduler_profile,
        TheoremSchedulerProfile::CanonicalExact
    );
    assert_eq!(theorem.envelope_profile, TheoremEnvelopeProfile::Exact);
    assert_eq!(
        theorem.assumption_bundle,
        TheoremAssumptionBundle::FaultFreeTransport
    );
    assert_eq!(theorem.eligibility, TheoremEligibility::Exact);
}

#[test]
fn test_parse_durable_wal_scenario() {
    let toml = r#"
            name = "durable_wal"
            roles = ["A", "B"]
            steps = 4
            checkpoint_interval = 2

            [durability]
            mode = "wal"
        "#;

    let scenario = Scenario::parse(toml).expect("parse durable wal scenario");
    assert!(scenario.requires_durable_resume());
    assert_eq!(scenario.durability.mode, DurabilityMode::Wal);
}

#[test]
fn test_parse_generic_scenario_without_field() {
    let toml = r#"
            name = "generic"
            roles = ["A", "B"]
            steps = 4
            seed = 1
        "#;

    let scenario = Scenario::parse(toml).expect("parse generic scenario");
    assert!(scenario.field.is_none());
}

#[test]
fn test_parse_network_link_topology() {
    let toml = r#"
            name = "links"
            roles = ["A", "B", "C"]
            steps = 10

            [field]
            layer = "mean_field"

            [field.params]
            beta = "1.0"
            species = ["up", "down"]
            initial_state = ["0.5", "0.5"]
            step_size = "0.01"

            [network]
            base_latency_ms = 5
            latency_variance = "0.1"
            loss_probability = "0.01"

            [[network.links]]
            from = "A"
            to = "B"
            enabled = true
            base_latency_ms = 25
            latency_variance = "0.2"
            loss_probability = "0.4"

            [[network.links]]
            from = "B"
            to = "C"
            enabled = false
        "#;

    let scenario = Scenario::parse(toml).expect("parse scenario");
    let cfg = scenario.network_config().expect("network config");
    assert_eq!(cfg.links.len(), 2);

    let ab = &cfg.links[0];
    assert_eq!(ab.from, "A");
    assert_eq!(ab.to, "B");
    assert!(ab.enabled);
    assert_eq!(ab.base_latency, Some(Duration::from_millis(25)));
    let expected_loss = FixedQ32::from_ratio(2, 5).expect("0.4");
    let eps = FixedQ32::from_ratio(1, 1_000_000).expect("epsilon");
    assert!(
        (ab.loss_probability.expect("loss") - expected_loss).abs() < eps,
        "expected 0.4 link loss override"
    );

    let bc = &cfg.links[1];
    assert_eq!(bc.from, "B");
    assert_eq!(bc.to, "C");
    assert!(!bc.enabled);
}

#[test]
fn test_parse_reconfiguration_program() {
    let toml = r#"
            name = "reconfiguration_program"
            roles = ["A", "B", "C"]
            steps = 10

            [[reconfigurations]]
            trigger = { at_tick = 2 }
            effect = { kind = "pure" }
            action = { type = "link", from = "A", to = "B", enabled = false }

            [[reconfigurations]]
            trigger = { after_step = 3 }
            effect = { kind = "transition_choreography", budget_cost = 5 }
            action = { type = "mode_transition", roles = ["B", "C"], from_mode = "mesh", to_mode = "relay" }
        "#;

    let scenario = Scenario::parse(toml).expect("parse scenario");
    assert_eq!(scenario.reconfigurations.len(), 2);
    assert!(scenario.requires_network_model());
    let schedule = scenario
        .reconfiguration_schedule()
        .expect("build reconfiguration schedule");
    assert_eq!(schedule.len(), 2);
    assert_eq!(schedule[0].operation_id, "reconfiguration:0");
    assert_eq!(schedule[1].operation_id, "reconfiguration:1");
}

#[test]
fn test_reject_duplicate_roles() {
    let toml = r#"
            name = "dup_roles"
            roles = ["A", "A"]
            steps = 1

            [field]
            layer = "mean_field"

            [field.params]
            beta = "1.0"
            species = ["up", "down"]
            initial_state = ["0.5", "0.5"]
            step_size = "0.01"
        "#;

    let error = Scenario::parse(toml).expect_err("duplicate roles must fail");
    assert!(error.contains("duplicate role"));
}

#[test]
fn test_reject_zero_concurrency() {
    let toml = r#"
            name = "bad_concurrency"
            roles = ["A", "B"]
            steps = 1

            [execution]
            scheduler_concurrency = 0

            [field]
            layer = "mean_field"

            [field.params]
            beta = "1.0"
            species = ["up", "down"]
            initial_state = ["0.5", "0.5"]
            step_size = "0.01"
        "#;

    let error = Scenario::parse(toml).expect_err("zero scheduler concurrency must fail");
    assert!(error.contains("concurrency"));
}

#[test]
fn test_auto_execution_serializes_in_ci_environment() {
    let spec = ExecutionSpec::default();
    let resolved = spec
        .resolve_for(ExecutionEnvironment {
            available_parallelism: 8,
            threaded_available: true,
        })
        .expect("resolve execution");
    assert_eq!(resolved.backend, ResolvedExecutionBackend::Canonical);
    assert_eq!(
        resolved.scheduler_policy,
        ResolvedSchedulerPolicy::Cooperative
    );
    assert_eq!(resolved.scheduler_concurrency, 1);
    assert_eq!(resolved.worker_threads, 1);
}

#[test]
fn test_auto_execution_defaults_to_authoritative_serialized_outside_ci() {
    let spec = ExecutionSpec::default();
    let resolved = spec
        .resolve_for(ExecutionEnvironment {
            available_parallelism: 6,
            threaded_available: true,
        })
        .expect("resolve execution");
    assert_eq!(resolved.backend, ResolvedExecutionBackend::Canonical);
    assert_eq!(
        resolved.scheduler_policy,
        ResolvedSchedulerPolicy::Cooperative
    );
    assert_eq!(resolved.scheduler_concurrency, 1);
    assert_eq!(resolved.worker_threads, 1);
}

#[test]
fn test_explicit_threaded_execution_keeps_parallel_defaults() {
    let spec = ExecutionSpec {
        backend: ExecutionBackend::Threaded,
        scheduler_policy: SchedulerPolicySpec::Auto,
        scheduler_concurrency: None,
        worker_threads: None,
    };
    let resolved = spec
        .resolve_for(ExecutionEnvironment {
            available_parallelism: 6,
            threaded_available: true,
        })
        .expect("resolve execution");
    assert_eq!(resolved.backend, ResolvedExecutionBackend::Threaded);
    assert_eq!(
        resolved.scheduler_policy,
        ResolvedSchedulerPolicy::Cooperative
    );
    assert_eq!(resolved.scheduler_concurrency, 6);
    assert_eq!(resolved.worker_threads, 6);
    assert_eq!(resolved.regime(), ExecutionRegime::ThreadedEnvelopeBounded);
}

#[test]
fn test_explicit_scheduler_policy_resolves() {
    let spec = ExecutionSpec {
        backend: ExecutionBackend::Canonical,
        scheduler_policy: SchedulerPolicySpec::ProgressAware,
        scheduler_concurrency: Some(1),
        worker_threads: Some(1),
    };
    let resolved = spec
        .resolve_for(ExecutionEnvironment {
            available_parallelism: 4,
            threaded_available: true,
        })
        .expect("resolve execution");
    assert_eq!(
        resolved.scheduler_policy,
        ResolvedSchedulerPolicy::ProgressAware
    );
}

#[test]
fn test_threaded_execution_regime_is_exact_at_scheduler_concurrency_one() {
    let spec = ExecutionSpec {
        backend: ExecutionBackend::Threaded,
        scheduler_policy: SchedulerPolicySpec::Auto,
        scheduler_concurrency: Some(1),
        worker_threads: Some(4),
    };
    let resolved = spec
        .resolve_for(ExecutionEnvironment {
            available_parallelism: 8,
            threaded_available: true,
        })
        .expect("resolve execution");
    assert_eq!(resolved.regime(), ExecutionRegime::ThreadedExact);
}

#[test]
fn test_explicit_theorem_profile_can_make_the_same_execution_ineligible() {
    let toml = r#"
            name = "theorem_profile_conflict"
            roles = ["A", "B"]
            steps = 1

            [execution]
            backend = "canonical"
            scheduler_concurrency = 1
            worker_threads = 1

            [theorem]
            scheduler_profile = "threaded_envelope"
            envelope_profile = "protocol_machine_envelope_adherence"
            assumption_bundle = "fault_free_transport"

            [field]
            layer = "mean_field"

            [field.params]
            beta = "1.0"
            species = ["up", "down"]
            initial_state = ["0.5", "0.5"]
            step_size = "0.01"
        "#;

    let scenario = Scenario::parse(toml).expect("parse scenario");
    let theorem = scenario
        .resolved_theorem_profile()
        .expect("resolve theorem profile");

    assert_eq!(
        theorem.scheduler_profile,
        TheoremSchedulerProfile::ThreadedEnvelope
    );
    assert_eq!(
        theorem.envelope_profile,
        TheoremEnvelopeProfile::ProtocolMachineEnvelopeAdherence
    );
    assert_eq!(
        theorem.assumption_bundle,
        TheoremAssumptionBundle::FaultFreeTransport
    );
    assert_eq!(theorem.eligibility, TheoremEligibility::Ineligible);
    assert!(theorem
        .eligibility_reason
        .expect("eligibility reason")
        .contains("threaded_envelope"));
}

#[test]
fn test_reject_delegation_with_identical_roles() {
    let toml = r#"
            name = "bad_reconfiguration"
            roles = ["A", "B"]
            steps = 1

            [[reconfigurations]]
            trigger = { immediate = true }
            action = { type = "delegation", scope = "owner", from_role = "A", to_role = "A" }
        "#;

    let error = Scenario::parse(toml).expect_err("identical delegation roles must fail");
    assert!(error.contains("delegation"));
}

#[test]
fn test_reject_unknown_link_role() {
    let toml = r#"
            name = "bad_link_role"
            roles = ["A", "B"]
            steps = 1

            [field]
            layer = "mean_field"

            [field.params]
            beta = "1.0"
            species = ["up", "down"]
            initial_state = ["0.5", "0.5"]
            step_size = "0.01"

            [network]
            base_latency_ms = 1

            [[network.links]]
            from = "A"
            to = "C"
            enabled = true
        "#;

    let error = Scenario::parse(toml).expect_err("unknown link role must fail");
    assert!(error.contains("unknown to-role"));
}

#[test]
fn core_scenario_schema_remains_domain_neutral() {
    let source = std::fs::read_to_string(
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/scenario.rs"),
    )
    .expect("read scenario source");
    for banned in [
        "bluetooth",
        "ble",
        "wifi",
        "lte",
        "quic",
        "zigbee",
        "satellite",
    ] {
        assert!(
            !source.contains(&format!("pub {banned}:"))
                && !source.contains(&format!("pub {banned}_"))
                && !source.contains(&format!("#[serde(rename = \"{banned}\"")),
            "core scenario schema should not expose domain-branded field `{banned}`",
        );
    }
}

#[test]
fn invalid_execution_combinations_fail_closed_with_stable_reasons() {
    let cases = [
        (
            "canonical_parallelism_rejected",
            r#"
name = "canonical_parallelism_rejected"
roles = ["A", "B"]
steps = 1

[execution]
backend = "canonical"
scheduler_concurrency = 2
worker_threads = 1
"#,
            "canonical simulator backend requires scheduler_concurrency = 1 and worker_threads = 1",
        ),
        (
            "canonical_workers_rejected",
            r#"
name = "canonical_workers_rejected"
roles = ["A", "B"]
steps = 1

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 2
"#,
            "canonical simulator backend requires scheduler_concurrency = 1 and worker_threads = 1",
        ),
        (
            "threaded_checkpoint_rejected",
            r#"
name = "threaded_checkpoint_rejected"
roles = ["A", "B"]
steps = 1
checkpoint_interval = 1

[execution]
backend = "threaded"
scheduler_concurrency = 1
worker_threads = 2
"#,
            "scenario checkpoints currently require the canonical simulator backend",
        ),
        (
            "exact_envelope_overclaim_rejected",
            r#"
name = "exact_envelope_overclaim_rejected"
roles = ["A", "B"]
steps = 1

[execution]
backend = "threaded"
scheduler_concurrency = 2
worker_threads = 2

[theorem]
envelope_profile = "exact"
"#,
            "envelope profile exact requires an exact execution regime",
        ),
    ];

    for (name, source, expected) in cases {
        if name == "exact_envelope_overclaim_rejected" {
            let scenario =
                Scenario::parse(source).expect("ineligible theorem profile should still parse");
            let theorem = scenario
                .resolved_theorem_profile()
                .expect("resolve theorem profile");
            assert_eq!(theorem.eligibility, TheoremEligibility::Ineligible);
            assert!(
                theorem
                    .eligibility_reason
                    .as_deref()
                    .is_some_and(|reason| reason.contains(expected)),
                "case `{name}` should report stable theorem ineligibility reason",
            );
        } else {
            let error = Scenario::parse(source).unwrap_err();
            assert!(
                error.contains(expected),
                "case `{name}` should fail closed with reason containing `{expected}`, got `{error}`",
            );
        }
    }
}
