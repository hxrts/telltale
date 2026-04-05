//! Simulator durability fault-injection and parity assurance tests.

use std::collections::BTreeMap;

use telltale_machine::coroutine::Value;
use telltale_machine::model::durability::{
    AgreementWal, AgreementWalArtifact, AgreementWalEntry, EvidenceOutcomeCacheArtifact,
    EvidenceOutcomeCacheEntry, InMemoryAgreementWal, WalSyncRequest,
};
use telltale_machine::model::effects::{
    EffectExchangeRecord, EffectFailure, EffectHandler, EffectOutcome, EffectRequest,
    EffectResponse, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_simulator::durability::{
    durable_property_report, inspect_durable_artifacts, monitor_evidence_consistency,
    monitor_monotonic_wal_levels, monitor_recovery_equivalence, monitor_write_ahead,
    run_durable_recovery_case, DurableFaultKind, DurableFaultOutcome, DurableFaultProgram,
    DurableWalEntryKind, FaultInjectingAgreementWal, ScheduledDurableFault,
};
use telltale_simulator::runner::{
    resume_with_durable_checkpoint_artifact, run_canonical_replay, run_with_scenario,
    DurableResumeArtifacts,
};
use telltale_simulator::scenario::{DurabilityMode, Scenario};
use telltale_types::{GlobalType, Label, LocalTypeR};

#[derive(Debug, Clone, Copy)]
struct PassthroughHandler;

impl EffectHandler for PassthroughHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Str(label.to_string()))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> EffectResult<String> {
        match labels.first().cloned() {
            Some(label) => EffectResult::success(label),
            None => EffectResult::failure(EffectFailure::invalid_input("no labels available")),
        }
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }
}

fn loop_protocol() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::mu(
        "loop",
        GlobalType::send(
            "A",
            "B",
            Label::new("msg"),
            GlobalType::send("B", "A", Label::new("ack"), GlobalType::var("loop")),
        ),
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(
                    Label::new("msg"),
                    None,
                    LocalTypeR::Recv {
                        partner: "B".into(),
                        branches: vec![(Label::new("ack"), None, LocalTypeR::var("loop"))],
                    },
                )],
            },
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(
                    Label::new("msg"),
                    None,
                    LocalTypeR::Send {
                        partner: "A".into(),
                        branches: vec![(Label::new("ack"), None, LocalTypeR::var("loop"))],
                    },
                )],
            },
        ),
    );

    (global, local_types)
}

fn scenario_name(prefix: &str) -> String {
    format!("{prefix}_{}", std::process::id())
}

fn durable_scenario(name: &str) -> Scenario {
    let toml = format!(
        r#"
name = "{name}"
roles = ["A", "B"]
steps = 14
seed = 41
checkpoint_interval = 2

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[theorem]
assumption_bundle = "observed_transport"

[durability]
mode = "wal"

[network]
base_latency_ms = 1
latency_variance = "0.0"
loss_probability = "0.0"

[[adversaries]]
id = "timing_once"
trigger = {{ at_tick = 2 }}
action = {{ type = "timing_disturbance", ticks = 1 }}
budget = {{ total = 1, mode = "activation", assumption_failure = "fairness_failure" }}

[[reconfigurations]]
trigger = {{ at_tick = 1 }}
action = {{ type = "handoff", handoff_id = "handoff#1", from_role = "A", to_role = "B" }}

[field]
layer = "mean_field"

[field.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"
"#
    );
    let scenario = Scenario::parse(&toml).expect("parse durable scenario");
    assert_eq!(scenario.durability.mode, DurabilityMode::Wal);
    scenario
}

fn assert_authoritative_equivalence(
    left: &telltale_simulator::runner::ScenarioResult,
    right: &telltale_simulator::runner::ScenarioResult,
) {
    assert_eq!(left.replay.theorem_profile, right.replay.theorem_profile);
    assert_eq!(left.replay.obs_trace, right.replay.obs_trace);
    assert_eq!(left.replay.effect_exchanges, right.replay.effect_exchanges);
    assert_eq!(
        left.replay.output_condition_trace,
        right.replay.output_condition_trace
    );
    assert_eq!(
        left.replay.semantic_audit_log,
        right.replay.semantic_audit_log
    );
    assert_eq!(left.replay.semantic_objects, right.replay.semantic_objects);
    assert_eq!(
        left.replay.reconfiguration_trace,
        right.replay.reconfiguration_trace
    );
    assert_eq!(
        left.replay.environment_trace,
        right.replay.environment_trace
    );
}

fn synthetic_wal_sync_exchange(operation_id: &str, tick: u64) -> EffectExchangeRecord {
    let sync = WalSyncRequest {
        operation_id: operation_id.to_string(),
        downstream_coroutine_id: "coro:0".to_string(),
        gate_level: telltale_machine::AgreementLevel::SoftSafe,
        agreement_state: None,
        agreement_evidence: Vec::new(),
        tick,
    };
    EffectExchangeRecord {
        effect_id: 0,
        handler_identity: "agreement_wal".to_string(),
        ordering_key: tick,
        request: EffectRequest::wal_sync(tick, operation_id.to_string(), sync),
        outcome: EffectOutcome::success(EffectResponse::WalSync),
    }
}

#[test]
fn fault_injecting_wal_supports_failure_latency_partial_write_and_unavailability() {
    let entry = AgreementWalEntry::Escalation {
        operation_id: "durable:op".to_string(),
        previous_level: telltale_machine::AgreementLevel::Provisional,
        new_level: telltale_machine::AgreementLevel::SoftSafe,
        evidence_id: Some("ev#1".to_string()),
        tick: 3,
    };

    let mut delayed = FaultInjectingAgreementWal::new(
        InMemoryAgreementWal::new(),
        DurableFaultProgram {
            faults: vec![ScheduledDurableFault {
                tick: 3,
                kind: DurableFaultKind::Latency { ticks: 5 },
            }],
        },
    );
    delayed
        .append(entry.clone())
        .expect("delayed append succeeds");
    assert_eq!(
        delayed.history()[0].outcome,
        DurableFaultOutcome::Delayed { ticks: 5 }
    );

    let mut failed = FaultInjectingAgreementWal::new(
        InMemoryAgreementWal::new(),
        DurableFaultProgram {
            faults: vec![ScheduledDurableFault {
                tick: 3,
                kind: DurableFaultKind::WriteFailure,
            }],
        },
    );
    let err = failed.append(entry.clone()).expect_err("write failure");
    assert!(err.contains("write failure"));

    let mut partial = FaultInjectingAgreementWal::new(
        InMemoryAgreementWal::new(),
        DurableFaultProgram {
            faults: vec![ScheduledDurableFault {
                tick: 3,
                kind: DurableFaultKind::PartialWrite,
            }],
        },
    );
    let err = partial.append(entry.clone()).expect_err("partial write");
    assert!(err.contains("partial write"));

    let mut unavailable = FaultInjectingAgreementWal::new(
        InMemoryAgreementWal::new(),
        DurableFaultProgram {
            faults: vec![ScheduledDurableFault {
                tick: 0,
                kind: DurableFaultKind::AvailabilityWindow {
                    start_tick: 2,
                    end_tick: 4,
                },
            }],
        },
    );
    let err = unavailable
        .append(entry)
        .expect_err("availability window should reject append");
    assert!(err.contains("unavailable"));
}

#[test]
fn durable_agreement_level_matrix_is_exercised_via_resume_summary() {
    let (global, local_types) = loop_protocol();
    let scenario = durable_scenario(&scenario_name("phase23_durable_matrix"));
    let cases = [
        ("none", AgreementWalArtifact::default(), None),
        (
            "provisional",
            AgreementWalArtifact {
                entries: vec![AgreementWalEntry::Escalation {
                    operation_id: "durable:prov".to_string(),
                    previous_level: telltale_machine::AgreementLevel::None,
                    new_level: telltale_machine::AgreementLevel::Provisional,
                    evidence_id: Some("prov#1".to_string()),
                    tick: 5,
                }],
            },
            Some(telltale_machine::DurableRecoveryAction::ReexecuteFromScratch),
        ),
        (
            "softsafe",
            AgreementWalArtifact {
                entries: vec![AgreementWalEntry::Escalation {
                    operation_id: "durable:soft".to_string(),
                    previous_level: telltale_machine::AgreementLevel::Provisional,
                    new_level: telltale_machine::AgreementLevel::SoftSafe,
                    evidence_id: Some("soft#1".to_string()),
                    tick: 5,
                }],
            },
            Some(telltale_machine::DurableRecoveryAction::ResumeFromEvidenceBoundary),
        ),
        (
            "finalized",
            AgreementWalArtifact {
                entries: vec![AgreementWalEntry::Finalization {
                    operation_id: "durable:final".to_string(),
                    outcome: telltale_machine::FinalizationOutcome::Finalized,
                    materialization_proof_id: Some("proof#1".to_string()),
                    canonical_handle_id: Some("handle#1".to_string()),
                    tick: 5,
                }],
            },
            Some(telltale_machine::DurableRecoveryAction::ReuseFinalized),
        ),
        (
            "timed_out",
            AgreementWalArtifact {
                entries: vec![AgreementWalEntry::Finalization {
                    operation_id: "durable:terminal".to_string(),
                    outcome: telltale_machine::FinalizationOutcome::TimedOut,
                    materialization_proof_id: None,
                    canonical_handle_id: None,
                    tick: 5,
                }],
            },
            Some(telltale_machine::DurableRecoveryAction::PreserveTerminal),
        ),
    ];

    for (label, wal, expected_action) in cases {
        let recovery = run_durable_recovery_case(
            &local_types,
            &global,
            &BTreeMap::new(),
            &scenario,
            &PassthroughHandler,
            None,
            4,
            &DurableResumeArtifacts {
                wal,
                evidence_cache: EvidenceOutcomeCacheArtifact::default(),
            },
        )
        .unwrap_or_else(|err| panic!("run durable recovery case {label}: {err}"));
        let summary = recovery
            .resumed
            .stats
            .durable_recovery
            .as_ref()
            .expect("durable summary");
        assert_eq!(
            summary.execution_regime,
            recovery.resumed.stats.execution_regime
        );
        assert_eq!(
            summary.theorem_profile,
            recovery.resumed.stats.theorem_profile
        );
        match expected_action {
            Some(action) => assert!(
                summary
                    .decisions
                    .iter()
                    .any(|decision| decision.action == action),
                "expected action {action:?} in {label}"
            ),
            None => assert!(summary.decisions.is_empty()),
        }
    }
}

#[test]
fn durable_property_monitors_cover_write_ahead_monotonicity_evidence_and_equivalence() {
    let (global, local_types) = loop_protocol();
    let scenario = durable_scenario(&scenario_name("phase23_durable_properties"));
    let wal = AgreementWalArtifact {
        entries: vec![
            AgreementWalEntry::Escalation {
                operation_id: "durable:soft".to_string(),
                previous_level: telltale_machine::AgreementLevel::Provisional,
                new_level: telltale_machine::AgreementLevel::SoftSafe,
                evidence_id: Some("soft#1".to_string()),
                tick: 5,
            },
            AgreementWalEntry::VisibilityGateCrossing {
                operation_id: "durable:soft".to_string(),
                downstream_coroutine_id: "coro:0".to_string(),
                gate_level: telltale_machine::AgreementLevel::SoftSafe,
                tick: 5,
            },
        ],
    };
    let recovery = run_durable_recovery_case(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
        None,
        4,
        &DurableResumeArtifacts {
            wal: AgreementWalArtifact::default(),
            evidence_cache: EvidenceOutcomeCacheArtifact::default(),
        },
    )
    .expect("recovery case");
    let report = durable_property_report(
        &wal,
        &EvidenceOutcomeCacheArtifact {
            entries: vec![EvidenceOutcomeCacheEntry {
                evidence_id: "soft#1".to_string(),
                interface_name: "Storage".to_string(),
                operation_name: "write".to_string(),
                outcome: EffectOutcome::success(EffectResponse::Release),
            }],
        },
        &[synthetic_wal_sync_exchange("durable:soft", 5)],
        &recovery.uninterrupted,
        &recovery.resumed,
    );

    assert!(report.write_ahead);
    assert!(report.monotonic_wal_levels);
    assert!(report.evidence_consistency);
    assert!(report.recovery_equivalence);
    assert!(report.violations.is_empty());
}

#[test]
fn durable_execution_parity_holds_across_direct_replay_and_resume_lanes() {
    let (global, local_types) = loop_protocol();
    let scenario = durable_scenario(&scenario_name("phase23_durable_parity"));
    let direct = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
    )
    .expect("direct durable run");
    let replay = run_canonical_replay(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
    )
    .expect("canonical replay");
    let recovery = run_durable_recovery_case(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
        None,
        4,
        &DurableResumeArtifacts {
            wal: AgreementWalArtifact::default(),
            evidence_cache: EvidenceOutcomeCacheArtifact::default(),
        },
    )
    .expect("durable recovery");

    assert_authoritative_equivalence(&direct, &replay);
    assert_authoritative_equivalence(&direct, &recovery.resumed);
}

#[test]
fn durable_property_monitors_fail_closed_with_precise_diagnostics() {
    let missing_sync_wal = AgreementWalArtifact {
        entries: vec![AgreementWalEntry::VisibilityGateCrossing {
            operation_id: "durable:gate".to_string(),
            downstream_coroutine_id: "coro:0".to_string(),
            gate_level: telltale_machine::AgreementLevel::SoftSafe,
            tick: 5,
        }],
    };
    let write_ahead = monitor_write_ahead(&missing_sync_wal, &[]);
    assert!(write_ahead.is_err());
    assert!(write_ahead
        .expect_err("missing wal_sync should fail")
        .contains("durable:gate"));

    let regressed_wal = AgreementWalArtifact {
        entries: vec![AgreementWalEntry::Escalation {
            operation_id: "durable:regress".to_string(),
            previous_level: telltale_machine::AgreementLevel::Finalized,
            new_level: telltale_machine::AgreementLevel::SoftSafe,
            evidence_id: Some("regress#1".to_string()),
            tick: 4,
        }],
    };
    let monotonic = monitor_monotonic_wal_levels(&regressed_wal);
    assert!(monotonic.is_err());
    assert!(monotonic
        .expect_err("regressed wal should fail")
        .contains("regression"));

    let consistent_wal = AgreementWalArtifact {
        entries: vec![AgreementWalEntry::EvidenceProduced {
            evidence: telltale_machine::AgreementEvidence {
                evidence_id: "known#1".to_string(),
                operation_id: "durable:known".to_string(),
                session: None,
                owner_id: None,
                level: telltale_machine::AgreementLevel::SoftSafe,
                kind: telltale_machine::AgreementEvidenceKind::CommitFact,
                reference: "commit://known#1".to_string(),
                authoritative: true,
            },
            tick: 4,
        }],
    };
    let inconsistent_cache = EvidenceOutcomeCacheArtifact {
        entries: vec![EvidenceOutcomeCacheEntry {
            evidence_id: "missing#1".to_string(),
            interface_name: "Storage".to_string(),
            operation_name: "write".to_string(),
            outcome: EffectOutcome::success(EffectResponse::Release),
        }],
    };
    let evidence_consistency = monitor_evidence_consistency(&consistent_wal, &inconsistent_cache);
    assert!(evidence_consistency.is_err());
    assert!(evidence_consistency
        .expect_err("missing evidence should fail")
        .contains("missing#1"));

    let (global, local_types) = loop_protocol();
    let scenario = durable_scenario(&scenario_name("phase24_monitor_failures"));
    let recovery = run_durable_recovery_case(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
        None,
        4,
        &DurableResumeArtifacts {
            wal: AgreementWalArtifact::default(),
            evidence_cache: EvidenceOutcomeCacheArtifact::default(),
        },
    )
    .expect("recovery case");
    let mut drifted = recovery.resumed.clone();
    drifted.replay.theorem_profile.eligibility_reason = Some("drift".to_string());
    let recovery_equivalence = monitor_recovery_equivalence(&recovery.uninterrupted, &drifted);
    assert!(recovery_equivalence.is_err());
    assert!(recovery_equivalence
        .expect_err("drifted replay should fail")
        .contains("theorem profile drifted"));
}

#[test]
fn inspect_durable_artifacts_projects_every_entry_family_and_recovery_summary() {
    let wal = AgreementWalArtifact {
        entries: vec![
            AgreementWalEntry::Escalation {
                operation_id: "durable:escalate".to_string(),
                previous_level: telltale_machine::AgreementLevel::Provisional,
                new_level: telltale_machine::AgreementLevel::SoftSafe,
                evidence_id: Some("soft#1".to_string()),
                tick: 3,
            },
            AgreementWalEntry::EvidenceProduced {
                evidence: telltale_machine::AgreementEvidence {
                    evidence_id: "soft#1".to_string(),
                    operation_id: "durable:escalate".to_string(),
                    session: None,
                    owner_id: None,
                    level: telltale_machine::AgreementLevel::SoftSafe,
                    kind: telltale_machine::AgreementEvidenceKind::CommitFact,
                    reference: "commit://soft#1".to_string(),
                    authoritative: true,
                },
                tick: 3,
            },
            AgreementWalEntry::Finalization {
                operation_id: "durable:final".to_string(),
                outcome: telltale_machine::FinalizationOutcome::Finalized,
                materialization_proof_id: Some("proof#1".to_string()),
                canonical_handle_id: Some("handle#1".to_string()),
                tick: 4,
            },
            AgreementWalEntry::VisibilityGateCrossing {
                operation_id: "durable:gate".to_string(),
                downstream_coroutine_id: "coro:0".to_string(),
                gate_level: telltale_machine::AgreementLevel::Finalized,
                tick: 5,
            },
        ],
    };
    let evidence_cache = EvidenceOutcomeCacheArtifact {
        entries: vec![EvidenceOutcomeCacheEntry {
            evidence_id: "soft#1".to_string(),
            interface_name: "Storage".to_string(),
            operation_name: "write".to_string(),
            outcome: EffectOutcome::success(EffectResponse::Release),
        }],
    };
    let (global, local_types) = loop_protocol();
    let scenario = durable_scenario(&scenario_name("phase24_durable_projection"));
    let recovery = run_durable_recovery_case(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
        None,
        4,
        &DurableResumeArtifacts {
            wal: wal.clone(),
            evidence_cache: evidence_cache.clone(),
        },
    )
    .expect("recovery case");
    let summary = recovery
        .resumed
        .stats
        .durable_recovery
        .as_ref()
        .expect("durable recovery summary");

    let report = inspect_durable_artifacts(&wal, &evidence_cache, Some(summary));
    assert_eq!(report.wal_entries.len(), 4);
    assert_eq!(
        report
            .wal_entries
            .iter()
            .map(|entry| entry.kind.clone())
            .collect::<Vec<_>>(),
        vec![
            DurableWalEntryKind::Escalation,
            DurableWalEntryKind::EvidenceProduced,
            DurableWalEntryKind::Finalization,
            DurableWalEntryKind::VisibilityGateCrossing,
        ]
    );
    assert_eq!(
        report
            .wal_entries
            .iter()
            .map(|entry| entry.operation_id.clone())
            .collect::<Vec<_>>(),
        vec![
            "durable:escalate".to_string(),
            "durable:escalate".to_string(),
            "durable:final".to_string(),
            "durable:gate".to_string(),
        ]
    );
    assert_eq!(report.evidence_cache_entries.len(), 1);
    assert_eq!(report.evidence_cache_entries[0].evidence_id, "soft#1");
    let projected_recovery = report.recovery.expect("recovery summary");
    assert_eq!(
        projected_recovery.execution_regime,
        summary.execution_regime
    );
    assert_eq!(projected_recovery.theorem_profile, summary.theorem_profile);
    assert_eq!(projected_recovery.decisions, summary.decisions);
}

#[test]
fn repeated_durable_resume_is_idempotent_for_the_same_checkpoint_and_wal_suffix() {
    let (global, local_types) = loop_protocol();
    let scenario = durable_scenario(&scenario_name("phase24_durable_idempotent"));
    let full = run_with_scenario(
        &local_types,
        &global,
        &BTreeMap::new(),
        &scenario,
        &PassthroughHandler,
    )
    .expect("full durable run");
    let checkpoint = full
        .replay
        .checkpoints
        .iter()
        .find(|checkpoint| checkpoint.tick == 4)
        .expect("checkpoint at tick 4");
    let durable = DurableResumeArtifacts {
        wal: AgreementWalArtifact {
            entries: vec![
                AgreementWalEntry::Escalation {
                    operation_id: "durable:soft".to_string(),
                    previous_level: telltale_machine::AgreementLevel::Provisional,
                    new_level: telltale_machine::AgreementLevel::SoftSafe,
                    evidence_id: Some("soft#1".to_string()),
                    tick: 5,
                },
                AgreementWalEntry::Finalization {
                    operation_id: "durable:soft".to_string(),
                    outcome: telltale_machine::FinalizationOutcome::Finalized,
                    materialization_proof_id: Some("proof#soft".to_string()),
                    canonical_handle_id: None,
                    tick: 5,
                },
            ],
        },
        evidence_cache: EvidenceOutcomeCacheArtifact {
            entries: vec![EvidenceOutcomeCacheEntry {
                evidence_id: "soft#1".to_string(),
                interface_name: "Storage".to_string(),
                operation_name: "write".to_string(),
                outcome: EffectOutcome::success(EffectResponse::Release),
            }],
        },
    };

    let resumed_once = resume_with_durable_checkpoint_artifact(
        &scenario,
        checkpoint,
        &durable,
        &PassthroughHandler,
        None,
        None,
    )
    .expect("first durable resume");
    let resumed_twice = resume_with_durable_checkpoint_artifact(
        &scenario,
        checkpoint,
        &durable,
        &PassthroughHandler,
        None,
        None,
    )
    .expect("second durable resume");

    assert_authoritative_equivalence(&resumed_once, &resumed_twice);
    assert_eq!(
        resumed_once.stats.durable_recovery,
        resumed_twice.stats.durable_recovery
    );
}
