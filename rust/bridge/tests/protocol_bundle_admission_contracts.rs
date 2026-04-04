#![allow(clippy::expect_used)]
//! Admission contract enforcement for protocol bundles.

#[path = "test_choreographies/mod.rs"]
mod test_choreographies;

use std::collections::BTreeMap;
use std::sync::Arc;

use telltale_bridge::{
    export_protocol_bundle, DistributedClaims, InvariantClaims, ProtocolEnvelopeBridgeConfig,
    ProtocolMachineEnvelopeAdherenceConfig, ProtocolMachineEnvelopeAdmissionConfig,
    ProtocolMachineRunner, QuorumSystemKind, ReconfigurationConfig,
};
use telltale_machine::determinism::DeterminismMode;
use telltale_machine::output_condition::OutputConditionPolicy;
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{
    enforce_protocol_machine_runtime_gates, runtime_capability_snapshot, runtime_execution_profile,
    ComposedRuntime, CompositionCertificate, CompositionError, DeterminismCapability, MemoryBudget,
    ProtocolBundle as MachineProtocolBundle, ProtocolMachineAdmissibilityClass,
    ProtocolMachineConfig, ProtocolMachineEscalationWindowClass, ProtocolMachineFairnessAssumption,
    ReconfigurationPlan, ReconfigurationPlanStep, RuntimeCapability, RuntimeContracts,
    RuntimeGateResult, SchedPolicy, SchedulerCapability, TheoremPackCapabilities,
};
use telltale_runtime::{Region, RoleName, Topology, TopologyEndpoint};
use telltale_types::{GlobalType, Label, LocalTypeR};

fn simple_protocol() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::send("A", "B", Label::new("Ping"), GlobalType::End);
    let mut locals = BTreeMap::new();
    locals.insert(
        "A".to_string(),
        LocalTypeR::send("B", Label::new("Ping"), LocalTypeR::End),
    );
    locals.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new("Ping"), LocalTypeR::End),
    );
    (global, locals)
}

fn simple_image() -> Arc<CodeImage> {
    let (global, locals) = simple_protocol();
    Arc::new(CodeImage::from_local_types(&locals, &global))
}

fn exported_bundle(claims: InvariantClaims) -> telltale_bridge::ProtocolBundle {
    let (global, locals) = simple_protocol();
    export_protocol_bundle(&global, &locals, claims)
}

fn admit_public_bundle(
    cfg: ProtocolMachineConfig,
    theorem_pack: TheoremPackCapabilities,
    runtime_contracts: Option<RuntimeContracts>,
) -> Result<(), CompositionError> {
    let bundle = MachineProtocolBundle::new(
        simple_image(),
        CompositionCertificate {
            artifact_id: "cert/public-runtime-gate".to_string(),
            link_ok_full: true,
            theorem_pack,
            runtime_contracts,
        },
    );
    let mut runtime = ComposedRuntime::new(cfg, MemoryBudget::default());
    runtime.admit_bundle(bundle)
}

fn eligibility_value(caps: &TheoremPackCapabilities, key: &str) -> bool {
    caps.execution_profile()
        .theorem_pack_eligibility
        .iter()
        .find_map(|(eligibility_key, enabled)| (eligibility_key == key).then_some(*enabled))
        .unwrap_or(false)
}

fn local_claim_consistency(claims: &InvariantClaims) -> Result<(), &'static str> {
    let distributed = &claims.distributed;

    if let Some(quorum) = &distributed.quorum_geometry {
        if quorum.quorum_size == 0
            || quorum.n == 0
            || quorum.quorum_size > quorum.n
            || quorum.intersection_size > quorum.quorum_size
        {
            return Err("quorum_geometry");
        }
        if matches!(quorum.quorum_system, QuorumSystemKind::Majority)
            && (quorum.intersection_size == 0 || quorum.quorum_size.saturating_mul(2) <= quorum.n)
        {
            return Err("quorum_geometry");
        }
    }

    if let Some(partial_synchrony) = &distributed.partial_synchrony {
        if matches!(
            partial_synchrony.timing,
            telltale_bridge::TimingModel::Asynchronous
        ) && partial_synchrony.delta_bound.is_none()
            && distributed.responsiveness.is_some()
        {
            return Err("partial_synchrony");
        }
    }

    let bridge_enabled = distributed
        .protocol_envelope_bridge
        .as_ref()
        .is_some_and(|config| config.enabled);
    let adherence_enabled = distributed
        .protocol_machine_envelope_adherence
        .as_ref()
        .is_some_and(|config| config.enabled);
    let admission_enabled = distributed
        .protocol_machine_envelope_admission
        .as_ref()
        .is_some_and(|config| config.enabled);
    if bridge_enabled && (!adherence_enabled || !admission_enabled) {
        return Err("protocol_envelope_bridge");
    }

    Ok(())
}

fn strict_protocol_machine_runner_required() -> bool {
    std::env::var("TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER")
        .map(|value| value != "0")
        .unwrap_or(false)
}

fn protocol_machine_runner() -> ProtocolMachineRunner {
    if strict_protocol_machine_runner_required() {
        ProtocolMachineRunner::require_available();
    }
    ProtocolMachineRunner::try_new().expect(
        "Lean protocol-machine runner must be available for reconfiguration admission tests",
    )
}

#[test]
fn protocol_bundle_export_and_runtime_admission_agree_on_protocol_machine_capabilities() {
    let theorem_pack = TheoremPackCapabilities::full();
    let claims = InvariantClaims {
        distributed: DistributedClaims {
            protocol_machine_envelope_adherence: Some(ProtocolMachineEnvelopeAdherenceConfig {
                enabled: eligibility_value(&theorem_pack, "protocol_machine_envelope_adherence"),
            }),
            protocol_machine_envelope_admission: Some(ProtocolMachineEnvelopeAdmissionConfig {
                enabled: eligibility_value(&theorem_pack, "protocol_machine_envelope_admission"),
            }),
            protocol_envelope_bridge: Some(ProtocolEnvelopeBridgeConfig {
                enabled: eligibility_value(&theorem_pack, "protocol_envelope_bridge"),
            }),
            ..DistributedClaims::default()
        },
        ..InvariantClaims::default()
    };

    local_claim_consistency(&claims).expect("full capability bundle should be consistent");
    let exported = exported_bundle(claims.clone());
    assert_eq!(
        exported
            .claims
            .distributed
            .protocol_machine_envelope_adherence
            .as_ref()
            .map(|config| config.enabled),
        Some(true)
    );
    assert_eq!(
        exported
            .claims
            .distributed
            .protocol_machine_envelope_admission
            .as_ref()
            .map(|config| config.enabled),
        Some(true)
    );
    assert_eq!(
        exported
            .claims
            .distributed
            .protocol_envelope_bridge
            .as_ref()
            .map(|config| config.enabled),
        Some(true)
    );

    let config = ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::PredicateAllowList(vec![
            "protocol_machine.observable_output".to_string(),
        ]),
        ..ProtocolMachineConfig::default()
    };
    let bundle = MachineProtocolBundle::new(
        simple_image(),
        CompositionCertificate {
            artifact_id: "cert/aligned".to_string(),
            link_ok_full: true,
            theorem_pack,
            runtime_contracts: Some(RuntimeContracts::full()),
        },
    );
    let mut runtime = ComposedRuntime::new(config, MemoryBudget::default());
    runtime
        .admit_bundle(bundle)
        .expect("aligned capability surfaces should admit");
}

#[test]
fn runtime_admission_rejects_bridge_claims_when_certificate_drops_bridge_capability() {
    let theorem_pack = TheoremPackCapabilities {
        determinism: vec![DeterminismCapability::Full],
        schedulers: vec![SchedulerCapability::Cooperative],
        output_condition_gating: false,
    };
    let claims = InvariantClaims {
        distributed: DistributedClaims {
            protocol_machine_envelope_adherence: Some(ProtocolMachineEnvelopeAdherenceConfig {
                enabled: true,
            }),
            protocol_machine_envelope_admission: Some(ProtocolMachineEnvelopeAdmissionConfig {
                enabled: true,
            }),
            protocol_envelope_bridge: Some(ProtocolEnvelopeBridgeConfig { enabled: true }),
            ..DistributedClaims::default()
        },
        ..InvariantClaims::default()
    };

    local_claim_consistency(&claims).expect("bridge claim fixture should be internally consistent");
    let exported = exported_bundle(claims);
    assert_eq!(
        exported
            .claims
            .distributed
            .protocol_envelope_bridge
            .as_ref()
            .map(|config| config.enabled),
        Some(true)
    );
    assert!(
        !eligibility_value(&theorem_pack, "protocol_envelope_bridge"),
        "theorem-pack capability drop should be visible in the execution profile"
    );

    let config = ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::PredicateAllowList(vec![
            "protocol_machine.observable_output".to_string(),
        ]),
        ..ProtocolMachineConfig::default()
    };
    let bundle = MachineProtocolBundle::new(
        simple_image(),
        CompositionCertificate {
            artifact_id: "cert/missing-bridge".to_string(),
            link_ok_full: true,
            theorem_pack,
            runtime_contracts: Some(RuntimeContracts::full()),
        },
    );
    let mut runtime = ComposedRuntime::new(config, MemoryBudget::default());
    let err = runtime
        .admit_bundle(bundle)
        .expect_err("missing bridge capability should reject output-condition admission");
    assert!(matches!(
        err,
        CompositionError::MissingCapability { ref capability, .. }
        if capability == "execution_profile"
    ));
}

#[test]
fn negative_protocol_bundle_fixtures_fail_local_claim_consistency_checks() {
    let bad_quorum = test_choreographies::bad_quorum();
    assert_eq!(
        local_claim_consistency(&bad_quorum.claims),
        Err("quorum_geometry")
    );

    let unbounded_wait = test_choreographies::unbounded_wait();
    assert_eq!(
        local_claim_consistency(&unbounded_wait.claims),
        Err("partial_synchrony")
    );

    let bridge_without_admission = test_choreographies::bridge_without_admission();
    assert_eq!(
        local_claim_consistency(&bridge_without_admission.claims),
        Err("protocol_envelope_bridge")
    );
}

#[test]
fn public_runtime_gate_matrix_matches_composed_runtime_admission() {
    let default_cfg = ProtocolMachineConfig::default();
    assert_eq!(
        enforce_protocol_machine_runtime_gates(&default_cfg, None),
        RuntimeGateResult::Admitted
    );
    let default_profile = runtime_execution_profile(&default_cfg, None);
    assert!(default_profile
        .admissibility_classes
        .contains(&ProtocolMachineAdmissibilityClass::ProtocolEnvelopeBridge));
    assert!(default_profile
        .escalation_window_classes
        .contains(&ProtocolMachineEscalationWindowClass::ProtocolBridge));
    admit_public_bundle(default_cfg, TheoremPackCapabilities::full(), None)
        .expect("default public runtime path should admit without contracts");

    let round_robin_cfg = ProtocolMachineConfig {
        sched_policy: SchedPolicy::RoundRobin,
        ..ProtocolMachineConfig::default()
    };
    assert_eq!(
        enforce_protocol_machine_runtime_gates(&round_robin_cfg, None),
        RuntimeGateResult::RejectedMissingContracts
    );
    let err = admit_public_bundle(round_robin_cfg, TheoremPackCapabilities::full(), None)
        .expect_err("advanced scheduler mode should reject missing contracts");
    assert!(matches!(
        err,
        CompositionError::MissingRuntimeContracts { .. }
    ));

    let bridge_disabled_cfg = ProtocolMachineConfig {
        output_condition_policy: OutputConditionPolicy::AllowAll,
        ..ProtocolMachineConfig::default()
    };
    assert_eq!(
        enforce_protocol_machine_runtime_gates(
            &bridge_disabled_cfg,
            Some(&RuntimeContracts::full())
        ),
        RuntimeGateResult::Admitted
    );
    let err = admit_public_bundle(
        bridge_disabled_cfg,
        TheoremPackCapabilities {
            determinism: vec![DeterminismCapability::Full],
            schedulers: vec![SchedulerCapability::Cooperative],
            output_condition_gating: false,
        },
        Some(RuntimeContracts::full()),
    )
    .expect_err("public admission should reject theorem packs that drop bridge capability");
    assert!(matches!(
        err,
        CompositionError::MissingCapability { ref capability, .. }
        if capability == "execution_profile"
    ));
}

#[test]
fn mixed_determinism_profile_matrix_is_stable_across_public_surfaces() {
    let full_cfg = ProtocolMachineConfig {
        determinism_mode: DeterminismMode::Full,
        ..ProtocolMachineConfig::default()
    };
    assert_eq!(
        enforce_protocol_machine_runtime_gates(&full_cfg, None),
        RuntimeGateResult::Admitted
    );
    admit_public_bundle(full_cfg, TheoremPackCapabilities::full(), None)
        .expect("full determinism should admit without runtime contracts");

    let modulo_effects_cfg = ProtocolMachineConfig {
        sched_policy: SchedPolicy::RoundRobin,
        determinism_mode: DeterminismMode::ModuloEffects,
        ..ProtocolMachineConfig::default()
    };
    assert_eq!(
        enforce_protocol_machine_runtime_gates(
            &modulo_effects_cfg,
            Some(&RuntimeContracts::full())
        ),
        RuntimeGateResult::Admitted
    );
    let modulo_effects_profile =
        runtime_execution_profile(&modulo_effects_cfg, Some(&RuntimeContracts::full()));
    assert!(modulo_effects_profile
        .fairness_assumptions
        .contains(&ProtocolMachineFairnessAssumption::StarvationFreedom));
    assert!(modulo_effects_profile
        .fairness_assumptions
        .contains(&ProtocolMachineFairnessAssumption::LivenessFairness));
    assert!(modulo_effects_profile
        .escalation_window_classes
        .contains(&ProtocolMachineEscalationWindowClass::AdmissionComplexity));
    admit_public_bundle(
        modulo_effects_cfg,
        TheoremPackCapabilities::full(),
        Some(RuntimeContracts::full()),
    )
    .expect("mixed determinism should admit when contracts and theorem-pack capabilities align");

    let mut no_modulo_comm = RuntimeContracts::full();
    no_modulo_comm.determinism_artifacts.modulo_commutativity = false;
    let modulo_comm_cfg = ProtocolMachineConfig {
        sched_policy: SchedPolicy::RoundRobin,
        determinism_mode: DeterminismMode::ModuloCommutativity,
        ..ProtocolMachineConfig::default()
    };
    assert_eq!(
        enforce_protocol_machine_runtime_gates(&modulo_comm_cfg, Some(&no_modulo_comm)),
        RuntimeGateResult::RejectedUnsupportedDeterminismProfile
    );
    let err = admit_public_bundle(
        modulo_comm_cfg,
        TheoremPackCapabilities::full(),
        Some(no_modulo_comm),
    )
    .expect_err("modulo-commutativity should reject when runtime contracts drop the artifact");
    assert!(matches!(
        err,
        CompositionError::MissingCapability { ref capability, .. }
        if capability == "determinism_profile::ModuloCommutativity"
    ));

    let mut no_replay_gate = RuntimeContracts::full();
    no_replay_gate.can_use_mixed_determinism_profiles = false;
    let replay_cfg = ProtocolMachineConfig {
        determinism_mode: DeterminismMode::Replay,
        ..ProtocolMachineConfig::default()
    };
    assert_eq!(
        enforce_protocol_machine_runtime_gates(&replay_cfg, Some(&no_replay_gate)),
        RuntimeGateResult::RejectedUnsupportedDeterminismProfile
    );
    let err = admit_public_bundle(
        replay_cfg,
        TheoremPackCapabilities::full(),
        Some(no_replay_gate),
    )
    .expect_err("replay determinism should reject when mixed-profile gating is absent");
    assert!(matches!(
        err,
        CompositionError::MissingCapability { ref capability, .. }
        if capability == "determinism_profile::Replay"
    ));
}

#[test]
fn runtime_capability_snapshot_reports_all_public_capabilities_in_stable_order() {
    let mut contracts = RuntimeContracts::full();
    contracts
        .capabilities
        .remove(&RuntimeCapability::LiveMigration);
    contracts
        .capabilities
        .remove(&RuntimeCapability::AutoscaleRepartition);
    contracts
        .capabilities
        .remove(&RuntimeCapability::PlacementRefinement);
    let snapshot = runtime_capability_snapshot(&contracts);

    assert_eq!(
        snapshot,
        vec![
            ("live_migration".to_string(), false),
            ("autoscale_repartition".to_string(), false),
            ("placement_refinement".to_string(), false),
            ("relaxed_reordering".to_string(), true),
        ]
    );
}

#[test]
fn distributed_reconfiguration_claims_remain_schema_visible_but_do_not_bypass_runtime_caps() {
    let claims = InvariantClaims {
        distributed: DistributedClaims {
            reconfiguration: Some(ReconfigurationConfig {
                dynamic_membership: true,
                overlap_required: true,
            }),
            ..DistributedClaims::default()
        },
        ..InvariantClaims::default()
    };
    let exported = exported_bundle(claims);
    let reconfiguration = exported
        .claims
        .distributed
        .reconfiguration
        .expect("reconfiguration claim should round-trip through the bridge schema");
    assert!(reconfiguration.dynamic_membership);
    assert!(reconfiguration.overlap_required);

    let mut contracts = RuntimeContracts::full();
    contracts
        .capabilities
        .remove(&RuntimeCapability::LiveMigration);
    contracts
        .capabilities
        .remove(&RuntimeCapability::AutoscaleRepartition);
    contracts
        .capabilities
        .remove(&RuntimeCapability::PlacementRefinement);

    assert_eq!(
        runtime_capability_snapshot(&contracts),
        vec![
            ("live_migration".to_string(), false),
            ("autoscale_repartition".to_string(), false),
            ("placement_refinement".to_string(), false),
            ("relaxed_reordering".to_string(), true),
        ],
        "schema-level reconfiguration claims must not silently re-enable missing runtime capabilities",
    );
    assert_eq!(
        enforce_protocol_machine_runtime_gates(
            &ProtocolMachineConfig::default(),
            Some(&contracts)
        ),
        RuntimeGateResult::Admitted,
        "reconfiguration schema metadata is descriptive today and must not mutate default runtime admission",
    );
}

#[test]
fn exported_reconfiguration_claims_flow_into_machine_runtime_admission() {
    let exported = exported_bundle(InvariantClaims {
        distributed: DistributedClaims {
            reconfiguration: Some(ReconfigurationConfig {
                dynamic_membership: true,
                overlap_required: true,
            }),
            ..DistributedClaims::default()
        },
        ..InvariantClaims::default()
    });

    let machine_bundle = exported
        .to_machine_bundle(CompositionCertificate {
            artifact_id: "cert/bridge-reconfig".to_string(),
            link_ok_full: true,
            theorem_pack: TheoremPackCapabilities::full(),
            runtime_contracts: Some(RuntimeContracts::full()),
        })
        .expect("bridge bundle should convert into machine bundle");
    assert_eq!(
        machine_bundle.reconfiguration_policy(),
        Some(&telltale_machine::ReconfigurationPolicy {
            dynamic_membership: true,
            overlap_required: true,
        })
    );

    let mut runtime =
        ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
    runtime
        .admit_bundle(machine_bundle)
        .expect("reconfiguration-enabled bridge bundle should admit with matching contracts");
    runtime
        .seed_bundle_membership(0, ["Alice", "Bob"])
        .expect("seed membership");
    let event = runtime
        .reconfigure_bundle(0, ["Bob", "Carol"])
        .expect("apply reconfiguration");
    assert_eq!(event.previous_members, vec!["Alice", "Bob"]);
    assert_eq!(event.next_members, vec!["Bob", "Carol"]);
    assert!(event.overlap_preserved);
}

#[test]
fn exported_reconfiguration_claims_reject_runtime_without_matching_capabilities() {
    let exported = exported_bundle(InvariantClaims {
        distributed: DistributedClaims {
            reconfiguration: Some(ReconfigurationConfig {
                dynamic_membership: true,
                overlap_required: true,
            }),
            ..DistributedClaims::default()
        },
        ..InvariantClaims::default()
    });

    let mut contracts = RuntimeContracts::full();
    contracts
        .capabilities
        .remove(&RuntimeCapability::LiveMigration);
    let machine_bundle = exported
        .to_machine_bundle(CompositionCertificate {
            artifact_id: "cert/bridge-reconfig-missing".to_string(),
            link_ok_full: true,
            theorem_pack: TheoremPackCapabilities::full(),
            runtime_contracts: Some(contracts),
        })
        .expect("bridge bundle should convert into machine bundle");

    let mut runtime =
        ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
    let err = runtime
        .admit_bundle(machine_bundle)
        .expect_err("overlap-required reconfiguration should require live migration capability");
    assert!(matches!(
        err,
        CompositionError::MissingReconfigurationCapability { ref capability, .. }
        if capability == "reconfiguration::overlap_required"
    ));
}

#[test]
fn exported_reconfiguration_transition_matches_lean_reference_event() {
    let runner = protocol_machine_runner();

    let exported = exported_bundle(InvariantClaims {
        distributed: DistributedClaims {
            reconfiguration: Some(ReconfigurationConfig {
                dynamic_membership: true,
                overlap_required: true,
            }),
            ..DistributedClaims::default()
        },
        ..InvariantClaims::default()
    });

    let machine_bundle = exported
        .to_machine_bundle(CompositionCertificate {
            artifact_id: "cert/bridge-reconfig-lean".to_string(),
            link_ok_full: true,
            theorem_pack: TheoremPackCapabilities::full(),
            runtime_contracts: Some(RuntimeContracts::full()),
        })
        .expect("bridge bundle should convert into machine bundle");
    let policy = machine_bundle
        .reconfiguration_policy()
        .cloned()
        .expect("bridge bundle should carry reconfiguration policy");

    let mut runtime =
        ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
    runtime
        .admit_bundle(machine_bundle)
        .expect("aligned bridge/runtime bundle should admit");
    runtime
        .seed_bundle_membership(0, ["Carol", "Alice", "Bob"])
        .expect("seed membership");
    let rust_event = runtime
        .reconfigure_bundle(0, ["Bob", "Dora", "Carol"])
        .expect("apply accepted reconfiguration");

    let validation = runner
        .validate_reconfiguration_transition(
            &rust_event.artifact_id,
            &policy,
            0,
            &rust_event.previous_members,
            &rust_event.next_members,
        )
        .unwrap_or_else(|err| panic!("lean reconfiguration validation should execute: {err}"));

    assert!(
        validation.valid,
        "accepted reconfiguration should validate in Lean: {:?}",
        validation.errors
    );
    assert_eq!(validation.event.as_ref(), Some(&rust_event));
}

#[test]
fn invalid_reconfiguration_transition_matches_lean_rejection() {
    let runner = protocol_machine_runner();

    let exported = exported_bundle(InvariantClaims {
        distributed: DistributedClaims {
            reconfiguration: Some(ReconfigurationConfig {
                dynamic_membership: true,
                overlap_required: true,
            }),
            ..DistributedClaims::default()
        },
        ..InvariantClaims::default()
    });

    let machine_bundle = exported
        .to_machine_bundle(CompositionCertificate {
            artifact_id: "cert/bridge-reconfig-invalid".to_string(),
            link_ok_full: true,
            theorem_pack: TheoremPackCapabilities::full(),
            runtime_contracts: Some(RuntimeContracts::full()),
        })
        .expect("bridge bundle should convert into machine bundle");
    let policy = machine_bundle
        .reconfiguration_policy()
        .cloned()
        .expect("bridge bundle should carry reconfiguration policy");

    let mut runtime =
        ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
    runtime
        .admit_bundle(machine_bundle)
        .expect("aligned bridge/runtime bundle should admit");
    runtime
        .seed_bundle_membership(0, ["Alice", "Bob"])
        .expect("seed membership");
    let rust_err = runtime
        .reconfigure_bundle(0, ["Carol", "Dora"])
        .expect_err("disjoint overlap-required transition must reject");
    assert!(matches!(
        rust_err,
        CompositionError::OverlapRequiredViolation { .. }
    ));

    let validation = runner
        .validate_reconfiguration_transition(
            "cert/bridge-reconfig-invalid",
            &policy,
            0,
            &["Alice".to_string(), "Bob".to_string()],
            &["Carol".to_string(), "Dora".to_string()],
        )
        .unwrap_or_else(|err| panic!("lean reconfiguration validation should execute: {err}"));

    assert!(!validation.valid, "invalid transition must reject in Lean");
    assert!(
        validation
            .errors
            .iter()
            .any(|error| error.code == "reconfiguration.overlap_required"),
        "expected explicit overlap-required error, got {:?}",
        validation.errors
    );
    assert_eq!(
        validation
            .event
            .as_ref()
            .map(|event| event.overlap_preserved),
        Some(false)
    );
}

#[test]
fn reconfiguration_plan_with_runtime_topology_artifacts_matches_lean_step_validation() {
    let runner = protocol_machine_runner();

    let exported = exported_bundle(InvariantClaims {
        distributed: DistributedClaims {
            reconfiguration: Some(ReconfigurationConfig {
                dynamic_membership: true,
                overlap_required: true,
            }),
            ..DistributedClaims::default()
        },
        ..InvariantClaims::default()
    });

    let machine_bundle = exported
        .to_machine_bundle(CompositionCertificate {
            artifact_id: "cert/bridge-reconfig-plan".to_string(),
            link_ok_full: true,
            theorem_pack: TheoremPackCapabilities::full(),
            runtime_contracts: Some(RuntimeContracts::full()),
        })
        .expect("bridge bundle should convert into machine bundle");
    let policy = machine_bundle
        .reconfiguration_policy()
        .cloned()
        .expect("bridge bundle should carry reconfiguration policy");

    let mut runtime =
        ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
    runtime
        .admit_bundle(machine_bundle)
        .expect("aligned bridge/runtime bundle should admit");
    runtime
        .seed_bundle_membership(0, ["Alice", "Bob"])
        .expect("seed membership");

    let prepare_topology = Topology::builder()
        .local_role(RoleName::from_static("Bob"))
        .colocated_role(RoleName::from_static("Carol"), RoleName::from_static("Bob"))
        .remote_role(
            RoleName::from_static("Dora"),
            TopologyEndpoint::new("127.0.0.1:19851").expect("endpoint"),
        )
        .region(
            RoleName::from_static("Bob"),
            Region::new("eu_central_1").expect("region"),
        )
        .region(
            RoleName::from_static("Dora"),
            Region::new("us_east_1").expect("region"),
        )
        .build();
    let cutover_topology = Topology::builder()
        .remote_role(
            RoleName::from_static("Carol"),
            TopologyEndpoint::new("127.0.0.1:19852").expect("endpoint"),
        )
        .colocated_role(
            RoleName::from_static("Dora"),
            RoleName::from_static("Carol"),
        )
        .remote_role(
            RoleName::from_static("Eve"),
            TopologyEndpoint::new("127.0.0.1:19853").expect("endpoint"),
        )
        .region(
            RoleName::from_static("Carol"),
            Region::new("us_east_1").expect("region"),
        )
        .region(
            RoleName::from_static("Eve"),
            Region::new("us_west_2").expect("region"),
        )
        .build();
    let plan = ReconfigurationPlan {
        plan_id: "plan/bridge-blue-green".to_string(),
        steps: vec![
            ReconfigurationPlanStep {
                step_id: "prepare".to_string(),
                next_members: vec!["Bob".to_string(), "Carol".to_string(), "Dora".to_string()],
                placements: prepare_topology
                    .placement_observations_for_roles(["Bob", "Carol", "Dora"])
                    .expect("prepare placement observations"),
            },
            ReconfigurationPlanStep {
                step_id: "cutover".to_string(),
                next_members: vec!["Carol".to_string(), "Dora".to_string(), "Eve".to_string()],
                placements: cutover_topology
                    .placement_observations_for_roles(["Carol", "Dora", "Eve"])
                    .expect("cutover placement observations"),
            },
        ],
    };

    let execution = runtime
        .execute_reconfiguration_plan(0, &plan)
        .expect("execute plan");
    assert_eq!(execution.phases.len(), 2);
    assert!(
        execution.phases[0]
            .transport_boundaries
            .iter()
            .any(|boundary| matches!(
                boundary.boundary,
                telltale_types::TransportBoundaryKind::SharedMemory
            )),
        "prepare phase should expose a colocated shared-memory boundary"
    );
    assert!(
        execution.phases[1]
            .transport_boundaries
            .iter()
            .any(|boundary| matches!(
                boundary.boundary,
                telltale_types::TransportBoundaryKind::Network
            ) && boundary.cross_region),
        "cutover phase should expose a cross-region network boundary"
    );

    for phase in &execution.phases {
        let validation = runner
            .validate_reconfiguration_transition(
                &phase.event.artifact_id,
                &policy,
                phase.event.epoch.saturating_sub(1),
                &phase.event.previous_members,
                &phase.event.next_members,
            )
            .unwrap_or_else(|err| panic!("lean reconfiguration validation should execute: {err}"));
        assert!(
            validation.valid,
            "accepted reconfiguration plan phase should validate in Lean: {:?}",
            validation.errors
        );
        assert_eq!(validation.event.as_ref(), Some(&phase.event));
    }
}
