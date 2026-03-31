#![allow(clippy::expect_used)]

use std::collections::BTreeMap;

use telltale_bridge::{
    export_protocol_bundle, DistributedClaims, InvariantClaims, ReconfigurationConfig,
};
use telltale_machine::coroutine::Value;
use telltale_machine::instr::{ImmValue, Instr};
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{
    run_loaded_protocol_machine_record_replay_conformance, ComposedRuntime, CompositionCertificate,
    CompositionError, MemoryBudget, ProtocolBundle, ProtocolMachine, ProtocolMachineConfig,
    ReconfigurationPlan, ReconfigurationPlanExecution, ReconfigurationPlanStep,
    ReconfigurationRuntimeSnapshot, RuntimeContracts, RuntimeUpgradeCompatibility,
    RuntimeUpgradeExecution, RuntimeUpgradeExecutionConstraint, RuntimeUpgradeRequest,
    TheoremPackCapabilities,
};
use telltale_machine::{DelegationStatus, ObsEvent, OwnershipScope, SemanticAuditRecord};
use telltale_runtime::{Region, RoleName, Topology, TopologyEndpoint};
use telltale_types::{
    CanonicalPublicationContinuity, GlobalType, Label, LocalTypeR, PendingEffectTreatment,
    TransitionArtifactPhase,
};

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

fn exported_bundle() -> telltale_bridge::ProtocolBundle {
    let (global, locals) = simple_protocol();
    export_protocol_bundle(
        &global,
        &locals,
        InvariantClaims {
            distributed: DistributedClaims {
                reconfiguration: Some(ReconfigurationConfig {
                    dynamic_membership: true,
                    overlap_required: true,
                }),
                ..DistributedClaims::default()
            },
            ..InvariantClaims::default()
        },
    )
}

fn roundtripped_machine_bundle(artifact_id: &str) -> ProtocolBundle {
    let exported = serde_json::from_str::<telltale_bridge::ProtocolBundle>(
        &serde_json::to_string(&exported_bundle()).expect("serialize exported bundle"),
    )
    .expect("deserialize exported bundle");
    exported
        .to_machine_bundle(CompositionCertificate {
            artifact_id: artifact_id.to_string(),
            link_ok_full: true,
            theorem_pack: TheoremPackCapabilities::full(),
            runtime_contracts: Some(RuntimeContracts::full()),
        })
        .expect("convert exported bundle into machine bundle")
}

fn configured_runtime(artifact_id: &str) -> ComposedRuntime {
    let mut runtime =
        ComposedRuntime::new(ProtocolMachineConfig::default(), MemoryBudget::default());
    runtime
        .admit_bundle(roundtripped_machine_bundle(artifact_id))
        .expect("admit machine bundle");
    runtime
}

#[derive(Debug, Clone, Copy)]
struct NoopHandler;

impl EffectHandler for NoopHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Unit)
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

fn ownership_transfer_image() -> CodeImage {
    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);
    local_types.insert("B".to_string(), LocalTypeR::End);

    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![
            Instr::Set {
                dst: 1,
                val: ImmValue::Nat(1),
            },
            Instr::Transfer {
                endpoint: 0,
                target: 1,
                bundle: 2,
            },
            Instr::Halt,
        ],
    );
    programs.insert("B".to_string(), vec![Instr::Halt]);

    CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    }
}

#[derive(Debug, Clone, PartialEq)]
struct OwnershipTransferView {
    obs_trace: Vec<ObsEvent>,
    semantic_audit_log: Vec<SemanticAuditRecord>,
    semantic_handoffs: Vec<telltale_machine::SemanticHandoff>,
}

fn ownership_transfer_view() -> OwnershipTransferView {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine
        .load_choreography(&ownership_transfer_image())
        .expect("load ownership transfer fixture");

    let report =
        run_loaded_protocol_machine_record_replay_conformance(&mut machine, &NoopHandler, 32)
            .expect("record/replay harness should succeed");
    assert!(report.replay_consistent);
    assert!(
        machine.trace().iter().any(|event| matches!(
            event,
            ObsEvent::Transferred { role, from, to, .. }
                if role == "A" && from == &0 && to == &1
        )),
        "ownership transfer fixture must emit a transfer observable"
    );
    assert!(
        machine.delegation_audit_log().iter().any(|record| {
            record.status == DelegationStatus::Committed
                && record.receipt.scope
                    == OwnershipScope::Fragments(std::collections::BTreeSet::from(
                        ["A".to_string()],
                    ))
        }),
        "ownership transfer fixture must emit a committed handoff receipt"
    );
    OwnershipTransferView {
        obs_trace: machine.trace().to_vec(),
        semantic_audit_log: machine.semantic_audit_log().to_vec(),
        semantic_handoffs: machine.semantic_objects().semantic_handoffs,
    }
}

fn prepare_plan() -> ReconfigurationPlan {
    let topology = Topology::builder()
        .local_role(RoleName::from_static("Bob"))
        .colocated_role(RoleName::from_static("Carol"), RoleName::from_static("Bob"))
        .remote_role(
            RoleName::from_static("Dora"),
            TopologyEndpoint::new("127.0.0.1:19861").expect("endpoint"),
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
    ReconfigurationPlan {
        plan_id: "plan/recovery-prefix".to_string(),
        steps: vec![ReconfigurationPlanStep {
            step_id: "prepare".to_string(),
            next_members: vec!["Bob".to_string(), "Carol".to_string(), "Dora".to_string()],
            placements: topology
                .placement_observations_for_roles(["Bob", "Carol", "Dora"])
                .expect("prepare placement observations"),
        }],
    }
}

fn cutover_plan() -> ReconfigurationPlan {
    let topology = Topology::builder()
        .remote_role(
            RoleName::from_static("Carol"),
            TopologyEndpoint::new("127.0.0.1:19862").expect("endpoint"),
        )
        .colocated_role(
            RoleName::from_static("Dora"),
            RoleName::from_static("Carol"),
        )
        .remote_role(
            RoleName::from_static("Eve"),
            TopologyEndpoint::new("127.0.0.1:19863").expect("endpoint"),
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
    ReconfigurationPlan {
        plan_id: "plan/recovery-suffix".to_string(),
        steps: vec![ReconfigurationPlanStep {
            step_id: "cutover".to_string(),
            next_members: vec!["Carol".to_string(), "Dora".to_string(), "Eve".to_string()],
            placements: topology
                .placement_observations_for_roles(["Carol", "Dora", "Eve"])
                .expect("cutover placement observations"),
        }],
    }
}

fn runtime_upgrade_request(upgrade_id: &str, plan: ReconfigurationPlan) -> RuntimeUpgradeRequest {
    RuntimeUpgradeRequest {
        upgrade_id: upgrade_id.to_string(),
        plan,
        compatibility: RuntimeUpgradeCompatibility {
            execution_constraint: RuntimeUpgradeExecutionConstraint::PreserveBundleProfile,
            ownership_continuity_required: true,
            pending_effect_treatment: PendingEffectTreatment::PreservePending,
            canonical_publication_continuity:
                CanonicalPublicationContinuity::PreserveCanonicalTruth,
        },
        carried_publication_ids: vec![format!("publication/{upgrade_id}")],
        invalidated_publication_ids: Vec::new(),
        carried_obligation_ids: vec![format!("obligation/{upgrade_id}")],
        invalidated_obligation_ids: Vec::new(),
    }
}

#[derive(Debug)]
struct RecoveryView {
    ownership_transfer: OwnershipTransferView,
    suffix_execution: ReconfigurationPlanExecution,
    final_snapshot: ReconfigurationRuntimeSnapshot,
    full_history: Vec<telltale_machine::ReconfigurationEvent>,
    plan_executions: Vec<ReconfigurationPlanExecution>,
}

fn drive_history_with_optional_restore(restore_after_prefix: bool) -> RecoveryView {
    let ownership_transfer = ownership_transfer_view();
    let mut runtime = configured_runtime("cert/reconfiguration-recovery");
    runtime
        .seed_bundle_membership(0, ["Alice", "Bob"])
        .expect("seed initial members");
    runtime
        .execute_reconfiguration_plan(0, &prepare_plan())
        .expect("execute prefix plan");
    let saved_snapshot = serde_json::from_str::<ReconfigurationRuntimeSnapshot>(
        &serde_json::to_string(
            &runtime
                .bundle_reconfiguration_snapshot(0)
                .expect("snapshot after prefix plan"),
        )
        .expect("serialize reconfiguration snapshot"),
    )
    .expect("deserialize reconfiguration snapshot");

    let mut runtime = if restore_after_prefix {
        let mut restored = configured_runtime("cert/reconfiguration-recovery");
        restored
            .restore_bundle_reconfiguration_snapshot(0, saved_snapshot)
            .expect("restore prefix snapshot");
        restored
    } else {
        runtime
    };
    let suffix_execution = runtime
        .execute_reconfiguration_plan(0, &cutover_plan())
        .expect("execute suffix plan");
    RecoveryView {
        ownership_transfer,
        suffix_execution,
        final_snapshot: serde_json::from_str(
            &serde_json::to_string(
                &runtime
                    .bundle_reconfiguration_snapshot(0)
                    .expect("final reconfiguration snapshot"),
            )
            .expect("serialize final snapshot"),
        )
        .expect("deserialize final snapshot"),
        full_history: runtime
            .bundle_reconfiguration_history(0)
            .expect("full reconfiguration history")
            .to_vec(),
        plan_executions: runtime
            .bundle_reconfiguration_plan_executions(0)
            .expect("plan execution history")
            .to_vec(),
    }
}

#[test]
fn recovery_harness_replays_equivalent_reconfiguration_histories_to_same_semantic_truth() {
    let straight_line = drive_history_with_optional_restore(false);
    let restored = drive_history_with_optional_restore(true);

    assert_eq!(
        restored.ownership_transfer,
        straight_line.ownership_transfer
    );
    assert_eq!(restored.suffix_execution, straight_line.suffix_execution);
    assert_eq!(restored.final_snapshot, straight_line.final_snapshot);
    assert_eq!(restored.full_history, straight_line.full_history);
    assert_eq!(restored.plan_executions, straight_line.plan_executions);
}

#[test]
fn recovery_harness_detects_tampered_snapshot_divergence() {
    let mut runtime = configured_runtime("cert/reconfiguration-recovery-negative");
    runtime
        .seed_bundle_membership(0, ["Alice", "Bob"])
        .expect("seed initial members");
    runtime
        .execute_reconfiguration_plan(0, &prepare_plan())
        .expect("execute prefix plan");
    let mut tampered_snapshot = runtime
        .bundle_reconfiguration_snapshot(0)
        .expect("snapshot after prefix plan");
    tampered_snapshot.active_members = vec!["Bob".to_string(), "Mallory".to_string()];

    let mut restored = configured_runtime("cert/reconfiguration-recovery-negative");
    let error = restored
        .restore_bundle_reconfiguration_snapshot(0, tampered_snapshot)
        .expect_err("tampered snapshot must reject");
    assert!(matches!(
        error,
        CompositionError::InvalidReconfigurationPlan { .. }
    ));
}

#[derive(Debug)]
struct RuntimeUpgradeRecoveryView {
    ownership_transfer: OwnershipTransferView,
    suffix_execution: RuntimeUpgradeExecution,
    final_snapshot: ReconfigurationRuntimeSnapshot,
    runtime_upgrades: Vec<RuntimeUpgradeExecution>,
}

fn drive_runtime_upgrade_history_with_optional_restore(
    restore_after_prefix: bool,
) -> RuntimeUpgradeRecoveryView {
    let ownership_transfer = ownership_transfer_view();
    let mut runtime = configured_runtime("cert/runtime-upgrade-recovery");
    runtime
        .seed_bundle_membership(0, ["Alice", "Bob"])
        .expect("seed initial members");
    runtime
        .execute_runtime_upgrade(
            0,
            &runtime_upgrade_request("upgrade/prepare", prepare_plan()),
        )
        .expect("execute prefix runtime upgrade");
    let saved_snapshot = serde_json::from_str::<ReconfigurationRuntimeSnapshot>(
        &serde_json::to_string(
            &runtime
                .bundle_reconfiguration_snapshot(0)
                .expect("snapshot after prefix runtime upgrade"),
        )
        .expect("serialize runtime-upgrade snapshot"),
    )
    .expect("deserialize runtime-upgrade snapshot");

    let mut runtime = if restore_after_prefix {
        let mut restored = configured_runtime("cert/runtime-upgrade-recovery");
        restored
            .restore_bundle_reconfiguration_snapshot(0, saved_snapshot)
            .expect("restore runtime-upgrade snapshot");
        restored
    } else {
        runtime
    };
    let suffix_execution = runtime
        .execute_runtime_upgrade(
            0,
            &runtime_upgrade_request("upgrade/cutover", cutover_plan()),
        )
        .expect("execute suffix runtime upgrade");
    RuntimeUpgradeRecoveryView {
        ownership_transfer,
        suffix_execution,
        final_snapshot: serde_json::from_str(
            &serde_json::to_string(
                &runtime
                    .bundle_reconfiguration_snapshot(0)
                    .expect("final runtime-upgrade snapshot"),
            )
            .expect("serialize final runtime-upgrade snapshot"),
        )
        .expect("deserialize final runtime-upgrade snapshot"),
        runtime_upgrades: runtime
            .bundle_runtime_upgrade_executions(0)
            .expect("runtime upgrade execution history")
            .to_vec(),
    }
}

#[test]
fn recovery_harness_replays_equivalent_runtime_upgrade_histories_to_same_semantic_truth() {
    let straight_line = drive_runtime_upgrade_history_with_optional_restore(false);
    let restored = drive_runtime_upgrade_history_with_optional_restore(true);

    assert_eq!(
        restored.ownership_transfer,
        straight_line.ownership_transfer
    );
    assert_eq!(restored.suffix_execution, straight_line.suffix_execution);
    assert_eq!(restored.final_snapshot, straight_line.final_snapshot);
    assert_eq!(restored.runtime_upgrades, straight_line.runtime_upgrades);
    assert_eq!(
        restored
            .final_snapshot
            .runtime_upgrades
            .last()
            .expect("final runtime-upgrade execution")
            .artifacts
            .last()
            .expect("committed cutover artifact")
            .phase,
        TransitionArtifactPhase::CommittedCutover
    );
}

#[test]
fn recovery_harness_detects_tampered_runtime_upgrade_snapshot_divergence() {
    let mut runtime = configured_runtime("cert/runtime-upgrade-recovery-negative");
    runtime
        .seed_bundle_membership(0, ["Alice", "Bob"])
        .expect("seed initial members");
    runtime
        .execute_runtime_upgrade(
            0,
            &runtime_upgrade_request("upgrade/prepare", prepare_plan()),
        )
        .expect("execute prefix runtime upgrade");
    let mut tampered_snapshot = runtime
        .bundle_reconfiguration_snapshot(0)
        .expect("snapshot after prefix runtime upgrade");
    tampered_snapshot.runtime_upgrades[0].artifacts.clear();

    let mut restored = configured_runtime("cert/runtime-upgrade-recovery-negative");
    let error = restored
        .restore_bundle_reconfiguration_snapshot(0, tampered_snapshot)
        .expect_err("tampered runtime-upgrade snapshot must reject");
    assert!(matches!(
        error,
        CompositionError::InvalidReconfigurationPlan { .. }
    ));
}
