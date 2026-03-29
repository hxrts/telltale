#![allow(clippy::expect_used, missing_docs)]

use std::collections::BTreeMap;

use telltale_bridge::{
    export_protocol_bundle, global_to_json, local_to_json, DistributedClaims, InvariantClaims,
    LeanRunner, ReconfigurationConfig,
};
use telltale_language::ast::{choreography_to_global, local_to_local_r};
use telltale_language::compiler::parser::parse_choreography_str;
use telltale_language::compiler::projection::project;
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{
    run_loaded_protocol_machine_record_replay_conformance, ComposedRuntime, CompositionCertificate,
    MemoryBudget, ProtocolBundle, ProtocolMachine, ProtocolMachineConfig, ReconfigurationPlan,
    ReconfigurationPlanStep, ReconfigurationRuntimeSnapshot, RuntimeContracts,
    TheoremPackCapabilities,
};
use telltale_runtime::{Region, RoleName, Topology, TopologyEndpoint};
use telltale_types::{GlobalType, Label, LocalTypeR};

const STRICT_ENV: &str = "TELLTALE_REQUIRE_LEAN_VALIDATOR";

const LARGE_PROTOCOL_ROLE_COUNT: usize = 12;
const LARGE_PROTOCOL_HOP_COUNT: usize = 48;
const LARGE_PROTOCOL_GLOBAL_JSON_BUDGET_BYTES: usize = 32_000;
const LARGE_PROTOCOL_TOTAL_LOCAL_JSON_BUDGET_BYTES: usize = 96_000;
const LARGE_PROTOCOL_BUNDLE_JSON_BUDGET_BYTES: usize = 140_000;

const LONG_TRACE_STEPS: usize = 96;
const LONG_TRACE_EVENT_BUDGET: usize = 256;
const LONG_TRACE_JSON_BUDGET_BYTES: usize = 96_000;
const LONG_REPORT_JSON_BUDGET_BYTES: usize = 4_096;

const LARGE_RECONFIG_STEP_COUNT: usize = 8;
const LARGE_RECONFIG_HISTORY_BUDGET: usize = 16;
const LARGE_RECONFIG_SNAPSHOT_BUDGET_BYTES: usize = 128_000;

fn strict_projection_required() -> bool {
    std::env::var(STRICT_ENV)
        .map(|value| value != "0")
        .unwrap_or(false)
}

fn projection_runner() -> Option<LeanRunner> {
    match LeanRunner::for_projection() {
        Ok(runner) => Some(runner),
        Err(telltale_bridge::LeanRunnerError::BinaryNotFound(_)) => {
            assert!(
                !strict_projection_required(),
                "strict scale-budget verification is enabled but telltale_validator is unavailable"
            );
            None
        }
        Err(err) => panic!("failed to initialize Lean projection runner: {err}"),
    }
}

fn large_projection_dsl() -> String {
    let roles: Vec<_> = (0..LARGE_PROTOCOL_ROLE_COUNT)
        .map(|index| format!("R{index}"))
        .collect();
    let mut dsl = format!(
        "protocol LargeProjection =\n    roles {}\n",
        roles.join(", ")
    );
    for hop in 0..LARGE_PROTOCOL_HOP_COUNT {
        let sender = &roles[hop % roles.len()];
        let receiver = &roles[(hop + 1) % roles.len()];
        dsl.push_str(&format!("    {sender} -> {receiver} : Hop{hop:02}\n"));
    }
    dsl
}

fn long_ping_pong_image() -> CodeImage {
    let global = GlobalType::mu(
        "Loop",
        GlobalType::send(
            "A",
            "B",
            Label::new("Ping"),
            GlobalType::send("B", "A", Label::new("Pong"), GlobalType::var("Loop")),
        ),
    );
    let local_a = LocalTypeR::mu(
        "Loop",
        LocalTypeR::send(
            "B",
            Label::new("Ping"),
            LocalTypeR::recv("B", Label::new("Pong"), LocalTypeR::var("Loop")),
        ),
    );
    let local_b = LocalTypeR::mu(
        "Loop",
        LocalTypeR::recv(
            "A",
            Label::new("Ping"),
            LocalTypeR::send("A", Label::new("Pong"), LocalTypeR::var("Loop")),
        ),
    );
    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), local_a);
    local_types.insert("B".to_string(), local_b);
    CodeImage::from_local_types(&local_types, &global)
}

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

fn scaled_topology(step: usize) -> Topology {
    let suffix = 20 + step;
    Topology::builder()
        .local_role(RoleName::from_static("Bob"))
        .colocated_role(RoleName::from_static("Carol"), RoleName::from_static("Bob"))
        .remote_role(
            RoleName::from_static("Dora"),
            TopologyEndpoint::new(format!("127.0.0.1:19{suffix:03}")).expect("endpoint"),
        )
        .remote_role(
            RoleName::from_static("Eve"),
            TopologyEndpoint::new(format!("127.0.0.1:29{suffix:03}")).expect("endpoint"),
        )
        .colocated_role(RoleName::from_static("Frank"), RoleName::from_static("Eve"))
        .region(
            RoleName::from_static("Bob"),
            Region::new("eu_central_1").expect("region"),
        )
        .region(
            RoleName::from_static("Dora"),
            Region::new("us_east_1").expect("region"),
        )
        .region(
            RoleName::from_static("Eve"),
            Region::new("ap_southeast_1").expect("region"),
        )
        .build()
}

fn scaled_reconfiguration_plan() -> ReconfigurationPlan {
    let mut steps = Vec::new();
    for step in 0..LARGE_RECONFIG_STEP_COUNT {
        let topology = scaled_topology(step);
        steps.push(ReconfigurationPlanStep {
            step_id: format!("phase-{step:02}"),
            next_members: vec![
                "Bob".to_string(),
                "Carol".to_string(),
                "Dora".to_string(),
                "Eve".to_string(),
                "Frank".to_string(),
            ],
            placements: topology
                .placement_observations_for_roles(["Bob", "Carol", "Dora", "Eve", "Frank"])
                .expect("scaled placement observations"),
        });
    }
    ReconfigurationPlan {
        plan_id: "plan/scale-budget".to_string(),
        steps,
    }
}

#[test]
fn large_projection_lowering_corpus_stays_within_structural_budgets() {
    let dsl = large_projection_dsl();
    let choreography = parse_choreography_str(&dsl).expect("parse large deterministic DSL");
    let global =
        choreography_to_global(&choreography).expect("large deterministic DSL should lower");
    let global_json = global_to_json(&global);
    let global_json_bytes = serde_json::to_vec(&global_json)
        .expect("serialize large global JSON")
        .len();
    assert!(
        global_json_bytes <= LARGE_PROTOCOL_GLOBAL_JSON_BUDGET_BYTES,
        "large global JSON exceeded budget: {global_json_bytes} > {LARGE_PROTOCOL_GLOBAL_JSON_BUDGET_BYTES}"
    );

    let mut locals = BTreeMap::new();
    let mut total_local_json_bytes = 0usize;
    for role in &choreography.roles {
        let local = project(&choreography, role)
            .unwrap_or_else(|err| panic!("project {}: {err}", role.name()));
        let local_r = local_to_local_r(&local)
            .unwrap_or_else(|err| panic!("convert {} local type: {err}", role.name()));
        let local_json = local_to_json(&local_r);
        total_local_json_bytes += serde_json::to_vec(&local_json)
            .expect("serialize large local JSON")
            .len();
        locals.insert(role.name().to_string(), local_r);
    }
    assert_eq!(locals.len(), LARGE_PROTOCOL_ROLE_COUNT);
    assert!(
        total_local_json_bytes <= LARGE_PROTOCOL_TOTAL_LOCAL_JSON_BUDGET_BYTES,
        "large local JSON exceeded budget: {total_local_json_bytes} > {LARGE_PROTOCOL_TOTAL_LOCAL_JSON_BUDGET_BYTES}"
    );

    let bundle = export_protocol_bundle(&global, &locals, InvariantClaims::default());
    let bundle_json_bytes = serde_json::to_vec(&bundle)
        .expect("serialize large protocol bundle")
        .len();
    assert!(
        bundle_json_bytes <= LARGE_PROTOCOL_BUNDLE_JSON_BUDGET_BYTES,
        "large protocol bundle exceeded budget: {bundle_json_bytes} > {LARGE_PROTOCOL_BUNDLE_JSON_BUDGET_BYTES}"
    );

    if let Some(runner) = projection_runner() {
        let role_names: Vec<String> = choreography
            .roles
            .iter()
            .map(|role| role.name().to_string())
            .collect();
        let lean_projections = runner
            .project(&global_json, &role_names)
            .expect("Lean projection export should accept large deterministic corpus");
        assert_eq!(lean_projections.len(), LARGE_PROTOCOL_ROLE_COUNT);
        let lean_payload_bytes = serde_json::to_vec(&lean_projections)
            .expect("serialize Lean projection payload")
            .len();
        assert!(
            lean_payload_bytes <= LARGE_PROTOCOL_TOTAL_LOCAL_JSON_BUDGET_BYTES,
            "Lean projection payload exceeded budget: {lean_payload_bytes} > {LARGE_PROTOCOL_TOTAL_LOCAL_JSON_BUDGET_BYTES}"
        );
    }
}

#[test]
fn long_protocol_machine_replay_history_stays_within_trace_budgets() {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine
        .load_choreography(&long_ping_pong_image())
        .expect("load long deterministic ping/pong image");

    let report = run_loaded_protocol_machine_record_replay_conformance(
        &mut machine,
        &NoopHandler,
        LONG_TRACE_STEPS,
    )
    .expect("long replay conformance should succeed");
    assert!(report.replay_consistent);
    assert!(report.exact_trace_match);
    assert_eq!(report.baseline_event_count, report.replay_event_count);
    assert!(
        report.baseline_event_count <= LONG_TRACE_EVENT_BUDGET,
        "baseline trace exceeded budget: {} > {}",
        report.baseline_event_count,
        LONG_TRACE_EVENT_BUDGET
    );
    assert!(
        report.recorded_effect_count <= LONG_TRACE_EVENT_BUDGET,
        "recorded effect trace exceeded budget: {} > {}",
        report.recorded_effect_count,
        LONG_TRACE_EVENT_BUDGET
    );

    let trace_json_bytes = serde_json::to_vec(machine.trace())
        .expect("serialize long trace")
        .len();
    let report_json_bytes = serde_json::to_vec(&report)
        .expect("serialize replay report")
        .len();
    assert!(
        trace_json_bytes <= LONG_TRACE_JSON_BUDGET_BYTES,
        "trace JSON exceeded budget: {trace_json_bytes} > {LONG_TRACE_JSON_BUDGET_BYTES}"
    );
    assert!(
        report_json_bytes <= LONG_REPORT_JSON_BUDGET_BYTES,
        "replay report JSON exceeded budget: {report_json_bytes} > {LONG_REPORT_JSON_BUDGET_BYTES}"
    );
}

#[test]
fn large_reconfiguration_history_snapshot_stays_within_budget() {
    let plan = scaled_reconfiguration_plan();
    let mut runtime = configured_runtime("cert/reconfig-scale-budget");
    let execution = runtime
        .execute_reconfiguration_plan(0, &plan)
        .expect("scaled reconfiguration plan should execute");
    assert_eq!(execution.phases.len(), LARGE_RECONFIG_STEP_COUNT);
    assert!(
        execution.phases.len() <= LARGE_RECONFIG_HISTORY_BUDGET,
        "scaled reconfiguration execution exceeded phase budget"
    );

    let snapshot = runtime
        .bundle_reconfiguration_snapshot(0)
        .expect("export scaled reconfiguration snapshot");
    assert_eq!(snapshot.history.len(), LARGE_RECONFIG_STEP_COUNT);
    assert_eq!(snapshot.plan_executions.len(), 1);
    let snapshot_json_bytes = serde_json::to_vec(&snapshot)
        .expect("serialize scaled reconfiguration snapshot")
        .len();
    assert!(
        snapshot_json_bytes <= LARGE_RECONFIG_SNAPSHOT_BUDGET_BYTES,
        "scaled reconfiguration snapshot exceeded budget: {snapshot_json_bytes} > {LARGE_RECONFIG_SNAPSHOT_BUDGET_BYTES}"
    );

    let mut restored = configured_runtime("cert/reconfig-scale-budget");
    restored
        .restore_bundle_reconfiguration_snapshot(0, snapshot.clone())
        .expect("restore scaled reconfiguration snapshot");
    let restored_snapshot: ReconfigurationRuntimeSnapshot = serde_json::from_slice(
        &serde_json::to_vec(
            &restored
                .bundle_reconfiguration_snapshot(0)
                .expect("re-export restored snapshot"),
        )
        .expect("serialize restored snapshot"),
    )
    .expect("deserialize restored snapshot");
    assert_eq!(restored_snapshot, snapshot);
}
