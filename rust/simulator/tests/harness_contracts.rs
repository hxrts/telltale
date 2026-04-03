//! Integration tests for harness and contract-check surfaces.

use std::collections::BTreeMap;

use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_simulator::contracts::{
    assert_contracts, evaluate_contracts, ContractCheckConfig, ExpectedProgressState,
    ExpectedPublication,
};
use telltale_simulator::field::{FieldSpec, MeanFieldSpec};
use telltale_simulator::generated::ScenarioEffectResult;
use telltale_simulator::harness::{
    DirectAdapter, HarnessConfig, HarnessSpec, HostAdapter, SimulationHarness,
};
use telltale_simulator::scenario::{ExecutionSpec, Scenario};
use telltale_types::{FixedQ32, GlobalType, Label, LocalTypeR};

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
        EffectResult::success(
            labels
                .first()
                .cloned()
                .expect("labels should contain at least one branch"),
        )
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }
}

struct StateProvidingAdapter {
    handler: PassthroughHandler,
}

impl HostAdapter for StateProvidingAdapter {
    fn effect_handler(&self) -> &dyn EffectHandler {
        &self.handler
    }

    fn initial_states(
        &self,
        _scenario: &Scenario,
    ) -> Result<Option<BTreeMap<String, Vec<FixedQ32>>>, String> {
        let mut states = BTreeMap::new();
        states.insert("A".to_string(), vec![FixedQ32::half(), FixedQ32::half()]);
        states.insert("B".to_string(), vec![FixedQ32::half(), FixedQ32::half()]);
        Ok(Some(states))
    }
}

fn simple_protocol() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::mu(
        "loop",
        GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("loop")),
    );

    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::var("loop"))],
            },
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::mu(
            "loop",
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::var("loop"))],
            },
        ),
    );

    (global, local_types)
}

fn scenario() -> Scenario {
    Scenario {
        name: "harness_contracts".to_string(),
        roles: vec!["A".to_string(), "B".to_string()],
        steps: 10,
        execution: ExecutionSpec::default(),
        seed: 5,
        network: None,
        field: Some(FieldSpec::MeanField(MeanFieldSpec {
            beta: FixedQ32::one(),
            species: vec!["up".into(), "down".into()],
            initial_state: vec![FixedQ32::half(), FixedQ32::half()],
            step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
        })),
        reconfigurations: Vec::new(),
        adversaries: Vec::new(),
        properties: None,
        checkpoint_interval: None,
        theorem: telltale_simulator::scenario::TheoremProfileSpec::default(),
        extensions: BTreeMap::new(),
    }
}

#[test]
fn harness_run_passes_default_contract_checks() {
    let (global_type, local_types) = simple_protocol();
    let spec = HarnessSpec::new(local_types, global_type, scenario());

    let adapter = DirectAdapter::new(&PassthroughHandler);
    let harness = SimulationHarness::new(&adapter);
    let result = harness.run(&spec).expect("harness run");

    let config = ContractCheckConfig {
        expected_roles: vec!["A".into(), "B".into()],
        ..ContractCheckConfig::default()
    };
    assert_contracts(&result, &config).expect("default contracts should pass");
}

#[test]
fn harness_contracts_detect_missing_role_samples() {
    let (global_type, local_types) = simple_protocol();
    let spec = HarnessSpec::new(local_types, global_type, scenario());

    let adapter = DirectAdapter::new(&PassthroughHandler);
    let harness = SimulationHarness::new(&adapter);
    let result = harness.run(&spec).expect("harness run");

    let config = ContractCheckConfig {
        expected_roles: vec!["C".into()],
        ..ContractCheckConfig::default()
    };
    let report = evaluate_contracts(&result, &config);
    assert!(!report.passed);
    assert!(report
        .failures
        .iter()
        .any(|msg| msg.contains("missing sampled trace records")));
}

#[test]
fn harness_contracts_detect_missing_parity_progress_contracts() {
    let (global_type, local_types) = simple_protocol();
    let spec = HarnessSpec::new(local_types, global_type, scenario());

    let adapter = DirectAdapter::new(&PassthroughHandler);
    let harness = SimulationHarness::new(&adapter);
    let mut result = harness.run(&spec).expect("harness run");
    result.replay.semantic_objects.progress_contracts.clear();

    let report = evaluate_contracts(&result, &ContractCheckConfig::default());
    assert!(!report.passed);
    assert!(report
        .failures
        .iter()
        .any(|msg| msg.contains("parity-critical semantic operations")));
}

#[test]
fn harness_contracts_validate_expected_progress_and_publication_states() {
    let (global_type, local_types) = simple_protocol();
    let spec = HarnessSpec::new(local_types, global_type, scenario());

    let adapter = DirectAdapter::new(&PassthroughHandler);
    let harness = SimulationHarness::new(&adapter);
    let result = harness.run(&spec).expect("harness run");

    let progress = result
        .replay
        .semantic_objects
        .progress_contracts
        .first()
        .expect("at least one progress contract");
    let publication = result
        .replay
        .semantic_objects
        .publication_events
        .first()
        .expect("at least one publication event");

    let config = ContractCheckConfig {
        expected_progress_states: vec![ExpectedProgressState {
            operation_id: progress.operation_id.clone(),
            state: "succeeded".to_string(),
        }],
        expected_publications: vec![ExpectedPublication {
            operation_id: publication.operation_id.clone(),
            publication: publication.publication.clone(),
            status: "published".to_string(),
        }],
        ..ContractCheckConfig::default()
    };

    assert_contracts(&result, &config).expect("expected semantic states should match");
}

#[test]
fn harness_contracts_report_expected_publication_mismatches() {
    let (global_type, local_types) = simple_protocol();
    let spec = HarnessSpec::new(local_types, global_type, scenario());

    let adapter = DirectAdapter::new(&PassthroughHandler);
    let harness = SimulationHarness::new(&adapter);
    let result = harness.run(&spec).expect("harness run");

    let publication = result
        .replay
        .semantic_objects
        .publication_events
        .first()
        .expect("at least one publication event");
    let config = ContractCheckConfig {
        expected_publications: vec![ExpectedPublication {
            operation_id: publication.operation_id.clone(),
            publication: publication.publication.clone(),
            status: "rejected".to_string(),
        }],
        ..ContractCheckConfig::default()
    };

    let report = evaluate_contracts(&result, &config);
    assert!(!report.passed);
    assert!(report
        .failures
        .iter()
        .any(|msg| msg.contains("publication status mismatch")));
}

#[test]
fn run_config_enforces_contract_checks() {
    let (global_type, local_types) = simple_protocol();
    let config = HarnessConfig {
        spec: HarnessSpec::new(local_types, global_type, scenario()),
        contracts: ContractCheckConfig {
            expected_roles: vec!["C".into()],
            ..ContractCheckConfig::default()
        },
    };

    let adapter = DirectAdapter::new(&PassthroughHandler);
    let harness = SimulationHarness::new(&adapter);
    let err = match harness.run_config(&config) {
        Ok(_) => panic!("contracts should fail"),
        Err(err) => err,
    };
    assert!(err.contains("missing sampled trace records"));
}

#[test]
fn generic_harness_run_succeeds_without_built_in_field() {
    let (global_type, local_types) = simple_protocol();
    let mut scenario = scenario();
    scenario.field = None;
    let spec = HarnessSpec::new(local_types, global_type, scenario);

    let adapter = StateProvidingAdapter {
        handler: PassthroughHandler,
    };
    let harness = SimulationHarness::new(&adapter);
    let result = harness.run(&spec).expect("generic harness run");

    assert!(result.trace.records.iter().any(|record| record.role == "A"));
    assert!(result.trace.records.iter().any(|record| record.role == "B"));
}

#[test]
fn generated_effect_result_helpers_cover_failure_modes() {
    let success =
        ScenarioEffectResult::success(serde_json::json!({"status": "ok"})).with_delay_ms(20);
    let timeout = ScenarioEffectResult::<serde_json::Value>::timeout();
    let degraded = ScenarioEffectResult::<serde_json::Value>::degraded("owner_lag");

    assert!(matches!(
        success,
        ScenarioEffectResult::Return {
            delay_ms: Some(20),
            ..
        }
    ));
    assert!(matches!(timeout, ScenarioEffectResult::Timeout { .. }));
    assert!(matches!(degraded, ScenarioEffectResult::Degraded { .. }));
}
