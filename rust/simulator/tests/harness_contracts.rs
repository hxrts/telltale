//! Integration tests for harness and contract-check surfaces.

use std::collections::BTreeMap;

use telltale_simulator::contracts::{evaluate_contracts, ContractCheckConfig};
use telltale_simulator::harness::{DirectAdapter, HarnessConfig, HarnessSpec, SimulationHarness};
use telltale_simulator::material::{MaterialParams, MeanFieldParams};
use telltale_simulator::scenario::{OutputConfig, Scenario};
use telltale_types::{FixedQ32, GlobalType, Label, LocalTypeR};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::{EffectHandler, SendDecision, SendDecisionInput};

#[derive(Debug, Clone, Copy)]
struct PassthroughHandler;

impl EffectHandler for PassthroughHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        Ok(Value::Str(label.to_string()))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
        Ok(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> Result<(), String> {
        Ok(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> Result<String, String> {
        labels
            .first()
            .cloned()
            .ok_or_else(|| "no labels available".to_string())
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
        Ok(())
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
        concurrency: 1,
        seed: 5,
        network: None,
        material: MaterialParams::MeanField(MeanFieldParams {
            beta: FixedQ32::one(),
            species: vec!["up".into(), "down".into()],
            initial_state: vec![FixedQ32::half(), FixedQ32::half()],
            step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
        }),
        events: Vec::new(),
        properties: None,
        checkpoint_interval: None,
        output: OutputConfig::default(),
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
    let report = evaluate_contracts(&result, &config);
    assert!(
        report.passed,
        "expected passing contract report: {report:?}"
    );
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
