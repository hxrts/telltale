#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::expect_used)]
//! Reduced semantic-effect parity checks against Lean fixtures.

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use std::path::{Path, PathBuf};
use std::process::Command;

use serde::Deserialize;
use telltale_machine::durable::WalSyncRequest;
use telltale_machine::instr::{ImmValue, Instr, InvokeAction};
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectRequestBody, EffectResult, SendDecision, SendDecisionInput,
    TopologyPerturbation,
};
use telltale_machine::model::output_condition::OutputConditionHint;
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::semantic_objects::OutstandingEffectStatus;
use telltale_machine::{EffectExchangeRecord, ProtocolMachine, ProtocolMachineConfig};
use test_support::simple_send_recv_image;

#[derive(Debug, Clone, Deserialize, PartialEq, Eq, PartialOrd, Ord)]
struct ReducedSemanticEffectFixture {
    name: String,
    effect_kind: String,
    lifecycle: String,
    interface_name: String,
    operation_name: String,
    publication_materialized: bool,
    output_predicate: Option<String>,
}

#[derive(Debug, Deserialize)]
struct ReducedSemanticEffectBundle {
    schema_version: String,
    fixtures: Vec<ReducedSemanticEffectFixture>,
}

fn single_role_end_image(program: Vec<Instr>) -> CodeImage {
    CodeImage {
        programs: {
            let mut programs = std::collections::BTreeMap::new();
            programs.insert("A".to_string(), program);
            programs
        },
        global_type: telltale_types::GlobalType::End,
        local_types: {
            let mut local_types = std::collections::BTreeMap::new();
            local_types.insert("A".to_string(), telltale_types::LocalTypeR::End);
            local_types
        },
    }
}

#[derive(Debug, Clone, Copy)]
struct BlockedSendHandler;

impl EffectHandler for BlockedSendHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[telltale_machine::Value],
    ) -> EffectResult<telltale_machine::Value> {
        EffectResult::success(telltale_machine::Value::Unit)
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(
            input.payload.unwrap_or(telltale_machine::Value::Unit),
        ))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_machine::Value>,
        _payload: &telltale_machine::Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_machine::Value],
    ) -> EffectResult<String> {
        labels.first().cloned().map_or_else(
            || EffectResult::failure(EffectFailure::invalid_input("no labels")),
            EffectResult::success,
        )
    }

    fn step(&self, _role: &str, _state: &mut Vec<telltale_machine::Value>) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn topology_events(&self, tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        let events = if tick == 1 {
            vec![TopologyPerturbation::Partition {
                from: "A".to_string(),
                to: "B".to_string(),
            }]
        } else {
            Vec::new()
        };
        EffectResult::success(events)
    }
}

#[derive(Debug, Clone, Copy)]
struct InternalEffectReplayHandler;

impl EffectHandler for InternalEffectReplayHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[telltale_machine::Value],
    ) -> EffectResult<telltale_machine::Value> {
        EffectResult::success(telltale_machine::Value::Str(label.to_string()))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(
            input.payload.unwrap_or(telltale_machine::Value::Unit),
        ))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_machine::Value>,
        _payload: &telltale_machine::Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_machine::Value],
    ) -> EffectResult<String> {
        labels.first().cloned().map_or_else(
            || EffectResult::failure(EffectFailure::invalid_input("no labels")),
            EffectResult::success,
        )
    }

    fn step(&self, _role: &str, _state: &mut Vec<telltale_machine::Value>) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn output_condition_hint(
        &self,
        sid: usize,
        role: &str,
        _state: &[telltale_machine::Value],
    ) -> Option<OutputConditionHint> {
        Some(OutputConditionHint {
            predicate_ref: "machine.replay.internal_effects".to_string(),
            witness_ref: Some(format!("sid:{sid}:role:{role}")),
        })
    }

    fn supports_wal_sync(&self) -> bool {
        true
    }

    fn wal_sync(&self, _sync: &WalSyncRequest) -> EffectResult<()> {
        EffectResult::success(())
    }
}

#[derive(Debug, Clone, Copy)]
struct FailedInvokeHandler;

impl EffectHandler for FailedInvokeHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[telltale_machine::Value],
    ) -> EffectResult<telltale_machine::Value> {
        EffectResult::success(telltale_machine::Value::Unit)
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(
            input.payload.unwrap_or(telltale_machine::Value::Unit),
        ))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_machine::Value>,
        _payload: &telltale_machine::Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_machine::Value],
    ) -> EffectResult<String> {
        labels.first().cloned().map_or_else(
            || EffectResult::failure(EffectFailure::invalid_input("no labels")),
            EffectResult::success,
        )
    }

    fn step(&self, _role: &str, _state: &mut Vec<telltale_machine::Value>) -> EffectResult<()> {
        EffectResult::failure(EffectFailure::contract_violation("invoke failed"))
    }
}

#[derive(Debug, Clone, Copy)]
struct SendThenFaultHandler;

impl EffectHandler for SendThenFaultHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[telltale_machine::Value],
    ) -> EffectResult<telltale_machine::Value> {
        EffectResult::success(telltale_machine::Value::Str(label.to_string()))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(
            input.payload.unwrap_or(telltale_machine::Value::Unit),
        ))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_machine::Value>,
        _payload: &telltale_machine::Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_machine::Value],
    ) -> EffectResult<String> {
        labels.first().cloned().map_or_else(
            || EffectResult::failure(EffectFailure::invalid_input("no labels")),
            EffectResult::success,
        )
    }

    fn step(&self, role: &str, _state: &mut Vec<telltale_machine::Value>) -> EffectResult<()> {
        if role == "B" {
            EffectResult::failure(EffectFailure::contract_violation("late fault"))
        } else {
            EffectResult::success(())
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct ResumedSendHandler;

impl EffectHandler for ResumedSendHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[telltale_machine::Value],
    ) -> EffectResult<telltale_machine::Value> {
        EffectResult::success(telltale_machine::Value::Unit)
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(
            input.payload.unwrap_or(telltale_machine::Value::Unit),
        ))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<telltale_machine::Value>,
        _payload: &telltale_machine::Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[telltale_machine::Value],
    ) -> EffectResult<String> {
        labels.first().cloned().map_or_else(
            || EffectResult::failure(EffectFailure::invalid_input("no labels")),
            EffectResult::success,
        )
    }

    fn step(&self, _role: &str, _state: &mut Vec<telltale_machine::Value>) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn topology_events(&self, tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        let events = match tick {
            1 => vec![TopologyPerturbation::Partition {
                from: "A".to_string(),
                to: "B".to_string(),
            }],
            2 => vec![TopologyPerturbation::Heal {
                from: "A".to_string(),
                to: "B".to_string(),
            }],
            _ => Vec::new(),
        };
        EffectResult::success(events)
    }
}

fn semantic_effect_runner_path() -> Option<PathBuf> {
    let crate_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = crate_dir
        .parent()
        .and_then(Path::parent)
        .map(|root| root.join("lean/.lake/build/bin/semantic_effect_parity_runner"))?;
    path.is_file().then_some(path)
}

fn load_lean_fixtures() -> Option<Vec<ReducedSemanticEffectFixture>> {
    let runner = semantic_effect_runner_path()?;
    let output = Command::new(runner).output().ok()?;
    if !output.status.success() {
        return None;
    }
    let bundle: ReducedSemanticEffectBundle = serde_json::from_slice(&output.stdout).ok()?;
    assert_eq!(bundle.schema_version, "semantic_effect_parity_v1");
    Some(bundle.fixtures)
}

fn fixture_from_exchange(
    name: &str,
    effect_kind: &str,
    lifecycle: &str,
    exchange: &EffectExchangeRecord,
    publication_materialized: bool,
    output_predicate: Option<String>,
) -> ReducedSemanticEffectFixture {
    ReducedSemanticEffectFixture {
        name: name.to_string(),
        effect_kind: effect_kind.to_string(),
        lifecycle: lifecycle.to_string(),
        interface_name: exchange.request.metadata.interface_name.clone(),
        operation_name: exchange.request.metadata.operation_name.clone(),
        publication_materialized,
        output_predicate,
    }
}

fn blocked_send_fixture() -> ReducedSemanticEffectFixture {
    let mut blocked_machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    blocked_machine
        .load_choreography(&simple_send_recv_image("A", "B", "m"))
        .expect("load blocked-send machine");
    blocked_machine
        .step(&BlockedSendHandler)
        .expect("run blocked-send step");
    let blocked_effect = blocked_machine
        .outstanding_effects()
        .iter()
        .find(|effect| {
            effect.effect_kind == "send_decision"
                && effect.status == OutstandingEffectStatus::Blocked
        })
        .expect("blocked send effect");
    let blocked_exchange = blocked_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| exchange.effect_id == blocked_effect.effect_id)
        .expect("matching blocked send exchange");
    fixture_from_exchange(
        "blocked_send",
        "send_decision",
        "blocked",
        blocked_exchange,
        false,
        None,
    )
}

fn internal_effect_fixtures() -> Vec<ReducedSemanticEffectFixture> {
    let mut internal_machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    internal_machine
        .load_choreography(&simple_send_recv_image("A", "B", "m"))
        .expect("load internal-effects machine");
    internal_machine
        .run(&InternalEffectReplayHandler, 64)
        .expect("run internal-effects machine");
    let predicate = internal_machine
        .output_condition_checks()
        .first()
        .map(|check| check.meta.predicate_ref.clone());
    let send_success = internal_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| {
            matches!(
                exchange.request.body,
                EffectRequestBody::SendDecision { .. }
            ) && exchange.succeeded()
        })
        .expect("successful send exchange");
    let output_hint = internal_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| {
            matches!(
                exchange.request.body,
                EffectRequestBody::OutputConditionHint { .. }
            )
        })
        .expect("output-condition hint exchange");
    let wal_sync = internal_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| matches!(exchange.request.body, EffectRequestBody::WalSync { .. }))
        .expect("wal-sync exchange");
    let publication_materialized = !internal_machine
        .semantic_objects()
        .publication_events
        .is_empty()
        && internal_machine
            .semantic_objects()
            .canonical_handles
            .iter()
            .any(|handle| {
                matches!(
                    handle.kind,
                    telltale_machine::CanonicalHandleKind::Materialization
                )
            });
    vec![
        fixture_from_exchange(
            "send_publication",
            "send_decision",
            "succeeded",
            send_success,
            publication_materialized,
            predicate.clone(),
        ),
        fixture_from_exchange(
            "output_condition_hint",
            "output_condition_hint",
            "succeeded",
            output_hint,
            false,
            predicate,
        ),
        fixture_from_exchange("wal_sync", "wal_sync", "succeeded", wal_sync, false, None),
    ]
}

fn failed_invoke_fixture() -> ReducedSemanticEffectFixture {
    let failed_invoke_image = single_role_end_image(vec![
        Instr::Set {
            dst: 1,
            val: ImmValue::Nat(1),
        },
        Instr::Invoke {
            action: InvokeAction::Reg(1),
        },
        Instr::Halt,
    ]);
    let mut failed_invoke_machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    failed_invoke_machine
        .load_choreography(&failed_invoke_image)
        .expect("load failed invoke machine");
    assert!(
        failed_invoke_machine.run(&FailedInvokeHandler, 32).is_err(),
        "failed invoke run should fail closed"
    );
    let failed_invoke = failed_invoke_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| {
            matches!(exchange.request.body, EffectRequestBody::InvokeStep { .. })
                && !exchange.succeeded()
        })
        .expect("failed invoke exchange");
    fixture_from_exchange(
        "failed_invoke",
        "invoke_step",
        "failed",
        failed_invoke,
        false,
        None,
    )
}

fn send_then_fault_fixture() -> ReducedSemanticEffectFixture {
    let mut send_then_fault_machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    send_then_fault_machine
        .load_choreography(&simple_send_recv_image("A", "B", "m"))
        .expect("load send-then-fault machine");
    assert!(
        send_then_fault_machine
            .run(&SendThenFaultHandler, 64)
            .is_err(),
        "send-then-fault run should fail closed"
    );
    let send_before_fault = send_then_fault_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| {
            matches!(
                exchange.request.body,
                EffectRequestBody::SendDecision { .. }
            ) && exchange.succeeded()
        })
        .expect("send before fault exchange");
    fixture_from_exchange(
        "send_before_fault",
        "send_decision",
        "succeeded_then_faulted",
        send_before_fault,
        false,
        None,
    )
}

fn resumed_send_fixture() -> ReducedSemanticEffectFixture {
    let mut resumed_machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    resumed_machine
        .load_choreography(&simple_send_recv_image("A", "B", "m"))
        .expect("load resumed machine");
    resumed_machine
        .run(&ResumedSendHandler, 64)
        .expect("run resumed machine");
    let resumed_send = resumed_machine
        .effect_exchanges()
        .iter()
        .find(|exchange| {
            matches!(
                exchange.request.body,
                EffectRequestBody::SendDecision { .. }
            ) && exchange.succeeded()
        })
        .expect("resumed send exchange");
    fixture_from_exchange(
        "resumed_send",
        "send_decision",
        "resumed",
        resumed_send,
        false,
        None,
    )
}

fn machine_fixtures() -> Vec<ReducedSemanticEffectFixture> {
    let mut fixtures = vec![blocked_send_fixture()];
    fixtures.extend(internal_effect_fixtures());
    fixtures.push(failed_invoke_fixture());
    fixtures.push(send_then_fault_fixture());
    fixtures.push(resumed_send_fixture());
    fixtures.sort();
    fixtures
}

#[test]
fn machine_semantic_effects_match_lean_reduced_fixture_surface() {
    let Some(mut expected) = load_lean_fixtures() else {
        eprintln!(
            "semantic_effect_parity_runner not available; build with: cd lean && lake build semantic_effect_parity_runner"
        );
        return;
    };
    expected.sort();
    assert_eq!(machine_fixtures(), expected);
}
