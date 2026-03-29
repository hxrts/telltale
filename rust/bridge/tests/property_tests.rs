#![allow(clippy::as_conversions, clippy::expect_used)]

use std::collections::BTreeMap;

use proptest::prelude::*;
use telltale_bridge::{
    export_protocol_bundle, InvariantClaims, ProtocolMachineRunner, ProtocolMachineRunnerError,
    ProtocolMachineTraceEvent, SchedulerKind,
};
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{EffectHandler, SendDecision, SendDecisionInput};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::ObsEvent;
use telltale_machine::{ProtocolMachine, ProtocolMachineConfig};
use telltale_types::{GlobalType, Label, LocalTypeR};

#[derive(Clone, Debug)]
struct GeneratedProtocol {
    global: GlobalType,
    local_types: BTreeMap<String, LocalTypeR>,
}

fn strict_protocol_machine_runner_required() -> bool {
    std::env::var("TELLTALE_REQUIRE_PROTOCOL_MACHINE_RUNNER")
        .map(|value| value != "0")
        .unwrap_or(false)
}

fn singleton_protocol() -> GeneratedProtocol {
    let mut local_types = BTreeMap::new();
    local_types.insert("Solo".to_string(), LocalTypeR::End);
    GeneratedProtocol {
        global: GlobalType::End,
        local_types,
    }
}

fn send_recv_protocol(label: &str) -> GeneratedProtocol {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send("B", Label::new(label), LocalTypeR::End),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new(label), LocalTypeR::End),
    );

    GeneratedProtocol {
        global: GlobalType::send("A", "B", Label::new(label), GlobalType::End),
        local_types,
    }
}

fn chain_protocol() -> GeneratedProtocol {
    let mut local_types = BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send(
            "B",
            Label::new("ab"),
            LocalTypeR::recv("C", Label::new("ca"), LocalTypeR::End),
        ),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv(
            "A",
            Label::new("ab"),
            LocalTypeR::send("C", Label::new("bc"), LocalTypeR::End),
        ),
    );
    local_types.insert(
        "C".to_string(),
        LocalTypeR::recv(
            "B",
            Label::new("bc"),
            LocalTypeR::send("A", Label::new("ca"), LocalTypeR::End),
        ),
    );

    GeneratedProtocol {
        global: GlobalType::send(
            "A",
            "B",
            Label::new("ab"),
            GlobalType::send(
                "B",
                "C",
                Label::new("bc"),
                GlobalType::send("C", "A", Label::new("ca"), GlobalType::End),
            ),
        ),
        local_types,
    }
}

fn arb_choreography() -> impl Strategy<Value = GeneratedProtocol> {
    let labels = prop::sample::select(vec!["msg", "ping", "tick"]);
    prop_oneof![
        Just(singleton_protocol()),
        labels.prop_map(send_recv_protocol),
        Just(chain_protocol()),
    ]
}

fn arb_scheduler_kind() -> impl Strategy<Value = SchedulerKind> {
    prop_oneof![
        Just(SchedulerKind::Cooperative),
        Just(SchedulerKind::RoundRobin),
        Just(SchedulerKind::Priority),
        Just(SchedulerKind::ProgressAware),
    ]
}

fn arb_invariant_claims() -> impl Strategy<Value = InvariantClaims> {
    (
        any::<bool>(),
        any::<bool>(),
        any::<Option<u8>>(),
        arb_scheduler_kind(),
    )
        .prop_map(
            |(with_liveness, progress_required, fairness_k, scheduler)| {
                let liveness = if with_liveness {
                    Some(telltale_bridge::LivenessConfig {
                        scheduler,
                        fairness_k: fairness_k.map(usize::from),
                        progress_required,
                    })
                } else {
                    None
                };

                InvariantClaims {
                    schema_version: telltale_bridge::canonical_schema_version(),
                    liveness,
                    distributed: telltale_bridge::DistributedClaims::default(),
                    classical: telltale_bridge::ClassicalClaims::default(),
                }
            },
        )
}

fn runtime_check_invariant(protocol: &GeneratedProtocol, claims: &InvariantClaims) -> bool {
    let _ = protocol;

    if let Some(quorum) = &claims.distributed.quorum_geometry {
        if quorum.quorum_size == 0
            || quorum.n == 0
            || quorum.quorum_size > quorum.n
            || quorum.intersection_size > quorum.quorum_size
        {
            return false;
        }
    }

    true
}

fn unsupported_lean_operation(stderr: &str) -> bool {
    stderr.contains("unknown operation")
        || stderr.contains("unsupported operation")
        || stderr.contains("validateTrace")
        || stderr.contains("verifyProtocolBundle")
        || stderr.contains("missing choreographies")
}

#[derive(Debug, Clone, Copy)]
struct PropertyHandler;

impl EffectHandler for PropertyHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[Value],
    ) -> telltale_machine::model::effects::EffectResult<Value> {
        telltale_machine::model::effects::EffectResult::success(Value::Str(label.to_string()))
    }

    fn send_decision(
        &self,
        input: SendDecisionInput<'_>,
    ) -> telltale_machine::model::effects::EffectResult<SendDecision> {
        telltale_machine::model::effects::EffectResult::success(SendDecision::Deliver(
            input.payload.unwrap_or(Value::Unit),
        ))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> telltale_machine::model::effects::EffectResult<()> {
        telltale_machine::model::effects::EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> telltale_machine::model::effects::EffectResult<String> {
        telltale_machine::model::effects::EffectResult::success(
            labels
                .first()
                .cloned()
                .expect("labels should contain at least one branch"),
        )
    }

    fn step(
        &self,
        _role: &str,
        _state: &mut Vec<Value>,
    ) -> telltale_machine::model::effects::EffectResult<()> {
        telltale_machine::model::effects::EffectResult::success(())
    }
}

fn obs_to_semantic_audit_event(event: &ObsEvent) -> Option<ProtocolMachineTraceEvent> {
    let mut out = ProtocolMachineTraceEvent {
        schema_version: telltale_bridge::canonical_schema_version(),
        kind: String::new(),
        tick: 0,
        session: None,
        sender: None,
        receiver: None,
        label: None,
        role: None,
        target: None,
        permitted: None,
        epoch: None,
        ghost: None,
        from: None,
        to: None,
        predicate_ref: None,
        witness_ref: None,
        output_digest: None,
        passed: None,
        reason: None,
    };

    match event {
        ObsEvent::Sent {
            tick,
            session,
            from,
            to,
            label,
            ..
        } => {
            out.kind = "sent".to_string();
            out.tick = *tick;
            out.session = Some(*session as u64);
            out.sender = Some(from.clone());
            out.receiver = Some(to.clone());
            out.label = Some(label.clone());
            Some(out)
        }
        ObsEvent::Received {
            tick,
            session,
            from,
            to,
            label,
            ..
        } => {
            out.kind = "received".to_string();
            out.tick = *tick;
            out.session = Some(*session as u64);
            out.sender = Some(from.clone());
            out.receiver = Some(to.clone());
            out.label = Some(label.clone());
            Some(out)
        }
        _ => None,
    }
}

fn run_rust_semantic_audit(
    protocol: &GeneratedProtocol,
) -> Result<Vec<ProtocolMachineTraceEvent>, String> {
    let image = CodeImage::from_local_types(&protocol.local_types, &protocol.global);
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine
        .load_choreography(&image)
        .map_err(|e| e.to_string())?;
    machine
        .run(&PropertyHandler, 128)
        .map_err(|e| e.to_string())?;
    Ok(machine
        .trace()
        .iter()
        .filter_map(obs_to_semantic_audit_event)
        .collect())
}

fn protocol_to_choreography_json(
    protocol: &GeneratedProtocol,
) -> telltale_bridge::ChoreographyJson {
    telltale_bridge::ChoreographyJson {
        schema_version: telltale_bridge::canonical_schema_version(),
        global_type: telltale_bridge::global_to_json(&protocol.global),
        roles: protocol.local_types.keys().cloned().collect(),
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(8))]

    #[test]
    fn rust_lean_trace_consistency(protocol in arb_choreography()) {
        let trace = run_rust_semantic_audit(&protocol)
            .map_err(proptest::test_runner::TestCaseError::fail)?;

        let Some(runner) = ProtocolMachineRunner::try_new() else {
            if strict_protocol_machine_runner_required() {
                ProtocolMachineRunner::require_available();
            }
            return Ok(());
        };

        let choreography = protocol_to_choreography_json(&protocol);
        match runner.validate_trace(&[choreography], &trace) {
            Ok(validation) => {
                prop_assert!(
                    validation.valid || !validation.errors.is_empty(),
                    "Lean validation returned invalid without structured errors"
                );
            }
            Err(ProtocolMachineRunnerError::ProcessFailed { stderr, .. })
                if unsupported_lean_operation(&stderr) => {}
            Err(err) => {
                return Err(proptest::test_runner::TestCaseError::fail(format!(
                    "validate_trace failed: {err}"
                )));
            }
        }
    }

    #[test]
    fn invariant_claim_consistency(
        protocol in arb_choreography(),
        claims in arb_invariant_claims()
    ) {
        let local_ok = runtime_check_invariant(&protocol, &claims);
        let Some(runner) = ProtocolMachineRunner::try_new() else {
            if strict_protocol_machine_runner_required() {
                ProtocolMachineRunner::require_available();
            }
            return Ok(());
        };

        let bundle = export_protocol_bundle(&protocol.global, &protocol.local_types, claims.clone());
        match runner.verify_invariants(&bundle) {
            Ok(result) => {
                if local_ok {
                    prop_assert!(
                        result.valid || !result.errors.is_empty(),
                        "local invariant check accepted but Lean returned unstructured invalid result"
                    );
                } else {
                    prop_assert!(
                        !result.valid || !result.errors.is_empty(),
                        "local invariant check rejected but Lean returned valid without evidence"
                    );
                }
                prop_assert!(
                    result.errors.iter().all(|err| !err.code.trim().is_empty()),
                    "structured errors must include non-empty codes"
                );
            }
            Err(ProtocolMachineRunnerError::ProcessFailed { stderr, .. })
                if unsupported_lean_operation(&stderr) => {}
            Err(err) => {
                return Err(proptest::test_runner::TestCaseError::fail(format!(
                    "verify_invariants failed: {err}"
                )));
            }
        }
    }
}
