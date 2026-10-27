// Shared actual-machine fixtures, included in the two existing backend modules.
use crate::effect::{EffectOutcomeStatus, EffectRequestBody, EffectResponse};
use crate::instr::{Instr, InvokeAction};
use crate::loader::CodeImage;
use std::collections::BTreeMap;
use std::sync::Mutex;
use telltale_types::{GlobalType, LocalTypeR};

struct OriginalReply(Mutex<Option<EffectOutcome>>);
impl EffectHandler for OriginalReply {
    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        match request.body {
            EffectRequestBody::InvokeStep { .. } | EffectRequestBody::Receive { .. } => self
                .0
                .lock()
                .unwrap()
                .take()
                .expect("one actual invocation"),
            EffectRequestBody::SendDecision { payload, .. } => {
                EffectOutcome::success(EffectResponse::SendDecision {
                    decision: SendDecision::Deliver(payload.unwrap_or(Value::Unit)),
                })
            }
            EffectRequestBody::TopologyEvents { .. } => {
                EffectOutcome::success(EffectResponse::TopologyEvents { events: vec![] })
            }
            EffectRequestBody::OutputConditionHint { .. } => {
                EffectOutcome::success(EffectResponse::OutputConditionHint { hint: None })
            }
            _ => EffectOutcome::failure(EffectFailure::contract_violation(
                "unexpected fixture request",
            )),
        }
    }
    fn handle_send(&self, _: &str, _: &str, _: &str, _: &[Value]) -> EffectResult<Value> {
        unreachable!("typed fixture")
    }
    fn handle_recv(
        &self,
        _: &str,
        _: &str,
        _: &str,
        _: &mut Vec<Value>,
        _: &Value,
    ) -> EffectResult<()> {
        unreachable!("typed fixture")
    }
    fn handle_choose(&self, _: &str, _: &str, _: &[String], _: &[Value]) -> EffectResult<String> {
        unreachable!("typed fixture")
    }
    fn step(&self, _: &str, _: &mut Vec<Value>) -> EffectResult<()> {
        unreachable!("typed fixture")
    }
}

fn original_image() -> CodeImage {
    CodeImage {
        programs: BTreeMap::from([(
            "A".into(),
            vec![
                Instr::Invoke {
                    action: InvokeAction::Named("runtime.step".into()),
                },
                Instr::Yield,
                Instr::Halt,
            ],
        )]),
        global_type: GlobalType::End,
        local_types: BTreeMap::from([("A".into(), LocalTypeR::End)]),
    }
}

#[test]
fn valid_invoke_commits_exact_state_and_advances_only_original_continuation() {
    let mut machine = make_machine();
    let target = machine.load_choreography(&original_image()).unwrap();
    let unrelated = machine.load_choreography(&original_image()).unwrap();
    let unrelated_before = snapshot(&machine, unrelated);
    let mut state = snapshot(&machine, target).1;
    state[1] = Value::Nat(42);
    let outcome = EffectOutcome::success(EffectResponse::InvokeStep {
        state: state.clone(),
    });
    let handler = OriginalReply(Mutex::new(Some(outcome.clone())));
    machine.step_round(&handler, 1).unwrap();
    let after = snapshot(&machine, target);
    assert_eq!(after.1, state);
    assert_eq!(after.2, 1);
    assert_eq!(snapshot(&machine, unrelated), unrelated_before);
    let exchange = machine
        .effect_exchanges()
        .iter()
        .find(|e| {
            e.request.session == Some(target)
                && matches!(e.request.body, EffectRequestBody::InvokeStep { .. })
        })
        .unwrap()
        .clone();
    assert_eq!(exchange.outcome, outcome);
    assert!(exchange.succeeded());
    assert!(machine
        .outstanding_effects()
        .iter()
        .any(|e| e.session == Some(target)
            && e.effect_kind == "invoke_step"
            && e.status == OutstandingEffectStatus::Succeeded));
}

#[test]
fn invalid_invoke_never_mutates_original_registers_or_unrelated_continuation() {
    let original_failure = EffectFailure::denied("original typed refusal");
    let poison = Some(EffectResponse::InvokeStep {
        state: vec![Value::Nat(999)],
    });
    let cases = [
        EffectOutcome {
            status: EffectOutcomeStatus::Failure {
                failure: original_failure.clone(),
            },
            response: poison.clone(),
        },
        EffectOutcome {
            status: EffectOutcomeStatus::Blocked,
            response: poison,
        },
        EffectOutcome::success(EffectResponse::Receive {
            state: vec![Value::Nat(999)],
        }),
        EffectOutcome::success(EffectResponse::Release),
        EffectOutcome {
            status: EffectOutcomeStatus::Success,
            response: None,
        },
    ];
    for outcome in cases {
        let mut machine = make_machine();
        let target = machine.load_choreography(&original_image()).unwrap();
        let unrelated = machine.load_choreography(&original_image()).unwrap();
        let before = snapshot(&machine, target);
        let unrelated_before = snapshot(&machine, unrelated);
        let handler = OriginalReply(Mutex::new(Some(outcome.clone())));
        assert!(machine.step_round(&handler, 1).is_err());
        let after = snapshot(&machine, target);
        assert_eq!(
            (after.0, &after.1, after.2),
            (before.0, &before.1, before.2)
        );
        assert_eq!(snapshot(&machine, unrelated), unrelated_before);
        let CoroStatus::Faulted(Fault::Invoke { failure }) = after.3 else {
            panic!("actual invoke fault required")
        };
        if matches!(outcome.status, EffectOutcomeStatus::Failure { .. }) {
            assert_eq!(failure, original_failure);
        }
        let exchange = machine
            .effect_exchanges()
            .iter()
            .find(|e| {
                e.request.session == Some(target)
                    && matches!(e.request.body, EffectRequestBody::InvokeStep { .. })
            })
            .unwrap()
            .clone();
        assert_eq!(exchange.outcome, outcome);
        assert!(!exchange.succeeded());
        assert!(machine
            .outstanding_effects()
            .iter()
            .all(|e| e.session != Some(target)
                || e.effect_kind != "invoke_step"
                || e.status != OutstandingEffectStatus::Succeeded));
        assert!(!machine
            .semantic_objects()
            .publication_events
            .iter()
            .any(|event| event.session == Some(target) && event.publication == "effect.succeeded"));
        if matches!(outcome.status, EffectOutcomeStatus::Blocked) {
            assert!(machine
                .outstanding_effects()
                .iter()
                .any(|e| e.session == Some(target)
                    && e.effect_kind == "invoke_step"
                    && e.status == OutstandingEffectStatus::Blocked));
        } else {
            assert!(machine
                .outstanding_effects()
                .iter()
                .any(|e| e.session == Some(target)
                    && e.effect_kind == "invoke_step"
                    && e.status == OutstandingEffectStatus::Failed));
        }
    }
}

fn receive_image() -> CodeImage {
    use telltale_types::Label;
    CodeImage {
        programs: BTreeMap::from([
            (
                "A".into(),
                vec![Instr::Send { chan: 0, val: 1 }, Instr::Halt],
            ),
            (
                "B".into(),
                vec![
                    Instr::Receive { chan: 0, dst: 1 },
                    Instr::Yield,
                    Instr::Halt,
                ],
            ),
        ]),
        global_type: GlobalType::send("A", "B", Label::new("m"), GlobalType::End),
        local_types: BTreeMap::from([
            (
                "A".into(),
                LocalTypeR::send("B", Label::new("m"), LocalTypeR::End),
            ),
            (
                "B".into(),
                LocalTypeR::recv("A", Label::new("m"), LocalTypeR::End),
            ),
        ]),
    }
}

fn receive_case_outcome(case: usize, state: Vec<Value>) -> EffectOutcome {
    let response = Some(EffectResponse::Receive { state });
    match case {
        0 => EffectOutcome {
            status: EffectOutcomeStatus::Success,
            response,
        },
        1 => EffectOutcome {
            status: EffectOutcomeStatus::Failure {
                failure: EffectFailure::denied("original receive failure"),
            },
            response,
        },
        2 => EffectOutcome {
            status: EffectOutcomeStatus::Blocked,
            response,
        },
        3 => EffectOutcome::success(EffectResponse::Release),
        4 => EffectOutcome::success(EffectResponse::Receive { state: vec![] }),
        _ => EffectOutcome {
            status: EffectOutcomeStatus::Success,
            response,
        },
    }
}

#[test]
fn actual_receive_state_and_continuation_require_exact_success() {
    for case in 0..7 {
        let mut machine = make_machine();
        let target = machine.load_choreography(&receive_image()).unwrap();
        let original = snapshot_role(&machine, target, "B");
        let mut expected = original.1.clone();
        expected[2] = Value::Nat(42);
        if case == 5 {
            // A present destination alone cannot authorize changing configured width.
            expected.truncate(2);
        }
        if case == 6 {
            expected.push(Value::Unit);
        }
        let outcome = receive_case_outcome(case, expected.clone());
        let handler = OriginalReply(Mutex::new(Some(outcome.clone())));
        // Actual Send enqueues the original signed payload before the selected Receive.
        machine.step_round(&handler, 1).unwrap();
        assert!(handler.0.lock().unwrap().is_some());
        let unrelated = machine.load_choreography(&original_image()).unwrap();
        let other = snapshot(&machine, unrelated);
        let sender = snapshot_role(&machine, target, "A");
        let result = machine.step_round(&handler, 1);
        let after = snapshot_role(&machine, target, "B");
        assert_eq!(snapshot(&machine, unrelated), other);
        let sender_after = snapshot_role(&machine, target, "A");
        assert_eq!(
            (sender_after.0, sender_after.1, sender_after.2),
            (sender.0, sender.1, sender.2)
        );
        if case == 0 {
            assert!(result.is_ok());
            expected[1] = Value::Unit;
            assert_eq!(after.1, expected);
            assert_eq!(after.2, 1);
        } else {
            assert!(result.is_err());
            assert_eq!(
                (after.0, &after.1, after.2),
                (original.0, &original.1, original.2)
            );
            assert!(machine
                .outstanding_effects()
                .iter()
                .all(|e| e.session != Some(target)
                    || e.effect_kind != "handle_recv"
                    || e.status != OutstandingEffectStatus::Succeeded));
        }
        let exchange = machine
            .effect_exchanges()
            .iter()
            .find(|e| {
                e.request.session == Some(target)
                    && matches!(e.request.body, EffectRequestBody::Receive { .. })
            })
            .unwrap();
        assert_eq!(exchange.outcome, outcome);
        assert_eq!(exchange.succeeded(), case == 0);
        let accepted = machine
            .outstanding_effects()
            .iter()
            .find(|effect| effect.effect_id == exchange.effect_id)
            .unwrap();
        if case != 0 {
            assert!(!machine
                .semantic_objects()
                .publication_events
                .iter()
                .any(|event| event.operation_id == accepted.operation_id
                    && event.publication == "effect.succeeded"));
        }

        assert!(matches!(
            exchange.request.body,
            EffectRequestBody::Receive {
                destination: Some(1),
                ..
            }
        ));
    }
}

#[test]
fn disabled_observability_never_replaces_original_failure_or_blocked_behavior() {
    for receive in [false, true] {
        for blocked in [false, true] {
            let config = ProtocolMachineConfig {
                observability_retention: crate::ObservabilityRetentionConfig {
                    mode: crate::ObservabilityRetentionMode::Disabled,
                    ..crate::ObservabilityRetentionConfig::default()
                },
                ..ProtocolMachineConfig::default()
            };
            let mut machine = make_machine_with_config(config);
            let image = if receive {
                receive_image()
            } else {
                original_image()
            };
            let target = machine.load_choreography(&image).unwrap();
            let role = if receive { "B" } else { "A" };
            let original = snapshot_role(&machine, target, role);
            let failure = EffectFailure::denied("original retained-disabled refusal");
            let response = if receive {
                EffectResponse::Receive {
                    state: vec![Value::Nat(999)],
                }
            } else {
                EffectResponse::InvokeStep {
                    state: vec![Value::Nat(999)],
                }
            };
            let outcome = EffectOutcome {
                status: if blocked {
                    EffectOutcomeStatus::Blocked
                } else {
                    EffectOutcomeStatus::Failure {
                        failure: failure.clone(),
                    }
                },
                response: Some(response),
            };
            let handler = OriginalReply(Mutex::new(Some(outcome)));
            if receive {
                machine.step_round(&handler, 1).unwrap();
                assert!(handler.0.lock().unwrap().is_some());
            }
            let error = machine.step_round(&handler, 1).unwrap_err();
            match error {
                ProtocolMachineError::Fault {
                    fault: Fault::Invoke { failure: actual },
                    ..
                } if !blocked => assert_eq!(actual, failure),
                ProtocolMachineError::Fault {
                    fault: Fault::Invoke { failure: actual },
                    ..
                } => assert!(actual.message.contains("blocked")),
                other => panic!("unexpected original outcome: {other:?}"),
            }
            let after = snapshot_role(&machine, target, role);
            assert_eq!(
                (after.0, &after.1, after.2),
                (original.0, &original.1, original.2)
            );
            // Retention storage differs between backends; semantic failure must not.
        }
    }
}

fn branch_image() -> CodeImage {
    use telltale_types::Label;
    CodeImage {
        programs: BTreeMap::from([
            (
                "A".into(),
                vec![
                    Instr::Offer {
                        chan: 0,
                        label: "m".into(),
                    },
                    Instr::Halt,
                ],
            ),
            (
                "B".into(),
                vec![
                    Instr::Choose {
                        chan: 0,
                        table: vec![("m".into(), 1)],
                    },
                    Instr::Yield,
                    Instr::Halt,
                ],
            ),
        ]),
        global_type: GlobalType::comm("A", "B", vec![(Label::new("m"), GlobalType::End)]),
        local_types: BTreeMap::from([
            (
                "A".into(),
                LocalTypeR::send_choice("B", vec![(Label::new("m"), None, LocalTypeR::End)]),
            ),
            (
                "B".into(),
                LocalTypeR::recv_choice("A", vec![(Label::new("m"), None, LocalTypeR::End)]),
            ),
        ]),
    }
}

#[test]
fn all_vm_state_replacers_require_actual_configured_width_before_publication() {
    for producer in 0..3 {
        for width_case in 0..4 {
            let config = ProtocolMachineConfig {
                num_registers: 4,
                ..ProtocolMachineConfig::default()
            };
            let mut machine = make_machine_with_config(config);
            let image = match producer {
                0 => original_image(),
                1 => receive_image(),
                _ => branch_image(),
            };
            let target = machine.load_choreography(&image).unwrap();
            let role = if producer == 0 { "A" } else { "B" };
            let before = snapshot_role(&machine, target, role);
            let mut state = before.1.clone();
            match width_case {
                0 => state.clear(),
                1 => state.truncate(2), // destination exists, width is nevertheless invalid
                2 => state.push(Value::Unit),
                _ => state[2] = Value::Nat(42),
            }
            let outcome = EffectOutcome::success(if producer == 0 {
                EffectResponse::InvokeStep {
                    state: state.clone(),
                }
            } else {
                EffectResponse::Receive {
                    state: state.clone(),
                }
            });
            let handler = OriginalReply(Mutex::new(Some(outcome.clone())));
            if producer != 0 {
                machine.step_round(&handler, 1).unwrap();
                assert!(handler.0.lock().unwrap().is_some());
            }
            let unrelated = machine.load_choreography(&original_image()).unwrap();
            let other = snapshot(&machine, unrelated);
            let result = machine.step_round(&handler, 1);
            assert!(
                handler.0.lock().unwrap().is_none(),
                "actual state callback consumed original response"
            );
            let after = snapshot_role(&machine, target, role);
            assert_eq!(snapshot(&machine, unrelated), other);
            if width_case == 3 {
                assert!(result.is_ok());
                if producer == 1 {
                    state[1] = Value::Unit;
                }
                assert_eq!(after.1, state);
                assert_eq!(after.2, 1);
            } else {
                assert!(result.is_err());
                assert_eq!(
                    (after.0, &after.1, after.2),
                    (before.0, &before.1, before.2)
                );
                let CoroStatus::Faulted(Fault::Invoke { failure }) = after.3 else {
                    panic!("state applicability fault required")
                };
                assert!(failure.message.contains("register width"));
            }
            assert_state_exchange(&machine, target, &outcome, producer, 4, width_case == 3);
        }
    }
}

fn assert_state_exchange(
    machine: &FixtureMachine,
    target: usize,
    outcome: &EffectOutcome,
    producer: usize,
    width: u16,
    accepted_success: bool,
) {
    let exchange = machine
        .effect_exchanges()
        .iter()
        .find(|e| {
            e.request.session == Some(target)
                && if producer == 0 {
                    matches!(e.request.body, EffectRequestBody::InvokeStep { .. })
                } else {
                    matches!(e.request.body, EffectRequestBody::Receive { .. })
                }
        })
        .unwrap();
    assert_eq!(&exchange.outcome, outcome);
    assert_eq!(exchange.succeeded(), accepted_success);
    match exchange.request.body {
        EffectRequestBody::InvokeStep { register_width, .. } => {
            assert_eq!(register_width, Some(width))
        }
        EffectRequestBody::Receive {
            register_width,
            destination,
            ..
        } => {
            assert_eq!(register_width, Some(width));
            assert_eq!(destination, if producer == 1 { Some(1) } else { None });
        }
        _ => panic!("actual state request required"),
    }
    let accepted = machine
        .outstanding_effects()
        .iter()
        .find(|e| e.effect_id == exchange.effect_id)
        .unwrap();
    assert_eq!(
        accepted.status,
        if accepted_success {
            OutstandingEffectStatus::Succeeded
        } else {
            OutstandingEffectStatus::Failed
        }
    );
    assert_eq!(
        machine
            .semantic_objects()
            .publication_events
            .iter()
            .any(|event| event.operation_id == accepted.operation_id
                && event.publication == "effect.succeeded"),
        accepted_success
    );
}

struct OriginalFamilyReply {
    family: &'static str,
    outcome: Mutex<Option<EffectOutcome>>,
}
impl EffectHandler for OriginalFamilyReply {
    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        let family = match request.body {
            EffectRequestBody::Acquire { .. } => "acquire",
            EffectRequestBody::Release { .. } => "release",
            EffectRequestBody::SendDecision { .. } => "send",
            EffectRequestBody::TopologyEvents { .. } => {
                return EffectOutcome::success(EffectResponse::TopologyEvents { events: vec![] })
            }
            EffectRequestBody::OutputConditionHint { .. } => {
                return EffectOutcome::success(EffectResponse::OutputConditionHint { hint: None })
            }
            _ => panic!("unexpected family fixture request"),
        };
        assert_eq!(family, self.family);
        self.outcome
            .lock()
            .unwrap()
            .take()
            .expect("one actual selected host callback")
    }
    fn handle_send(&self, _: &str, _: &str, _: &str, _: &[Value]) -> EffectResult<Value> {
        unreachable!("typed fixture")
    }
    fn handle_recv(
        &self,
        _: &str,
        _: &str,
        _: &str,
        _: &mut Vec<Value>,
        _: &Value,
    ) -> EffectResult<()> {
        unreachable!("typed fixture")
    }
    fn handle_choose(&self, _: &str, _: &str, _: &[String], _: &[Value]) -> EffectResult<String> {
        unreachable!("typed fixture")
    }
    fn step(&self, _: &str, _: &mut Vec<Value>) -> EffectResult<()> {
        unreachable!("typed fixture")
    }
}

#[test]
fn original_guard_and_send_outcomes_survive_every_retention_policy() {
    for mode in [
        crate::ObservabilityRetentionMode::Full,
        crate::ObservabilityRetentionMode::Disabled,
        crate::ObservabilityRetentionMode::Capped,
    ] {
        for family in ["acquire", "release", "send"] {
            for blocked in [false, true] {
                let config = ProtocolMachineConfig {
                    observability_retention: crate::ObservabilityRetentionConfig {
                        mode,
                        capacity: 1,
                    },
                    ..ProtocolMachineConfig::default()
                };
                let mut machine = make_machine_with_config(config);
                let mut image = if family == "send" {
                    receive_image()
                } else {
                    original_image()
                };
                if family != "send" {
                    image.programs.get_mut("A").unwrap()[0] = if family == "acquire" {
                        Instr::Acquire {
                            layer: "guard".into(),
                            dst: 1,
                        }
                    } else {
                        Instr::Release {
                            layer: "guard".into(),
                            evidence: 1,
                        }
                    };
                }
                let target = machine.load_choreography(&image).unwrap();
                let before = snapshot(&machine, target);
                let failure = EffectFailure::denied("original host family refusal");
                let response = Some(match family {
                    "acquire" => EffectResponse::Acquire {
                        evidence: Value::Unit,
                    },
                    "release" => EffectResponse::Release,
                    _ => EffectResponse::SendDecision {
                        decision: SendDecision::Drop,
                    },
                });
                let outcome = EffectOutcome {
                    status: if blocked {
                        EffectOutcomeStatus::Blocked
                    } else {
                        EffectOutcomeStatus::Failure {
                            failure: failure.clone(),
                        }
                    },
                    response,
                };
                let handler = OriginalFamilyReply {
                    family,
                    outcome: Mutex::new(Some(outcome)),
                };
                let result = machine.step_round(&handler, 1);
                assert!(
                    handler.outcome.lock().unwrap().is_none(),
                    "actual selected callback consumed original outcome"
                );
                let after = snapshot(&machine, target);
                assert_eq!(
                    (after.0, &after.1, after.2),
                    (before.0, &before.1, before.2)
                );
                if family == "acquire" && blocked && !blocked_acquire_is_fault() {
                    assert!(result.is_ok());
                    assert!(matches!(
                        after.3,
                        CoroStatus::Blocked(BlockReason::AcquireDenied { .. })
                    ));
                } else {
                    let error = result.unwrap_err();
                    let actual = match error {
                        ProtocolMachineError::Fault {
                            fault: Fault::Acquire { failure, .. } | Fault::Invoke { failure },
                            ..
                        } => failure,
                        other => panic!("unexpected host family fault: {other:?}"),
                    };
                    if blocked {
                        assert!(actual.message.contains("blocked"));
                    } else {
                        assert_eq!(actual, failure);
                    }
                }
            }
        }
    }
}
