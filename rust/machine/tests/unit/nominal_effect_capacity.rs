// Shared actual backend owner tests; no source compiler or public counter setter.
use crate::effect::{EffectRequestBody, EffectResponse};
use crate::nominal_command::{
    NominalCommandCall, NominalCommandDeclaration, NominalCommandReply, NominalCommandValue,
    NominalContinuationView,
};

#[derive(Clone)]
enum NominalBoundaryReply {
    Blocked,
    Failure(EffectFailure),
    Returned(Result<NominalCommandValue, String>),
}
struct NominalBoundaryHandler {
    change_identity_on_failure: bool,
    identity_changed: std::sync::atomic::AtomicBool,
    calls: std::sync::Mutex<Vec<EffectRequest>>,
    returned: std::sync::Mutex<Vec<(EffectRequest, EffectOutcome)>>,
    replies: std::sync::Mutex<std::collections::VecDeque<NominalBoundaryReply>>,
}
impl NominalBoundaryHandler {
    fn new(replies: Vec<NominalBoundaryReply>) -> Self {
        Self {
            change_identity_on_failure: false,
            identity_changed: std::sync::atomic::AtomicBool::new(false),
            calls: Default::default(),
            returned: Default::default(),
            replies: std::sync::Mutex::new(replies.into()),
        }
    }
    fn nominal_requests(&self) -> Vec<EffectRequest> {
        self.calls
            .lock()
            .unwrap()
            .iter()
            .filter(|request| matches!(&request.body, EffectRequestBody::NominalCommand { .. }))
            .cloned()
            .collect()
    }
    fn wals(&self) -> usize {
        self.calls
            .lock()
            .unwrap()
            .iter()
            .filter(|request| matches!(&request.body, EffectRequestBody::WalSync { .. }))
            .count()
    }
    fn hints(&self) -> usize {
        self.calls
            .lock()
            .unwrap()
            .iter()
            .filter(|request| {
                matches!(&request.body, EffectRequestBody::OutputConditionHint { .. })
            })
            .count()
    }
}
impl EffectHandler for NominalBoundaryHandler {
    fn supports_wal_sync(&self) -> bool {
        true
    }
    fn handler_identity(&self) -> String {
        if self
            .identity_changed
            .load(std::sync::atomic::Ordering::SeqCst)
        {
            "changed-nominal-capacity-handler".into()
        } else {
            "original-nominal-capacity-handler".into()
        }
    }
    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        self.calls.lock().unwrap().push(request.clone());
        let original_request = request.clone();
        let outcome = match request.body {
            EffectRequestBody::WalSync { .. } => EffectOutcome::success(EffectResponse::WalSync),
            EffectRequestBody::TopologyEvents { .. } => {
                EffectOutcome::success(EffectResponse::TopologyEvents { events: vec![] })
            }
            EffectRequestBody::OutputConditionHint { .. } => {
                EffectOutcome::success(EffectResponse::OutputConditionHint { hint: None })
            }
            EffectRequestBody::NominalCommand { request } => {
                match self
                    .replies
                    .lock()
                    .unwrap()
                    .pop_front()
                    .expect("no extra original callback")
                {
                    NominalBoundaryReply::Blocked => EffectOutcome::blocked(),
                    NominalBoundaryReply::Failure(failure) => {
                        if self.change_identity_on_failure {
                            self.identity_changed
                                .store(true, std::sync::atomic::Ordering::SeqCst);
                        }
                        EffectOutcome::failure(failure)
                    }
                    NominalBoundaryReply::Returned(result) => {
                        EffectOutcome::success(EffectResponse::NominalCommand {
                            reply: NominalCommandReply {
                                invocation: request.invocation,
                                result,
                            },
                        })
                    }
                }
            }
            _ => panic!("unexpected callback before actual nominal terminal branch"),
        };
        self.returned
            .lock()
            .unwrap()
            .push((original_request, outcome.clone()));
        outcome
    }
    fn handle_send(&self, _: &str, _: &str, _: &str, _: &[Value]) -> EffectResult<Value> {
        unreachable!()
    }
    fn handle_recv(
        &self,
        _: &str,
        _: &str,
        _: &str,
        _: &mut Vec<Value>,
        _: &Value,
    ) -> EffectResult<()> {
        unreachable!()
    }
    fn handle_choose(&self, _: &str, _: &str, _: &[String], _: &[Value]) -> EffectResult<String> {
        unreachable!()
    }
    fn step(&self, _: &str, _: &mut Vec<Value>) -> EffectResult<()> {
        panic!("nominal must not use generic step")
    }
}

const NOMINAL_BOUNDARY_BUDGET: u64 = 8;

fn nominal_boundary_retentions() -> [crate::engine::ObservabilityRetentionConfig; 3] {
    use crate::engine::{ObservabilityRetentionConfig, ObservabilityRetentionMode};
    [
        ObservabilityRetentionMode::Full,
        ObservabilityRetentionMode::Disabled,
        ObservabilityRetentionMode::Capped,
    ]
    .map(|mode| ObservabilityRetentionConfig { mode, capacity: 1 })
}

fn nominal_boundary_image() -> CodeImage {
    use crate::semantic_objects::{
        AgreementEvidenceKind, AgreementLevel, AgreementProfile, AgreementRule, OperationVisibility,
    };
    let declaration = NominalCommandDeclaration {
        interface: "Host".into(),
        operation: "ready".into(),
        may_block: true,
        readiness_predicate: None,
    };
    let call = NominalCommandCall {
        declaration: declaration.clone(),
        enclosing_operation: "Check".into(),
        role: "A".into(),
        agreement_profile: AgreementProfile {
            profile_name: "ImmediateLocal".into(),
            visibility: OperationVisibility::Immediate,
            rule: AgreementRule::NoAgreement,
            usable_at: AgreementLevel::None,
            finalized_at: AgreementLevel::None,
            required_evidence_kind: AgreementEvidenceKind::Witness,
        },
        progress_contract: "original-progress".into(),
        progress_window: "original-window".into(),
        budget_ticks: std::num::NonZeroU64::new(NOMINAL_BOUNDARY_BUDGET).unwrap(),
        result: 1,
        on_ok: 2,
        on_err: 4,
    };
    let global = telltale_types::GlobalType::Comm {
        sender: "A".into(),
        receiver: "B".into(),
        branches: vec![
            (
                telltale_types::Label::new("Ready"),
                telltale_types::GlobalType::End,
            ),
            (
                telltale_types::Label::new("Denied"),
                telltale_types::GlobalType::End,
            ),
        ],
    };
    let local_types = telltale_theory::projection::project_all(&global)
        .unwrap()
        .into_iter()
        .collect();
    CodeImage {
        global_type: global,
        local_types,
        programs: BTreeMap::from([
            (
                "A".into(),
                vec![
                    Instr::Invoke {
                        action: crate::instr::InvokeAction::DeclareCommand(declaration),
                    },
                    Instr::Invoke {
                        action: crate::instr::InvokeAction::NominalCommand(Box::new(call)),
                    },
                    Instr::Offer {
                        chan: 0,
                        label: "Ready".into(),
                    },
                    Instr::Halt,
                    Instr::Offer {
                        chan: 0,
                        label: "Denied".into(),
                    },
                    Instr::Halt,
                ],
            ),
            (
                "B".into(),
                vec![
                    Instr::Choose {
                        chan: 0,
                        table: vec![("Ready".into(), 1), ("Denied".into(), 1)],
                    },
                    Instr::Halt,
                ],
            ),
        ]),
    }
}

fn nominal_boundary_coroutine(machine: &NominalCapacityMachine) -> Coroutine {
    machine
        .coroutines()
        .iter()
        .find(|coro| coro.role == "A")
        .unwrap()
        .clone()
}
fn nominal_boundary_original(machine: &NominalCapacityMachine) -> NominalContinuationView {
    nominal_boundary_coroutine(machine)
        .nominal_continuation_view()
        .expect("actual original continuation")
}
fn prepare_nominal_boundary(
    handler: &NominalBoundaryHandler,
    retention: crate::engine::ObservabilityRetentionConfig,
) -> (NominalCapacityMachine, crate::owned::OwnedSession) {
    let mut machine = make_nominal_capacity_machine(retention);
    let owner = machine
        .load_choreography_owned(&nominal_boundary_image(), "actual-nominal-capacity-owner")
        .unwrap();
    drive_nominal_boundary(&mut machine, handler);
    (machine, owner)
}
fn drive_nominal_boundary(machine: &mut NominalCapacityMachine, handler: &NominalBoundaryHandler) {
    for _ in 0..8 {
        let coros = machine.coroutines();
        let a = coros.iter().find(|coro| coro.role == "A").unwrap();
        let b = coros.iter().find(|coro| coro.role == "B").unwrap();
        if a.pc == 1 && matches!(b.status, crate::coroutine::CoroStatus::Blocked(_)) {
            assert!(handler.nominal_requests().is_empty());
            assert!(a.nominal_continuation_view().is_none());
            return;
        }
        machine
            .step_round(handler, 1)
            .expect("actual declaration and peer wait");
    }
    panic!("real scheduler never reached nominal boundary with peer parked");
}
fn prepare_original_blocked(
    handler: &NominalBoundaryHandler,
    retention: crate::engine::ObservabilityRetentionConfig,
) -> (
    NominalCapacityMachine,
    crate::owned::OwnedSession,
    NominalContinuationView,
) {
    let (mut machine, owner) = prepare_nominal_boundary(handler, retention);
    machine
        .step_round(handler, 1)
        .expect("original callback really blocks");
    let original = nominal_boundary_original(&machine);
    assert_eq!(handler.nominal_requests().len(), 1);
    assert!(original.returned.is_none());
    assert_eq!(original.original_owner, *owner.capability());
    assert_eq!(
        nominal_boundary_coroutine(&machine).pc,
        original.original_pc
    );
    (machine, owner, original)
}
fn assert_nominal_boundary_failure(error: &ProtocolMachineError, expected: &EffectFailure) {
    match error {
        ProtocolMachineError::Fault {
            fault: Fault::Invoke { failure },
            ..
        }
        | ProtocolMachineError::HandlerError(failure) => assert_eq!(failure, expected),
        other => panic!("wrong native boundary cause: {other:?}"),
    }
}
fn assert_nominal_original_requests(
    handler: &NominalBoundaryHandler,
    original: &NominalContinuationView,
    session: crate::session::SessionId,
    expected: usize,
) {
    let calls = handler.nominal_requests();
    assert_eq!(calls.len(), expected);
    for call in calls {
        let EffectRequestBody::NominalCommand { request } = call.body else {
            unreachable!()
        };
        assert_eq!(request.invocation, original.invocation);
        assert_eq!(request.session, session);
        assert_eq!(request.declaration, original.call.declaration);
        assert_eq!(
            call.tick, original.issued_at,
            "retry never refreshes original request time"
        );
    }
}

// Actual returned callback chronology is complete even where the backend's
// diagnostic exchange stream is deliberately disabled or capped.
fn assert_nominal_boundary_observations(
    handler: &NominalBoundaryHandler,
    exchanges: &[crate::effect::EffectExchangeRecord],
    original: &NominalContinuationView,
    retention: crate::engine::ObservabilityRetentionConfig,
    terminal: &EffectOutcome,
) {
    let actual: Vec<_> = handler
        .returned
        .lock()
        .unwrap()
        .iter()
        .filter(|(request, _)| {
            matches!(&request.body,
            EffectRequestBody::NominalCommand { request }
                if request.invocation == original.invocation)
        })
        .cloned()
        .collect();
    assert_eq!(
        actual.len(),
        2,
        "two actual returns on the original callback occurrence"
    );
    assert_eq!(actual[0].1, EffectOutcome::blocked());
    assert_eq!(&actual[1].1, terminal);
    let observed: Vec<_> = exchanges
        .iter()
        .filter(|record| record.effect_id == original.invocation)
        .collect();
    let retained_count = nominal_capacity_expected_original_exchanges(retention);
    assert_eq!(
        observed.len(),
        retained_count,
        "actual backend diagnostic retention contract"
    );
    // These cases have no later successful hint/WAL/ingress record: a capped
    // cooperative stream's one remaining record must be this exact last return.
    for (record, (request, outcome)) in observed
        .iter()
        .zip(actual[actual.len() - retained_count..].iter())
    {
        assert_eq!(
            request.effect_id,
            Some(original.invocation),
            "nominal callback retains the actual pre-issued original occurrence"
        );
        assert_eq!(record.effect_id, original.invocation);
        assert_eq!(&record.request, request);
        assert_eq!(&record.outcome, outcome);
        assert_eq!(record.handler_identity, original.handler_identity);
    }
}

#[test]
fn fresh_nominal_capacity_refuses_before_original_issue_or_callback() {
    for retention in nominal_boundary_retentions() {
        for available in [1, 4] {
            let handler = NominalBoundaryHandler::new(vec![]);
            let (mut machine, _owner) = prepare_nominal_boundary(&handler, retention);
            let before = nominal_boundary_coroutine(&machine);
            // Poll consumes one. Three remaining cannot hold the complete fresh
            // nominal issue + publication bound, even though an issue alone fits.
            machine.next_effect_id = u64::MAX - available;
            let result = machine.step_round(&handler, 1);
            let after = nominal_boundary_coroutine(&machine);
            let next = machine.next_effect_id;
            let outstanding = machine.outstanding_effects.as_slice().to_vec();
            settle_clock_machine(machine);
            let error = result.expect_err("original boundary must refuse");
            assert_original_capacity_refusal(&error);
            assert_eq!(next, u64::MAX - available + 1);
            assert!(handler.nominal_requests().is_empty());
            assert_eq!(handler.hints(), 0);
            assert_eq!(handler.wals(), 0);
            assert!(after.nominal_continuation_view().is_none());
            assert_eq!(
                (after.pc, after.regs, after.cost_budget),
                (before.pc, before.regs, before.cost_budget)
            );
            assert!(!outstanding
                .iter()
                .any(|effect| effect.effect_kind == "nominal_command"));
        }
    }
}

#[test]
fn original_nominal_failure_at_dispatch_max_keeps_first_cause_without_fresh_ids() {
    for retention in nominal_boundary_retentions() {
        for changed_identity in [false, true] {
            let original_failure = EffectFailure::denied("actual original host refusal at MAX");
            let mut handler = NominalBoundaryHandler::new(vec![
                NominalBoundaryReply::Blocked,
                NominalBoundaryReply::Failure(original_failure.clone()),
            ]);
            handler.change_identity_on_failure = changed_identity;
            let (mut machine, owner, original) = prepare_original_blocked(&handler, retention);
            machine.next_effect_id = u64::MAX - 1;
            let result = machine.step_round(&handler, 1);
            let after = nominal_boundary_original(&machine);
            let refused_tick = machine.clock.tick;
            let failed = machine
                .outstanding_effects()
                .iter()
                .find(|effect| effect.effect_id == original.invocation)
                .unwrap()
                .clone();
            let next = machine.next_effect_id;
            let exchanges = machine.effect_exchanges().to_vec();
            settle_clock_machine(machine);
            let error = result.expect_err("original boundary must refuse");
            assert_nominal_boundary_failure(&error, &original_failure);
            assert_eq!(
                failed.status,
                crate::semantic_objects::OutstandingEffectStatus::Failed
            );
            assert_eq!(failed.completed_at_tick, Some(refused_tick));
            assert_eq!(failed.ordering_key, original.issued_at);
            assert_eq!(failed.budget_ticks, Some(original.call.budget_ticks.get()));
            assert_eq!(
                failed.owner_id.as_deref(),
                Some(original.original_owner.owner_id.as_str())
            );
            assert_eq!(after.returned, None);
            assert_eq!(after.issued_at, original.issued_at);
            assert_eq!(after.call, original.call);
            assert_eq!(after.original_owner, original.original_owner);
            if changed_identity {
                assert!(after.validation_failure.is_some());
                assert_ne!(after.validation_failure.as_ref(), Some(&original_failure));
                assert_eq!(
                    failed.outputs.get("failure"),
                    Some(&serde_json::to_value(&original_failure).unwrap())
                );
                assert_eq!(
                    failed.outputs.get("independent_validation"),
                    Some(
                        &serde_json::to_value(after.validation_failure.as_ref().unwrap()).unwrap()
                    )
                );
            } else {
                assert_eq!(after.validation_failure, None);
                assert_eq!(
                    failed.outputs,
                    nominal_capacity_host_failure_outputs(&original_failure)
                );
            }
            assert_eq!(next, u64::MAX);
            assert_eq!(handler.hints(), 0);
            assert_eq!(handler.wals(), 0);
            assert_nominal_original_requests(&handler, &original, owner.session_id(), 2);
            assert_nominal_boundary_observations(
                &handler,
                &exchanges,
                &original,
                retention,
                &EffectOutcome::failure(original_failure),
            );
        }
    }
}

#[test]
fn original_nominal_blocked_at_dispatch_max_stays_pending_without_fresh_ids() {
    for retention in nominal_boundary_retentions() {
        let handler = NominalBoundaryHandler::new(vec![
            NominalBoundaryReply::Blocked,
            NominalBoundaryReply::Blocked,
        ]);
        let (mut machine, owner, original) = prepare_original_blocked(&handler, retention);
        machine.next_effect_id = u64::MAX - 1;
        let result = machine.step_round(&handler, 1);
        let after = nominal_boundary_original(&machine);
        let outstanding = machine
            .outstanding_effects
            .as_slice()
            .iter()
            .find(|effect| effect.effect_id == original.invocation)
            .unwrap()
            .clone();
        let pc = nominal_boundary_coroutine(&machine).pc;
        let next = machine.next_effect_id;
        settle_clock_machine(machine);
        assert!(result.is_ok());
        assert_eq!(
            outstanding.status,
            crate::semantic_objects::OutstandingEffectStatus::Blocked
        );
        assert_eq!(outstanding.completed_at_tick, None);
        assert_eq!(outstanding.ordering_key, original.issued_at);
        assert_eq!(after, original);
        assert_eq!(pc, original.original_pc);
        assert_eq!(next, u64::MAX);
        assert_eq!(handler.hints(), 0);
        assert_eq!(handler.wals(), 0);
        assert_nominal_original_requests(&handler, &original, owner.session_id(), 2);
    }
}

#[test]
fn original_nominal_return_at_dispatch_max_retains_value_and_application_error_before_hint() {
    for retention in nominal_boundary_retentions() {
        for returned in [
            Ok(NominalCommandValue::Bool(true)),
            Err("actual application refusal".to_string()),
        ] {
            let handler = NominalBoundaryHandler::new(vec![
                NominalBoundaryReply::Blocked,
                NominalBoundaryReply::Returned(returned.clone()),
            ]);
            let (mut machine, owner, original) = prepare_original_blocked(&handler, retention);
            machine.next_effect_id = u64::MAX - 1;
            let result = machine.step_round(&handler, 1);
            let after = nominal_boundary_original(&machine);
            let refused_tick = machine.clock.tick;
            let failed_effect = machine
                .outstanding_effects
                .as_slice()
                .iter()
                .find(|effect| effect.effect_id == original.invocation)
                .unwrap()
                .clone();
            let exchanges = machine.effect_exchanges().to_vec();
            let pc = nominal_boundary_coroutine(&machine).pc;
            let second_result = machine.step_round(&handler, 1);
            let preserved = nominal_boundary_original(&machine);
            let next = machine.next_effect_id;
            settle_clock_machine(machine);
            let error = result.expect_err("original boundary must refuse");
            let again = second_result.expect_err("terminal exhaustion must not retry callback");
            assert_original_capacity_refusal(&error);
            assert_original_capacity_refusal(&again);
            let capacity_failure = EffectFailure::contract_violation(
                "canonical effect occurrence identifiers exhausted",
            );
            assert_eq!(after.validation_failure, Some(capacity_failure.clone()));
            assert_eq!(
                failed_effect.status,
                crate::semantic_objects::OutstandingEffectStatus::Failed
            );
            assert_eq!(failed_effect.completed_at_tick, Some(refused_tick));
            assert_eq!(
                failed_effect.outputs.get("failure"),
                Some(&serde_json::to_value(capacity_failure).unwrap())
            );
            assert_eq!(after.returned, Some(returned.clone()));
            assert_nominal_boundary_observations(
                &handler,
                &exchanges,
                &original,
                retention,
                &EffectOutcome::success(EffectResponse::NominalCommand {
                    reply: NominalCommandReply {
                        invocation: original.invocation,
                        result: returned,
                    },
                }),
            );
            assert_eq!(after.invocation, original.invocation);
            assert_eq!(after.issued_at, original.issued_at);
            assert_eq!(after.call, original.call);
            assert_eq!(after.original_owner, original.original_owner);
            assert_eq!(pc, original.original_pc);
            assert_eq!(preserved, after);
            assert_eq!(next, u64::MAX);
            assert_eq!(handler.hints(), 0);
            assert_eq!(handler.wals(), 0);
            assert_nominal_original_requests(&handler, &original, owner.session_id(), 2);
        }
    }
}

#[test]
fn original_nominal_retry_preserves_inclusive_window_without_extra_callback() {
    for retention in nominal_boundary_retentions() {
        for expired in [false, true] {
            let blocks = usize::try_from(NOMINAL_BOUNDARY_BUDGET + u64::from(expired)).unwrap();
            let mut replies = vec![NominalBoundaryReply::Blocked; blocks];
            if !expired {
                replies.push(NominalBoundaryReply::Returned(Ok(
                    NominalCommandValue::Bool(true),
                )));
            }
            let handler = NominalBoundaryHandler::new(replies);
            let (mut machine, owner, original) = prepare_original_blocked(&handler, retention);
            assert_eq!(original.call.budget_ticks.get(), NOMINAL_BOUNDARY_BUDGET);
            let endpoint = original
                .issued_at
                .checked_add(original.call.budget_ticks.get())
                .unwrap();
            // Only actual public rounds advance the SAME SimClock. Every
            // intermediate callback really returns Blocked on the original ID.
            let before_last = endpoint - u64::from(!expired);
            while machine.clock.tick < before_last {
                machine
                    .step_round(&handler, 1)
                    .expect("genuine admitted same-original Blocked retry");
                assert_eq!(nominal_boundary_original(&machine), original);
            }
            let result = machine.step_round(&handler, 1);
            let after = nominal_boundary_coroutine(&machine);
            let tick = machine.clock.tick;
            settle_clock_machine(machine);
            assert_eq!(tick, endpoint + u64::from(expired));
            if expired {
                let error = result.expect_err("expired original occurrence cannot call provider");
                assert_nominal_boundary_failure(
                    &error,
                    &EffectFailure::contract_violation("original nominal progress window expired"),
                );
                assert_eq!(handler.hints(), 0);
                assert_eq!(handler.wals(), 0);
                assert_eq!(after.pc, original.original_pc);
            } else {
                assert!(result.is_ok());
                assert_eq!(handler.hints(), 1);
                assert_eq!(handler.wals(), 1);
                assert_eq!(after.pc, original.call.on_ok);
                assert_eq!(
                    after.regs[usize::from(original.call.result)],
                    Value::Bool(true)
                );
            }
            assert_nominal_original_requests(
                &handler,
                &original,
                owner.session_id(),
                usize::try_from(NOMINAL_BOUNDARY_BUDGET + 1).unwrap(),
            );
        }
    }
}
