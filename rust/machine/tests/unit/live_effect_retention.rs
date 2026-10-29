// Actual producer fixtures shared by the two existing backend owner modules.
use crate::effect::{EffectRequestBody, EffectResponse};
use crate::engine::{LiveEffectRecord, ObservabilityRetentionConfig, ObservabilityRetentionMode};
use crate::instr::Instr;
use std::collections::BTreeMap;
use std::sync::atomic::{AtomicUsize, Ordering as AtomicOrdering};
use telltale_types::{GlobalType, LocalTypeR};

struct BlockedAcquire {
    actual_acquires: AtomicUsize,
    actual_topology: AtomicUsize,
}
impl BlockedAcquire {
    fn new() -> Self {
        Self {
            actual_acquires: AtomicUsize::new(0),
            actual_topology: AtomicUsize::new(0),
        }
    }
}
impl EffectHandler for BlockedAcquire {
    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        match request.body {
            EffectRequestBody::Acquire { .. } => {
                self.actual_acquires.fetch_add(1, AtomicOrdering::SeqCst);
                EffectOutcome::blocked()
            }
            EffectRequestBody::TopologyEvents { .. } => {
                self.actual_topology.fetch_add(1, AtomicOrdering::SeqCst);
                EffectOutcome::success(EffectResponse::TopologyEvents { events: vec![] })
            }
            EffectRequestBody::OutputConditionHint { .. } => {
                EffectOutcome::success(EffectResponse::OutputConditionHint { hint: None })
            }
            _ => panic!("unexpected request from actual Acquire/Yield fixture"),
        }
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
        unreachable!()
    }
}
fn image(acquire: bool) -> CodeImage {
    CodeImage {
        programs: BTreeMap::from([(
            "A".into(),
            if acquire {
                vec![
                    Instr::Acquire {
                        layer: "Guard".into(),
                        dst: 1,
                    },
                    Instr::Halt,
                ]
            } else {
                vec![Instr::Yield, Instr::Jump { target: 0 }]
            },
        )]),
        global_type: GlobalType::End,
        local_types: BTreeMap::from([("A".into(), LocalTypeR::End)]),
    }
}
fn retention_modes() -> [ObservabilityRetentionConfig; 2] {
    [
        ObservabilityRetentionConfig {
            mode: ObservabilityRetentionMode::Capped,
            capacity: 1,
        },
        ObservabilityRetentionConfig {
            mode: ObservabilityRetentionMode::Disabled,
            capacity: 1,
        },
    ]
}

#[test]
fn actual_blocked_acquire_survives_topology_and_preserves_enforcement() {
    for retention in retention_modes() {
        let mut machine = make_machine(retention);
        let original = machine
            .load_choreography_owned(&image(true), "actual-original")
            .unwrap();
        let unrelated = machine
            .load_choreography_owned(&image(false), "actual-unrelated")
            .unwrap();
        let handler = BlockedAcquire::new();
        // Existing backends differ in Blocked Acquire instruction policy: the
        // cooperative task blocks; threaded faults. Both must retain the actual
        // still-Blocked semantic obligation until explicit settlement/invalidation.
        let _first = machine.step_round(&handler, 1);
        assert_eq!(handler.actual_acquires.load(AtomicOrdering::SeqCst), 1);
        let active: Vec<_> = machine
            .outstanding_effects()
            .iter()
            .filter(|effect| effect.session == Some(original.session_id()) && effect.is_live())
            .cloned()
            .collect();
        assert!(!active.is_empty());
        for effect in &active {
            assert_eq!(effect.owner_id.as_deref(), Some("actual-original"));
            assert_eq!(effect.budget_ticks, Some(1));
            assert_eq!(effect.status, OutstandingEffectStatus::Blocked);
        }
        let topology_before = handler.actual_topology.load(AtomicOrdering::SeqCst);
        machine.step_round(&handler, 1).unwrap();
        assert!(handler.actual_topology.load(AtomicOrdering::SeqCst) > topology_before);
        for original_effect in &active {
            let retained = machine
                .outstanding_effects()
                .iter()
                .find(|effect| effect.effect_id == original_effect.effect_id)
                .unwrap();
            assert_eq!(retained.owner_id, original_effect.owner_id);
            assert_eq!(retained.status, OutstandingEffectStatus::Blocked);
            assert!(machine
                .operation_instances()
                .iter()
                .any(|operation| operation.operation_id == retained.operation_id
                    && operation.phase == OperationPhase::Blocked));
            assert!(machine
                .progress_contracts()
                .iter()
                .any(|contract| contract.operation_id == retained.operation_id
                    && contract.state == ProgressState::NoProgress));
        }
        let duplicate = EffectRequest::acquire(0, original.session_id(), None, "A", "Guard", &[]);
        assert!(machine.ensure_effect_request_allowed(&duplicate).is_err());
        machine
            .close_and_reap_session(original.session_id())
            .unwrap();
        assert!(machine.ensure_effect_request_allowed(&duplicate).is_ok());
        machine
            .close_and_reap_session(unrelated.session_id())
            .unwrap();
    }
}

#[test]
fn actual_session_settlement_prunes_only_terminal_history() {
    for retention in retention_modes() {
        let mut machine = make_machine(retention);
        let original = machine
            .load_choreography_owned(&image(true), "actual-original")
            .unwrap();
        let unrelated = machine
            .load_choreography_owned(&image(false), "actual-unrelated")
            .unwrap();
        let handler = BlockedAcquire::new();
        let _first = machine.step_round(&handler, 1);
        machine.step_round(&handler, 1).unwrap();
        assert!(machine
            .outstanding_effects()
            .iter()
            .any(LiveEffectRecord::is_live));
        machine
            .close_and_reap_session(original.session_id())
            .unwrap();
        let history_limit = if retention.mode == ObservabilityRetentionMode::Disabled {
            0
        } else {
            1
        };
        assert!(machine
            .outstanding_effects()
            .iter()
            .all(|record| !record.is_live()));
        assert!(machine
            .operation_instances()
            .iter()
            .all(|record| !record.is_live()));
        assert!(machine
            .progress_contracts()
            .iter()
            .all(|record| !record.is_live()));
        assert!(machine.outstanding_effects().len() <= history_limit);
        assert!(machine.operation_instances().len() <= history_limit);
        assert!(machine.progress_contracts().len() <= history_limit);
        // Unrelated actual runtime remains usable after original settlement.
        machine.step_round(&handler, 1).unwrap();
        machine
            .close_and_reap_session(unrelated.session_id())
            .unwrap();
    }
}

struct ActualWalReplies(std::sync::Mutex<Vec<crate::durable::WalSyncRequest>>);
impl EffectHandler for ActualWalReplies {
    fn supports_wal_sync(&self) -> bool {
        true
    }
    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        match request.body {
            EffectRequestBody::InvokeStep { state, .. } => {
                EffectOutcome::success(EffectResponse::InvokeStep { state })
            }
            EffectRequestBody::TopologyEvents { .. } => {
                EffectOutcome::success(EffectResponse::TopologyEvents { events: vec![] })
            }
            EffectRequestBody::OutputConditionHint { .. } => {
                EffectOutcome::success(EffectResponse::OutputConditionHint { hint: None })
            }
            EffectRequestBody::WalSync { sync } => {
                self.0.lock().unwrap().push(sync);
                EffectOutcome::success(EffectResponse::WalSync)
            }
            _ => panic!("unexpected request from actual Invoke/WalSync fixture"),
        }
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
        unreachable!()
    }
}

#[test]
fn actual_wal_sync_keeps_original_resident_terminal_evidence_across_retention_modes() {
    let modes = [
        ObservabilityRetentionConfig::default(),
        retention_modes()[0],
        retention_modes()[1],
    ];
    let mut original_sync = None;
    for retention in modes {
        let mut machine = make_machine(retention);
        machine.config.output_condition_policy =
            crate::output_condition::OutputConditionPolicy::AllowAll;
        let code = CodeImage {
            programs: BTreeMap::from([(
                "A".into(),
                vec![
                    Instr::Invoke {
                        action: crate::instr::InvokeAction::Named("runtime.step".into()),
                    },
                    Instr::Yield,
                    Instr::Halt,
                ],
            )]),
            global_type: GlobalType::End,
            local_types: BTreeMap::from([("A".into(), LocalTypeR::End)]),
        };
        let owner = machine
            .load_choreography_owned(&code, "actual-original")
            .unwrap();
        let handler = ActualWalReplies(std::sync::Mutex::new(Vec::new()));
        machine.step_round(&handler, 1).unwrap();
        let syncs = handler.0.lock().unwrap();
        assert_eq!(
            syncs.len(),
            1,
            "actual supported commit gate invoked WalSync"
        );
        let sync = syncs[0].clone();
        assert!(
            sync.agreement_state.is_some(),
            "must retain actual resident operation, not default Finalized fallback"
        );
        assert!(!sync.agreement_evidence.is_empty());
        assert!(!sync.operation_id.starts_with("wal_sync:coro:"));
        if let Some(original) = &original_sync {
            assert_eq!(&sync, original);
        } else {
            original_sync = Some(sync);
        }
        drop(syncs);
        // A terminal effect is still canonical input while its session remains
        // resident; history limits apply only after actual session retirement.
        assert!(
            machine
                .operation_instances()
                .iter()
                .any(|operation| operation.session == Some(owner.session_id())
                    && !operation.is_live())
        );
        machine.close_and_reap_session(owner.session_id()).unwrap();
        if retention.mode != ObservabilityRetentionMode::Full {
            let limit = if retention.mode == ObservabilityRetentionMode::Disabled {
                0
            } else {
                1
            };
            assert!(machine.operation_instances().len() <= limit);
            assert!(machine.outstanding_effects().len() <= limit);
            assert!(machine.progress_contracts().len() <= limit);
        }
    }
}
