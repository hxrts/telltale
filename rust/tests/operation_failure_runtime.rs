//! Actual parent failure/terminal enforcement; no physical settlement is inferred.
use std::collections::BTreeMap;
use std::num::NonZeroU64;
use std::sync::atomic::{AtomicUsize, Ordering};
use telltale_machine::coroutine::{Coroutine, Fault};
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectOutcome, EffectRequest, EffectRequestBody, EffectResponse,
    EffectResult,
};
use telltale_machine::nominal_command::{NominalCommandReply, NominalCommandValue};
use telltale_machine::semantic_objects::{
    OperationPhase, OutstandingEffectStatus, ProtocolMachineSemanticObjects,
};
use telltale_machine::{ProtocolMachine, ProtocolMachineConfig, ProtocolMachineError, Value};

const SOURCE: &str = r#"
effect Host
  command ready : Unit -> Result String Bool
  {
    class : best_effort
    progress : may_block
    region : session
    agreement_use : forbidden
    reentrancy : allow
  }
agreement_profile Selected
  visibility immediate
  rule no_agreement
  usable_at none
  finalized_at none
  evidence witness
operation Flow at A progress Progress within bounded agreement Selected =
  begin Flow
  let result at A = check Host.ready()
  case result of
    | Ok(value) =>
        A -> B : Ready
        await Flow
        resolve Flow as Success
    | Err(reason) =>
        A -> B : Denied
        await Flow
        resolve Flow as Failure
protocol Failure uses Host =
  roles A, B
  A -> B : Start
"#;
const EMPTY_SOURCE: &str = r#"
agreement_profile Selected
  visibility immediate
  rule no_agreement
  usable_at none
  finalized_at none
  evidence witness
operation Flow at A progress Progress within bounded agreement Selected =
  begin Flow
  await Flow
  resolve Flow as Success
protocol Empty =
  roles A, B
  A -> B : Start
"#;
fn image(source: &str) -> telltale_machine::runtime::loader::CodeImage {
    telltale::compile_operation_image(
        source,
        "Flow",
        &BTreeMap::from([("bounded".into(), NonZeroU64::new(64).unwrap())]),
    )
    .expect("actual selected source compiler")
}
struct Provider {
    fail: bool,
    calls: AtomicUsize,
}
impl EffectHandler for Provider {
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        super::NoopHandler.handle_send(role, partner, label, state)
    }
    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        super::NoopHandler.handle_recv(role, partner, label, state, payload)
    }
    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String> {
        super::NoopHandler.handle_choose(role, partner, labels, state)
    }

    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        if let EffectRequestBody::NominalCommand { request: actual } = &request.body {
            self.calls.fetch_add(1, Ordering::SeqCst);
            if self.fail {
                return EffectOutcome::failure(EffectFailure::contract_violation(
                    "original child failure",
                ));
            }
            EffectOutcome::success(EffectResponse::NominalCommand {
                reply: NominalCommandReply {
                    invocation: actual.invocation,
                    result: Ok(NominalCommandValue::Bool(true)),
                },
            })
        } else {
            super::NoopHandler.handle_effect(request)
        }
    }
    fn step(
        &self,
        _: &str,
        _: &mut Vec<telltale_machine::coroutine::Value>,
    ) -> telltale_machine::model::effects::EffectResult<()> {
        panic!("original child cannot fall back to generic invoke")
    }
}
fn assert_original_failure(
    error: &ProtocolMachineError,
    objects: &ProtocolMachineSemanticObjects,
    coroutines: &[Coroutine],
    deny: bool,
) {
    let ProtocolMachineError::Fault { fault, .. } = error else {
        panic!("actual original fault: {error}")
    };
    if deny {
        assert!(matches!(fault, Fault::OutputCondition { .. }));
    } else {
        assert!(
            matches!(fault, Fault::Invoke { failure } if *failure == EffectFailure::contract_violation("original child failure"))
        );
    }
    let coroutine = coroutines.iter().find(|coro| coro.role == "A").unwrap();
    let original = coroutine.operation_continuation_view().unwrap();
    assert_eq!(original.execution_failure.as_ref(), Some(fault));
    assert!(original.invalidated && !original.resolved && original.outcome.is_none());
    assert_eq!(original.declaration.name, "Flow");
    assert_eq!(original.declaration.budget_ticks.get(), 64);
    let parent = objects
        .operation_instances
        .iter()
        .find(|record| record.operation_id == original.operation_id)
        .unwrap();
    assert_eq!(parent.phase, OperationPhase::Failed);
    assert_eq!(parent.effect_ids, original.children);
    assert!(parent.terminal_publication.is_none());
    let progress = objects
        .progress_contracts
        .iter()
        .find(|record| record.operation_id == original.operation_id)
        .unwrap();
    assert_eq!(progress.last_ordering_key, Some(original.issued_at));
    assert_eq!(progress.budget_ticks, Some(64));
    assert_eq!(parent.owner_id.as_deref(), Some("original/owner"));
    assert_eq!(original.children.len(), 1);
    assert_eq!(
        original.completed_children.len(),
        1,
        "actual callback outcome survives refusal"
    );
    let child = objects
        .outstanding_effects
        .iter()
        .find(|effect| original.children.contains(&effect.effect_id))
        .unwrap();
    assert!(!matches!(
        child.status,
        OutstandingEffectStatus::Pending
            | OutstandingEffectStatus::Blocked
            | OutstandingEffectStatus::Succeeded
    ));
    if deny {
        assert_eq!(child.status, OutstandingEffectStatus::Invalidated);
    }
    assert!(objects.canonical_handles.is_empty());
}
fn skipped_terminal_image() -> telltale_machine::runtime::loader::CodeImage {
    use telltale_machine::instr::Instr;
    let mut image = image(EMPTY_SOURCE);
    let program = image.programs.get_mut("A").unwrap();
    let halt = program
        .iter()
        .position(|instruction| matches!(instruction, Instr::Halt))
        .unwrap();
    // Real instruction control flow, not a direct PC mutation: static Resolve
    // remains installed, but the actual Await slot jumps over it to Halt.
    program[1] = Instr::Jump { target: halt };
    image
}
fn assert_halt_refused(
    error: &ProtocolMachineError,
    objects: &ProtocolMachineSemanticObjects,
    coroutines: &[Coroutine],
    exchanges: &[telltale_machine::model::effects::EffectExchangeRecord],
) {
    let ProtocolMachineError::Fault { fault, .. } = error else {
        panic!("actual Halt fault required: {error}");
    };
    assert!(
        matches!(fault, Fault::Invoke { failure } if *failure == EffectFailure::contract_violation(
        "source operation reached halt without original resolution or invalidation"))
    );
    let original = coroutines
        .iter()
        .find(|coro| coro.role == "A")
        .unwrap()
        .operation_continuation_view()
        .unwrap();
    assert!(original.invalidated && !original.resolved);
    assert_eq!(original.execution_failure.as_ref(), Some(fault));
    assert!(original.children.is_empty() && original.completed_children.is_empty());
    assert!(original.declaration.required_children.is_empty());
    let parent = objects
        .operation_instances
        .iter()
        .find(|record| record.operation_id == original.operation_id)
        .unwrap();
    assert_eq!(parent.phase, OperationPhase::Failed);
    assert_eq!(parent.budget_ticks, Some(64));
    assert!(parent.effect_ids.is_empty() && parent.dependent_operation_ids.is_empty());
    assert_eq!(
        parent.owner_id.as_deref(),
        Some(original.owner.owner_id.as_str())
    );
    let source: Vec<_> = objects
        .operation_instances
        .iter()
        .filter(|record| record.operation_id.starts_with("operation:"))
        .collect();
    assert_eq!(source.len(), 1);
    assert_eq!(source[0].operation_id, original.operation_id);
    let progress: Vec<_> = objects
        .progress_contracts
        .iter()
        .filter(|record| record.operation_id == original.operation_id)
        .collect();
    assert_eq!(progress.len(), 1);
    assert_eq!(progress[0].last_ordering_key, Some(original.issued_at));
    assert_eq!(progress[0].budget_ticks, Some(64));
    super::operation_lifecycle_runtime::assert_empty_ingress_operations(objects, exchanges);
}
macro_rules! failure_backend {
    ($module:ident, $make:expr, $dispose:expr) => {
        mod $module {
            use super::*;
            #[test]
            fn actual_parent_retains_first_child_or_output_fault_without_settlement_ack() {
                for deny in [false, true] {
                    let source_image = image(SOURCE);
                    let config = ProtocolMachineConfig {
                        output_condition_policy: if deny {
                            telltale_machine::output_condition::OutputConditionPolicy::DenyAll
                        } else {
                            telltale_machine::output_condition::OutputConditionPolicy::AllowAll
                        },
                        ..Default::default()
                    };
                    let mut machine = ($make)(config);
                    let admitted = machine.load_choreography_owned(&source_image, "original/owner");
                    let provider = Provider {
                        fail: !deny,
                        calls: AtomicUsize::new(0),
                    };
                    let result = admitted.as_ref().ok().map(|_| machine.run(&provider, 64));
                    let first = machine.coroutines().to_vec();
                    let before = first
                        .iter()
                        .find(|coro| coro.role == "A")
                        .and_then(|coro| coro.operation_continuation_view());
                    if admitted.is_ok() {
                        let _later_observation = machine.step_round(&provider, 1);
                    }
                    let objects = machine.semantic_objects();
                    let after = machine.coroutines().to_vec();
                    let calls = provider.calls.load(Ordering::SeqCst);
                    ($dispose)(machine);
                    admitted.expect("actual owning admission before original execution");
                    let error = result.unwrap().expect_err("actual producer refused");
                    assert_eq!(calls, 1);
                    assert_original_failure(&error, &objects, &after, deny);
                    assert_eq!(
                        before.unwrap(),
                        after
                            .iter()
                            .find(|coro| coro.role == "A")
                            .unwrap()
                            .operation_continuation_view()
                            .unwrap()
                    );
                }
            }
            #[test]
            fn actual_jump_cannot_halt_with_unresolved_original_parent() {
                let mut machine = ($make)(ProtocolMachineConfig::default());
                let admitted =
                    machine.load_choreography_owned(&skipped_terminal_image(), "original/owner");
                let result = admitted
                    .as_ref()
                    .ok()
                    .map(|_| machine.run(&super::super::NoopHandler, 64));
                let objects = machine.semantic_objects();
                let coroutines = machine.coroutines().to_vec();
                let exchanges = machine.effect_exchanges().to_vec();
                ($dispose)(machine);
                admitted
                    .expect("static terminal exists; actual runtime gate must enforce execution");
                assert_halt_refused(
                    &result.unwrap().expect_err("unresolved parent cannot halt"),
                    &objects,
                    &coroutines,
                    &exchanges,
                );
            }
        }
    };
}
failure_backend!(cooperative, ProtocolMachine::new, |_: ProtocolMachine| {});
#[cfg(all(feature = "multi-thread", not(target_arch = "wasm32")))]
failure_backend!(
    threaded,
    |config| telltale_machine::ThreadedProtocolMachine::with_workers(config, 1),
    |machine: telltale_machine::ThreadedProtocolMachine| {
        machine
            .shutdown_worker_pool()
            .expect("actual original native worker join");
    }
);
#[test]
fn original_begin_without_static_terminal_is_refused_before_owning_admission() {
    use telltale_machine::instr::{Instr, InvokeAction};
    use telltale_machine::operation_lifecycle::OperationAction;
    let mut image = image(EMPTY_SOURCE);
    for instruction in image.programs.get_mut("A").unwrap() {
        if matches!(instruction, Instr::Invoke { action: InvokeAction::OperationLifecycle(action) }
            if matches!(action.as_ref(), OperationAction::Resolve { .. }))
        {
            *instruction = Instr::Halt;
        }
    }
    let mut machine = ProtocolMachine::new(Default::default());
    assert!(machine
        .load_choreography_owned(&image, "original/owner")
        .is_err());
    assert!(machine.operation_instances().is_empty());
    assert!(machine.effect_trace().is_empty());
}
