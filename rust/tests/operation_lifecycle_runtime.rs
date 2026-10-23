//! Actual explicit operation boundaries; no child callback or canonical proof is invented.

use std::collections::BTreeMap;
use std::num::NonZeroU64;

use telltale::compile_operation_lifecycle;
use telltale_machine::model::effects::{EffectHandler, EffectResult};
use telltale_machine::semantic_objects::OperationPhase;
use telltale_machine::Value;
use telltale_machine::{ProtocolMachine, ProtocolMachineConfig};

const SOURCE: &str = r#"
agreement_profile Selected
  visibility immediate
  rule no_agreement
  usable_at none
  finalized_at none
  evidence witness
operation Flow at A progress FlowProgress within bounded agreement Selected =
  begin Flow
  await Flow
  resolve Flow as Success
protocol Boundary =
  roles A, B
  A -> B : Start
"#;

fn image(source: &str) -> telltale_machine::runtime::loader::CodeImage {
    compile_operation_lifecycle(
        source,
        "Flow",
        &BTreeMap::from([(
            "bounded".into(),
            NonZeroU64::new(64).expect("selected logical window"),
        )]),
    )
    .expect("actual original source operation boundaries")
}

#[test]
fn source_begin_await_resolve_retains_original_instance_without_minting_proof() {
    let image = image(SOURCE);
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let original = machine
        .load_choreography_owned(&image, "original")
        .expect("actual issued owner");
    machine
        .run(&super::NoopHandler, 64)
        .expect("actual lifecycle execution");
    let objects = machine.semantic_objects();
    let original_continuation = machine
        .coroutines()
        .iter()
        .find(|coro| coro.role == "A")
        .and_then(|coro| coro.operation_continuation_view())
        .expect("actual original source continuation");
    assert_empty_operation_ledger(&objects, &original_continuation, machine.effect_exchanges());
    let record = objects
        .operation_instances
        .iter()
        .find(|record| record.operation_id == original_continuation.operation_id)
        .expect("same uniquely validated original");
    assert_eq!(
        record.owner_id.as_deref(),
        Some(original.capability().owner_id.as_str())
    );
    assert!(objects.materialization_proofs.is_empty());
    assert!(objects.canonical_handles.is_empty());
    assert!(objects
        .publication_events
        .iter()
        .all(|event| event.proof_ref.is_none()));
}

fn assert_empty_operation_ledger(
    objects: &telltale_machine::semantic_objects::ProtocolMachineSemanticObjects,
    original: &telltale_machine::operation_lifecycle::OperationContinuationView,
    exchanges: &[telltale_machine::model::effects::EffectExchangeRecord],
) {
    use telltale_machine::operation_lifecycle::OperationOutcome;
    let records = &objects.operation_instances;
    let ids: std::collections::BTreeSet<_> =
        records.iter().map(|record| &record.operation_id).collect();
    assert_eq!(
        ids.len(),
        records.len(),
        "canonical occurrences, not duplicate snapshots"
    );
    let source: Vec<_> = records
        .iter()
        .filter(|record| record.operation_id.starts_with("operation:"))
        .collect();
    assert_eq!(source.len(), 1, "exactly one actual source Begin");
    let record = source[0];
    assert_eq!(record.operation_id, original.operation_id);
    assert_eq!(record.session, Some(original.owner.session_id));
    assert_eq!(
        record.owner_id.as_deref(),
        Some(original.owner.owner_id.as_str())
    );
    assert_eq!(record.kind, original.declaration.name);
    assert_eq!(
        record.budget_ticks,
        Some(original.declaration.budget_ticks.get())
    );
    assert_eq!(
        record.agreement_profile.as_ref(),
        Some(&original.declaration.agreement_profile)
    );
    assert_eq!(record.phase, OperationPhase::Succeeded);
    assert!(record.requires_proof && original.resolved && !original.invalidated);
    assert_eq!(original.outcome, Some(OperationOutcome::Success(None)));
    assert!(record.effect_ids.is_empty() && record.dependent_operation_ids.is_empty());
    assert!(original.children.is_empty() && original.completed_children.is_empty());
    assert!(original.declaration.required_children.is_empty());
    let contracts: Vec<_> = objects
        .progress_contracts
        .iter()
        .filter(|progress| progress.operation_id == original.operation_id)
        .collect();
    assert_eq!(contracts.len(), 1);
    assert_eq!(contracts[0].last_ordering_key, Some(original.issued_at));
    assert_eq!(
        contracts[0].budget_ticks,
        Some(original.declaration.budget_ticks.get())
    );
    assert_empty_ingress_operations(objects, exchanges);
    assert_eq!(
        records.len(),
        exchanges.len() + 1,
        "exhaustive source plus real ingress classes"
    );
}

pub(super) fn assert_empty_ingress_operations(
    objects: &telltale_machine::semantic_objects::ProtocolMachineSemanticObjects,
    exchanges: &[telltale_machine::model::effects::EffectExchangeRecord],
) {
    use telltale_machine::model::effects::EffectRequestBody;
    use telltale_machine::semantic_objects::OutstandingEffectStatus;
    assert!(
        !exchanges.is_empty(),
        "actual scheduler ingress was observed"
    );
    assert_eq!(objects.outstanding_effects.len(), exchanges.len());
    assert_eq!(objects.operation_instances.len(), exchanges.len() + 1);
    let operation_ids: std::collections::BTreeSet<_> = objects
        .operation_instances
        .iter()
        .map(|record| &record.operation_id)
        .collect();
    assert_eq!(operation_ids.len(), objects.operation_instances.len());
    assert_eq!(objects.progress_contracts.len(), exchanges.len() + 1);
    let progress_ids: std::collections::BTreeSet<_> = objects
        .progress_contracts
        .iter()
        .map(|record| &record.operation_id)
        .collect();
    assert_eq!(progress_ids.len(), objects.progress_contracts.len());
    let ids: std::collections::BTreeSet<_> = exchanges
        .iter()
        .map(|exchange| exchange.effect_id)
        .collect();
    assert_eq!(ids.len(), exchanges.len());
    for exchange in exchanges {
        assert!(matches!(
            exchange.request.body,
            EffectRequestBody::TopologyEvents { .. }
        ));
        assert_eq!(exchange.request.effect_id, Some(exchange.effect_id));
        assert_eq!(exchange.request.session, None);
        assert_eq!(
            exchange.outcome.clone().into_topology().unwrap(),
            EffectResult::success(Vec::new())
        );
        let effects: Vec<_> = objects
            .outstanding_effects
            .iter()
            .filter(|effect| effect.effect_id == exchange.effect_id)
            .collect();
        assert_eq!(effects.len(), 1);
        let effect = effects[0];
        assert_eq!(effect.effect_kind, "topology_events");
        assert_eq!(effect.status, OutstandingEffectStatus::Succeeded);
        let records: Vec<_> = objects
            .operation_instances
            .iter()
            .filter(|record| record.operation_id == effect.operation_id)
            .collect();
        assert_eq!(records.len(), 1);
        let record = records[0];
        assert_eq!(record.effect_ids, vec![exchange.effect_id]);
        assert_eq!(exchange.request.metadata.operation_name, "topologyEvents");
        assert_eq!(record.kind, exchange.request.metadata.operation_name);
        assert_eq!(record.phase, OperationPhase::Succeeded);
        assert_eq!(record.session, exchange.request.session);
        assert!(record.owner_id.is_none() && !record.requires_proof);
        let progress: Vec<_> = objects
            .progress_contracts
            .iter()
            .filter(|progress| progress.operation_id == effect.operation_id)
            .collect();
        assert_eq!(progress.len(), 1);
        assert_eq!(progress[0].session, exchange.request.session);
        assert_eq!(progress[0].last_ordering_key, Some(exchange.ordering_key));
    }
}

#[test]
fn operation_source_rejects_duplicate_absent_and_erased_continuations() {
    for source in [
        SOURCE.replace("await Flow", "begin Flow"),
        SOURCE.replace("  begin Flow\n", ""),
        SOURCE.replace("  resolve Flow as Success\n", ""),
        SOURCE.replace("await Flow", "await Foreign"),
        SOURCE.replace("await Flow", "A -> B : Unlowered"),
    ] {
        assert!(
            compile_operation_lifecycle(
                &source,
                "Flow",
                &BTreeMap::from([(
                    "bounded".into(),
                    NonZeroU64::new(64).expect("selected original window")
                ),])
            )
            .is_err(),
            "unsupported original body must not disappear"
        );
    }
}

#[cfg(feature = "multi-thread")]
#[test]
fn threaded_source_operation_boundaries_use_same_canonical_transaction() {
    use telltale_machine::{ThreadedProtocolMachine, ThreadedRoundSemantics};
    let image = image(SOURCE);
    let config = ProtocolMachineConfig {
        threaded_round_semantics: ThreadedRoundSemantics::CanonicalOneStep,
        ..ProtocolMachineConfig::default()
    };
    let mut machine = ThreadedProtocolMachine::with_workers(config, 2);
    let admitted = machine.load_choreography_owned(&image, "original");
    let result = if admitted.is_ok() {
        Some(machine.run(&super::NoopHandler, 64))
    } else {
        None
    };
    let objects = machine.semantic_objects();
    let original_continuation = machine
        .coroutines()
        .iter()
        .find(|coro| coro.role == "A")
        .and_then(|coro| coro.operation_continuation_view());
    let exchanges = machine.effect_exchanges().to_vec();
    let joined = machine.shutdown_worker_pool();
    assert!(
        joined.is_ok(),
        "actual original worker acknowledgment before assertions"
    );
    assert!(admitted.is_ok());
    assert!(result.expect("actual admitted execution").is_ok());
    assert_empty_operation_ledger(
        &objects,
        &original_continuation.expect("actual original source continuation"),
        &exchanges,
    );
    assert!(objects.materialization_proofs.is_empty());
    assert!(objects.canonical_handles.is_empty());
}

const CHILD_SOURCE: &str = r#"
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
operation Flow at A progress FlowProgress within bounded agreement Selected =
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
protocol Boundary uses Host =
  roles A, B
  A -> B : Start
"#;

struct ChildProvider {
    calls: std::sync::Mutex<Vec<u64>>,
    block_first: bool,
}
impl EffectHandler for ChildProvider {
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

    fn step(
        &self,
        _: &str,
        _: &mut Vec<telltale_machine::coroutine::Value>,
    ) -> telltale_machine::model::effects::EffectResult<()> {
        panic!("source child must use its actual typed nominal boundary")
    }
    fn handle_effect(
        &self,
        request: telltale_machine::model::effects::EffectRequest,
    ) -> telltale_machine::model::effects::EffectOutcome {
        use telltale_machine::model::effects::{EffectOutcome, EffectRequestBody, EffectResponse};
        if let EffectRequestBody::NominalCommand { request: actual } = &request.body {
            let mut calls = self.calls.lock().expect("actual provider calls");
            calls.push(actual.invocation);
            if self.block_first && calls.len() == 1 {
                return EffectOutcome::blocked();
            }
            EffectOutcome::success(EffectResponse::NominalCommand {
                reply: telltale_machine::nominal_command::NominalCommandReply {
                    invocation: actual.invocation,
                    result: Ok(telltale_machine::nominal_command::NominalCommandValue::Bool(true)),
                },
            })
        } else {
            super::NoopHandler.handle_effect(request)
        }
    }
}

#[test]
fn enclosing_source_operation_survives_child_success_until_explicit_resolution() {
    let image = image(CHILD_SOURCE);
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine
        .load_choreography_owned(&image, "original")
        .expect("actual issued owner");
    let provider = ChildProvider {
        calls: std::sync::Mutex::new(Vec::new()),
        block_first: true,
    };
    for _ in 0..16 {
        machine.step(&provider).expect("actual scheduler step");
        if !provider.calls.lock().expect("calls").is_empty() {
            break;
        }
    }
    let original = machine
        .operation_instances()
        .iter()
        .find(|record| record.operation_id.starts_with("operation:"))
        .expect("actual enclosing Begin instance")
        .clone();
    assert_eq!(
        original.effect_ids.len(),
        1,
        "actual original admitted child"
    );
    assert!(matches!(
        original.phase,
        OperationPhase::Pending | OperationPhase::Blocked
    ));
    let ordering = machine
        .progress_contracts()
        .iter()
        .find(|progress| progress.operation_id == original.operation_id)
        .expect("actual original progress owner")
        .last_ordering_key;
    assert_eq!(
        provider.calls.lock().expect("actual first callback").len(),
        1
    );
    machine
        .run(&provider, 64)
        .expect("same original child retry and explicit resolve");
    let terminal = machine
        .operation_instances()
        .iter()
        .find(|record| record.operation_id == original.operation_id)
        .expect("same actual enclosing operation");
    assert_eq!(terminal.phase, OperationPhase::Succeeded);
    assert_eq!(terminal.effect_ids, original.effect_ids);
    assert!(terminal.requires_proof);
    let calls = provider.calls.lock().expect("actual callbacks");
    assert_eq!(calls.len(), 2);
    assert!(calls.iter().all(|id| *id == original.effect_ids[0]));
    assert_eq!(
        machine
            .progress_contracts()
            .iter()
            .find(|progress| progress.operation_id == original.operation_id)
            .expect("same original window")
            .last_ordering_key,
        ordering
    );
}

#[test]
fn skipped_required_source_child_cannot_become_empty_inventory_success() {
    use telltale_machine::instr::{Instr, InvokeAction};
    use telltale_machine::operation_lifecycle::OperationAction;
    let mut image = image(CHILD_SOURCE);
    let program = image
        .programs
        .get_mut("A")
        .expect("actual original owner program");
    let mut expected = None;
    if let Instr::Invoke {
        action: InvokeAction::NominalCommand(call),
    } = &mut program[2]
    {
        call.on_ok += 1;
        call.on_err += 1;
        expected = Some(call.as_ref().clone());
    }
    let expected = expected.expect("actual installed child call");
    program.insert(
        2,
        Instr::Jump {
            target: expected.on_ok + 1,
        },
    );
    if let Instr::Invoke {
        action: InvokeAction::OperationLifecycle(action),
    } = &mut program[1]
    {
        if let OperationAction::Begin { declaration } = action.as_mut() {
            declaration.required_children[0].pc = 3;
            declaration.required_children[0].call = expected;
        }
    }
    image
        .validate_runtime_shape()
        .expect("exact installed manifest is intact; only control flow skips it");
    let provider = ChildProvider {
        calls: std::sync::Mutex::new(Vec::new()),
        block_first: false,
    };
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine
        .load_choreography_owned(&image, "original")
        .expect("actual issued owner");
    assert!(machine.run(&provider, 64).is_err());
    assert!(provider
        .calls
        .lock()
        .expect("actual provider observation")
        .is_empty());
    let original = machine
        .coroutines()
        .iter()
        .find(|coro| coro.role == "A")
        .and_then(|coro| coro.operation_continuation_view())
        .expect("actual original continuation");
    assert!(original.invalidated);
    assert!(!original.resolved);
    assert!(original.children.is_empty());
    assert!(original.execution_failure.is_some());
}

#[test]
fn loader_refuses_duplicate_foreign_and_relocated_required_child_manifests() {
    use telltale_machine::instr::{Instr, InvokeAction};
    use telltale_machine::operation_lifecycle::OperationAction;
    for mutation in 0..4 {
        let mut image = image(CHILD_SOURCE);
        let program = image.programs.get_mut("A").expect("actual owner program");
        let Instr::Invoke {
            action: InvokeAction::OperationLifecycle(action),
        } = &mut program[1]
        else {
            panic!("actual Begin opcode absent");
        };
        let OperationAction::Begin { declaration } = action.as_mut() else {
            panic!("actual Begin absent");
        };
        let original = declaration.required_children[0].clone();
        match mutation {
            0 => declaration.required_children.push(original),
            1 => declaration.required_children[0].call.declaration.operation = "foreign".into(),
            2 => declaration.required_children[0].call.on_ok = original.call.on_err,
            _ => declaration.required_children[0].pc += 1,
        }
        assert!(
            image.validate_runtime_shape().is_err(),
            "altered exact source slot must refuse before ownership/callback admission"
        );
    }
}

#[test]
fn changed_generation_refuses_original_source_child_before_provider() {
    let image = image(CHILD_SOURCE);
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let original = machine
        .load_choreography_owned(&image, "original")
        .expect("actual original owner");
    let provider = ChildProvider {
        calls: std::sync::Mutex::new(Vec::new()),
        block_first: false,
    };
    for _ in 0..16 {
        machine
            .step(&provider)
            .expect("actual scheduler step to Begin");
        if machine
            .operation_instances()
            .iter()
            .any(|record| record.operation_id.starts_with("operation:"))
        {
            break;
        }
    }
    assert!(provider
        .calls
        .lock()
        .expect("actual original callback observation")
        .is_empty());
    let begun = machine
        .coroutines()
        .iter()
        .find(|coro| coro.role == "A")
        .and_then(|coro| coro.operation_continuation_view())
        .expect("actual Begin precondition");
    assert!(!begun.resolved && begun.children.is_empty());
    assert_eq!(begun.declaration.required_children.len(), 1);
    let current = original
        .attenuate_scope(&mut machine, telltale_machine::OwnershipScope::Session)
        .expect("canonical generation transition");
    assert_ne!(
        current.capability().generation,
        original.capability().generation
    );
    let failed = machine
        .run(&provider, 64)
        .expect_err("stale original continuation must refuse");
    assert!(matches!(
        failed,
        telltale_machine::ProtocolMachineError::Fault {
            fault: telltale_machine::coroutine::Fault::OperationOwnership { .. },
            ..
        }
    ));
    assert!(provider
        .calls
        .lock()
        .expect("actual no-callback observation")
        .is_empty());
}

#[cfg(feature = "multi-thread")]
#[test]
fn threaded_enclosing_instance_remains_distinct_from_actual_child_occurrence() {
    use telltale_machine::{ThreadedProtocolMachine, ThreadedRoundSemantics};
    let image = image(CHILD_SOURCE);
    let config = ProtocolMachineConfig {
        threaded_round_semantics: ThreadedRoundSemantics::CanonicalOneStep,
        ..ProtocolMachineConfig::default()
    };
    let mut machine = ThreadedProtocolMachine::with_workers(config, 2);
    let admitted = machine.load_choreography_owned(&image, "original");
    let provider = ChildProvider {
        calls: std::sync::Mutex::new(Vec::new()),
        block_first: true,
    };
    let mut first_failure = None;
    if admitted.is_ok() {
        for _ in 0..16 {
            if let Err(error) = machine.step_round(&provider, 1) {
                first_failure = Some(error);
                break;
            }
            if !provider
                .calls
                .lock()
                .expect("actual callback observation")
                .is_empty()
            {
                break;
            }
        }
    }
    let before = machine.semantic_objects();
    let finished = if admitted.is_ok() && first_failure.is_none() {
        Some(machine.run(&provider, 64))
    } else {
        None
    };
    let after = machine.semantic_objects();
    let calls = provider.calls.lock().expect("actual callbacks").clone();
    let joined = machine.shutdown_worker_pool();
    assert!(
        joined.is_ok(),
        "same actual pool joined before final assertions"
    );
    assert!(admitted.is_ok());
    assert!(first_failure.is_none());
    assert!(finished.expect("actual admitted execution").is_ok());
    let original = before
        .operation_instances
        .iter()
        .find(|record| record.operation_id.starts_with("operation:"))
        .expect("actual original source Begin");
    assert!(matches!(
        original.phase,
        OperationPhase::Pending | OperationPhase::Blocked
    ));
    assert_eq!(original.effect_ids.len(), 1);
    assert!(before
        .operation_instances
        .iter()
        .any(|child| child.operation_id != original.operation_id
            && child.effect_ids == original.effect_ids));
    let terminal = after
        .operation_instances
        .iter()
        .find(|record| record.operation_id == original.operation_id)
        .expect("same actual enclosing instance");
    assert_eq!(terminal.phase, OperationPhase::Succeeded);
    assert_eq!(terminal.effect_ids, original.effect_ids);
    assert_eq!(calls.len(), 2);
    assert!(calls.iter().all(|id| *id == original.effect_ids[0]));
}

telltale::tell! {
    agreement_profile LifecycleLocal
      visibility immediate
      rule no_agreement
      usable_at none
      finalized_at none
      evidence witness
    operation Flow at A progress FlowProgress within bounded agreement LifecycleLocal =
      begin Flow
      await Flow
      resolve Flow as Success
    protocol MacroOperationBoundary =
      roles A, B
      A -> B : Start
}

#[test]
fn macro_selected_operation_executes_actual_lifecycle_opcodes() {
    let image = MacroOperationBoundary::operation_image(
        "Flow",
        &BTreeMap::from([(
            "bounded".into(),
            NonZeroU64::new(64).expect("selected window"),
        )]),
    )
    .expect("actual macro-preserved original source lowering");
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine
        .load_choreography_owned(&image, "original")
        .expect("actual issued owner");
    machine
        .run(&super::NoopHandler, 64)
        .expect("actual source operation execution");
    let original = machine
        .operation_instances()
        .iter()
        .find(|record| record.operation_id.starts_with("operation:"))
        .expect("real original source operation");
    assert_eq!(original.phase, OperationPhase::Succeeded);
    assert!(original.requires_proof);
}

#[test]
fn original_child_failure_remains_the_standard_operation_error_source() {
    use std::error::Error;
    use telltale_machine::model::effects::EffectFailure;
    use telltale_machine::operation_lifecycle::OperationTransitionError;

    let error = OperationTransitionError::Child(EffectFailure::contract_violation("actual child"));
    let source = error
        .source()
        .expect("original child is exposed through the standard error chain")
        .downcast_ref::<EffectFailure>()
        .expect("the typed semantic child failure remains inspectable");
    let OperationTransitionError::Child(original) = &error else {
        unreachable!("selected original child carrier")
    };
    assert!(std::ptr::eq(source, original));
    let foreign = EffectFailure::contract_violation("actual child");
    assert!(!std::ptr::eq(source, &foreign));
    assert!(OperationTransitionError::Contract("missing child")
        .source()
        .is_none());
}

#[test]
fn manual_timeout_descriptor_cannot_bypass_original_escalation_lowering() {
    use telltale_machine::instr::{Instr, InvokeAction};
    use telltale_machine::operation_lifecycle::{OperationAction, OperationResolution};

    let mut image = image(SOURCE);
    let program = image.programs.get_mut("A").expect("actual owner program");
    let actual = program
        .iter_mut()
        .find(|instruction| {
            matches!(instruction,
        Instr::Invoke { action: InvokeAction::OperationLifecycle(action) }
        if matches!(action.as_ref(), OperationAction::Resolve { .. }))
        })
        .expect("actual source resolve instruction");
    *actual = Instr::Invoke {
        action: InvokeAction::OperationLifecycle(Box::new(OperationAction::Resolve {
            operation: "Flow".into(),
            outcome: OperationResolution::Timeout(None),
        })),
    };
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    assert!(machine.load_choreography_owned(&image, "original").is_err());
    assert!(machine.operation_instances().is_empty());
    assert!(machine.outstanding_effects().is_empty());
}
