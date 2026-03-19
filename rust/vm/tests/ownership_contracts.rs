#![cfg(not(target_arch = "wasm32"))]
#![allow(missing_docs)]

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use std::collections::{BTreeMap, BTreeSet};

use cfg_if::cfg_if;
use telltale_types::{GlobalType, LocalTypeR, ValType};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::{EffectHandler, SendDecision, SendDecisionInput};
use telltale_vm::instr::{ImmValue, Instr};
use telltale_vm::loader::CodeImage;
use telltale_vm::vm::ObsEvent;
use telltale_vm::{
    run_loaded_vm_record_replay_conformance, DelegationStatus, Edge, OwnershipError,
    OwnershipScope, SessionHostMutation, VMConfig, VM,
};
use test_support::simple_send_recv_image;

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        use telltale_vm::ThreadedVM;
    }
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
    ) -> Result<Value, String> {
        Ok(Value::Unit)
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

fn transfer_image() -> CodeImage {
    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);
    local_types.insert("B".to_string(), LocalTypeR::End);

    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![
            Instr::Set {
                dst: 1,
                val: ImmValue::Nat(1),
            },
            Instr::Transfer {
                endpoint: 0,
                target: 1,
                bundle: 2,
            },
            Instr::Halt,
        ],
    );
    programs.insert("B".to_string(), vec![Instr::Halt]);

    CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    }
}

#[test]
fn ownership_owned_session_transfer_invalidates_stale_handles() {
    let image = simple_send_recv_image("A", "B", "m");
    let mut vm = VM::new(VMConfig::default());
    let owned = vm
        .load_choreography_owned(&image, "runtime/owner")
        .expect("owned open should succeed");
    let receipt = owned
        .begin_transfer(
            &mut vm,
            "runtime/owner",
            OwnershipScope::Fragments(BTreeSet::from(["A".to_string()])),
        )
        .expect("transfer staging should succeed");
    let narrowed = owned
        .commit_transfer(&mut vm, &receipt)
        .expect("transfer commit should succeed");
    let edge = Edge::new(owned.session_id(), "A", "B");

    let stale = owned
        .apply_host_mutation(
            &mut vm,
            SessionHostMutation::UpdateTrace {
                edge: edge.clone(),
                trace: vec![ValType::Nat],
            },
        )
        .expect_err("stale owner must be rejected");
    assert!(matches!(
        stale,
        OwnershipError::StaleCapability {
            owner_id,
            expected_generation: 0,
            actual_generation: 1,
            ..
        } if owner_id == "runtime/owner"
    ));

    let scope = narrowed
        .apply_host_mutation(
            &mut vm,
            SessionHostMutation::UpdateTrace {
                edge,
                trace: vec![ValType::Bool],
            },
        )
        .expect_err("fragment-scoped owner must not mutate session-local host state");
    assert!(matches!(
        scope,
        OwnershipError::ScopeViolation {
            required: OwnershipScope::Session,
            actual: OwnershipScope::Fragments(_),
            ..
        }
    ));
}

#[test]
fn ownership_transfer_record_replay_preserves_observable_handoff() {
    let mut vm = VM::new(VMConfig::default());
    vm.load_choreography(&transfer_image())
        .expect("load transfer fixture");

    let report = run_loaded_vm_record_replay_conformance(&mut vm, &NoopHandler, 32)
        .expect("record/replay harness should succeed");

    assert!(report.replay_consistent);
    assert!(report.exact_trace_match);
    assert!(
        vm.trace()
            .iter()
            .any(|event| matches!(event, ObsEvent::Transferred { role, from, to, .. } if role == "A" && from == &0 && to == &1)),
        "transfer fixture must emit an observable handoff"
    );
    let audit = vm
        .delegation_audit_log()
        .last()
        .expect("transfer fixture should emit a delegation audit");
    assert_eq!(audit.status, DelegationStatus::Committed);
    assert_eq!(
        audit.receipt.scope,
        OwnershipScope::Fragments(BTreeSet::from(["A".to_string()]))
    );
}

cfg_if! {
    if #[cfg(feature = "multi-thread")] {
        #[test]
        fn threaded_ownership_transfer_matches_cooperative_audit_surface() {
            let image = transfer_image();

            let mut coop = VM::new(VMConfig::default());
            coop.load_choreography(&image)
                .expect("load cooperative transfer fixture");
            coop.run(&NoopHandler, 32)
                .expect("run cooperative transfer fixture");

            let mut threaded = ThreadedVM::with_workers(VMConfig::default(), 2);
            threaded
                .load_choreography(&image)
                .expect("load threaded transfer fixture");
            threaded
                .run(&NoopHandler, 32)
                .expect("run threaded transfer fixture");

            let coop_transfers: Vec<_> = coop
                .trace()
                .iter()
                .filter_map(|event| match event {
                    ObsEvent::Transferred {
                        session,
                        role,
                        from,
                        to,
                        ..
                    } => Some((*session, role.clone(), *from, *to)),
                    _ => None,
                })
                .collect();
            let threaded_transfers: Vec<_> = threaded
                .trace()
                .iter()
                .filter_map(|event| match event {
                    ObsEvent::Transferred {
                        session,
                        role,
                        from,
                        to,
                        ..
                    } => Some((*session, role.clone(), *from, *to)),
                    _ => None,
                })
                .collect();

            assert_eq!(coop_transfers, threaded_transfers);

            let coop_audit = coop
                .delegation_audit_log()
                .last()
                .expect("cooperative transfer should emit audit");
            let threaded_audit = threaded
                .delegation_audit_log()
                .last()
                .expect("threaded transfer should emit audit");

            assert_eq!(coop_audit.status, threaded_audit.status);
            assert_eq!(coop_audit.receipt.endpoint, threaded_audit.receipt.endpoint);
            assert_eq!(coop_audit.receipt.scope, threaded_audit.receipt.scope);
            assert_eq!(coop_audit.receipt.from_coro, threaded_audit.receipt.from_coro);
            assert_eq!(coop_audit.receipt.to_coro, threaded_audit.receipt.to_coro);
        }
    }
}
