//! Shared commit-phase helpers used by cooperative and threaded backends.

use serde_json::json;

use crate::coroutine::Fault;
use crate::effect::{infer_effect_interface_and_operation, EffectTraceEntry};
use crate::engine::ObsEvent;
use crate::output_condition::{
    verify_output_condition, OutputConditionCheck, OutputConditionHint, OutputConditionMeta,
    OutputConditionPolicy,
};

/// Check a complete dispatch's fresh occurrence bound without consuming IDs.
/// `u64::MAX` remains the exhausted sentinel; zero-fresh settlement is valid there.
pub(crate) fn require_effect_capacity(
    next: u64,
    additional: u64,
) -> Result<(), crate::effect::EffectFailure> {
    if additional <= u64::MAX - next {
        Ok(())
    } else {
        Err(crate::effect::EffectFailure::contract_violation(
            "canonical effect occurrence identifiers exhausted",
        ))
    }
}

/// Conservative fresh occurrence bound, before any instruction or host mutation.
/// Unused capacity is never allocated, so ordinary occurrence order is unchanged.
pub(crate) fn instruction_effect_capacity(
    instr: &crate::instr::Instr,
    nominal_already_issued: bool,
) -> u64 {
    use crate::instr::{Instr, InvokeAction};
    match instr {
        Instr::Send { .. }
        | Instr::Receive { .. }
        | Instr::Offer { .. }
        | Instr::Choose { .. }
        | Instr::Acquire { .. }
        | Instr::Release { .. }
        | Instr::Invoke {
            action: InvokeAction::Named(_) | InvokeAction::Reg(_),
        } => 4,
        Instr::Invoke {
            action: InvokeAction::NominalCommand(_),
        } => {
            if nominal_already_issued {
                3
            } else {
                4
            }
        }
        Instr::Open { .. }
        | Instr::Close { .. }
        | Instr::Fork { .. }
        | Instr::Join
        | Instr::Abort
        | Instr::Transfer { .. }
        | Instr::Tag { .. }
        | Instr::Check { .. } => 2,
        Instr::Set { .. }
        | Instr::Move { .. }
        | Instr::Jump { .. }
        | Instr::Spawn { .. }
        | Instr::Yield
        | Instr::Halt
        | Instr::Invoke {
            action: InvokeAction::DeclareCommand(_) | InvokeAction::OperationLifecycle(_),
        } => 0,
    }
}

/// Count only events that the canonical trace producer turns into occurrences.
pub(crate) fn derived_effect_count(
    events: &[ObsEvent],
) -> Result<u64, crate::effect::EffectFailure> {
    u64::try_from(
        events
            .iter()
            .filter(|event| {
                matches!(
                    event,
                    ObsEvent::Sent { .. }
                        | ObsEvent::Received { .. }
                        | ObsEvent::Invoked { .. }
                        | ObsEvent::Acquired { .. }
                        | ObsEvent::Released { .. }
                )
            })
            .count(),
    )
    .map_err(|_| {
        crate::effect::EffectFailure::contract_violation("derived effect batch count exceeds u64")
    })
}

/// Apply output-condition verification for a commit and record diagnostics.
pub(crate) fn apply_output_condition_gate<RecordCheck, RecordEvent>(
    policy: &OutputConditionPolicy,
    mut record_check: RecordCheck,
    mut record_event: RecordEvent,
    tick: u64,
    output_hint: Option<OutputConditionHint>,
) -> Result<(), Fault>
where
    RecordCheck: FnMut(OutputConditionCheck),
    RecordEvent: FnMut(ObsEvent),
{
    let digest = "machine.output_digest.unspecified".to_string();
    let meta = match output_hint {
        Some(h) => OutputConditionMeta::from_hint(h, digest),
        None => OutputConditionMeta::default_observable(digest),
    };
    let passed = verify_output_condition(policy, &meta);
    record_check(OutputConditionCheck {
        meta: meta.clone(),
        passed,
    });
    record_event(ObsEvent::OutputConditionChecked {
        tick,
        predicate_ref: meta.predicate_ref.clone(),
        witness_ref: meta.witness_ref.clone(),
        output_digest: meta.output_digest.clone(),
        passed,
    });
    if passed {
        Ok(())
    } else {
        Err(Fault::OutputCondition {
            predicate_ref: meta.predicate_ref,
        })
    }
}

/// Build canonical effect-trace entry from an observable event, if applicable.
#[allow(clippy::too_many_lines)]
pub(crate) fn effect_trace_entry_for_event(
    ev: &ObsEvent,
    effect_id: u64,
    handler_identity: &str,
    ordering_key: u64,
) -> Option<EffectTraceEntry> {
    match ev {
        ObsEvent::Sent {
            session,
            from,
            to,
            label,
            ..
        } => {
            let effect_kind = "send_decision".to_string();
            let (effect_interface, effect_operation) =
                infer_effect_interface_and_operation(&effect_kind);
            Some(EffectTraceEntry {
                effect_id,
                effect_kind,
                inputs: json!({
                    "session": session,
                    "from": from,
                    "to": to,
                    "label": label,
                }),
                outputs: json!({"committed": true}),
                handler_identity: handler_identity.to_string(),
                effect_interface,
                effect_operation,
                ordering_key,
                topology: None,
            })
        }
        ObsEvent::Received {
            session,
            from,
            to,
            label,
            ..
        } => {
            let effect_kind = "handle_recv".to_string();
            let (effect_interface, effect_operation) =
                infer_effect_interface_and_operation(&effect_kind);
            Some(EffectTraceEntry {
                effect_id,
                effect_kind,
                inputs: json!({
                    "session": session,
                    "from": from,
                    "to": to,
                    "label": label,
                }),
                outputs: json!({"committed": true}),
                handler_identity: handler_identity.to_string(),
                effect_interface,
                effect_operation,
                ordering_key,
                topology: None,
            })
        }
        ObsEvent::Invoked { coro_id, role, .. } => {
            let effect_kind = "invoke_step".to_string();
            let (effect_interface, effect_operation) =
                infer_effect_interface_and_operation(&effect_kind);
            Some(EffectTraceEntry {
                effect_id,
                effect_kind,
                inputs: json!({
                    "coro_id": coro_id,
                    "role": role,
                }),
                outputs: json!({"ok": true}),
                handler_identity: handler_identity.to_string(),
                effect_interface,
                effect_operation,
                ordering_key,
                topology: None,
            })
        }
        ObsEvent::Acquired {
            session,
            role,
            layer,
            ..
        } => {
            let effect_kind = "handle_acquire".to_string();
            let (effect_interface, effect_operation) =
                infer_effect_interface_and_operation(&effect_kind);
            Some(EffectTraceEntry {
                effect_id,
                effect_kind,
                inputs: json!({
                    "session": session,
                    "role": role,
                    "layer": layer,
                }),
                outputs: json!({"granted": true}),
                handler_identity: handler_identity.to_string(),
                effect_interface,
                effect_operation,
                ordering_key,
                topology: None,
            })
        }
        ObsEvent::Released {
            session,
            role,
            layer,
            ..
        } => {
            let effect_kind = "handle_release".to_string();
            let (effect_interface, effect_operation) =
                infer_effect_interface_and_operation(&effect_kind);
            Some(EffectTraceEntry {
                effect_id,
                effect_kind,
                inputs: json!({
                    "session": session,
                    "role": role,
                    "layer": layer,
                }),
                outputs: json!({"ok": true}),
                handler_identity: handler_identity.to_string(),
                effect_interface,
                effect_operation,
                ordering_key,
                topology: None,
            })
        }
        _ => None,
    }
}
