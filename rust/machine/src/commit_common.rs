//! Shared commit-phase helpers used by cooperative and threaded backends.

use serde_json::json;

use crate::coroutine::Fault;
use crate::effect::{infer_effect_interface_and_operation, EffectTraceEntry};
use crate::engine::ObsEvent;
use crate::output_condition::{
    verify_output_condition, OutputConditionCheck, OutputConditionHint, OutputConditionMeta,
    OutputConditionPolicy,
};

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
    let digest = "vm.output_digest.unspecified".to_string();
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
