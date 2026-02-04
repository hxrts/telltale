//! Trace normalization utilities.
//!
//! Session-local normalization reassigns ticks based on per-session
//! event counts. Global ticks are preserved for non-session events.

use std::collections::HashMap;

use crate::session::SessionId;
use crate::vm::ObsEvent;

/// Extract the session id from an observable event, if present.
#[must_use]
pub fn obs_session(ev: &ObsEvent) -> Option<SessionId> {
    match ev {
        ObsEvent::Sent { session, .. }
        | ObsEvent::Received { session, .. }
        | ObsEvent::Opened { session, .. }
        | ObsEvent::Closed { session, .. }
        | ObsEvent::Acquired { session, .. }
        | ObsEvent::Released { session, .. }
        | ObsEvent::Transferred { session, .. }
        | ObsEvent::Forked { session, .. }
        | ObsEvent::Joined { session, .. }
        | ObsEvent::Aborted { session, .. }
        | ObsEvent::Tagged { session, .. }
        | ObsEvent::Checked { session, .. } => Some(*session),
        ObsEvent::Halted { .. } | ObsEvent::Invoked { .. } | ObsEvent::Faulted { .. } => None,
    }
}

/// Clone an event with a new tick value.
#[must_use]
pub fn with_tick(ev: &ObsEvent, tick: u64) -> ObsEvent {
    match ev {
        ObsEvent::Sent {
            session,
            from,
            to,
            label,
            ..
        } => ObsEvent::Sent {
            tick,
            session: *session,
            from: from.clone(),
            to: to.clone(),
            label: label.clone(),
        },
        ObsEvent::Received {
            session,
            from,
            to,
            label,
            ..
        } => ObsEvent::Received {
            tick,
            session: *session,
            from: from.clone(),
            to: to.clone(),
            label: label.clone(),
        },
        ObsEvent::Opened { session, roles, .. } => ObsEvent::Opened {
            tick,
            session: *session,
            roles: roles.clone(),
        },
        ObsEvent::Closed { session, .. } => ObsEvent::Closed {
            tick,
            session: *session,
        },
        ObsEvent::Halted { coro_id, .. } => ObsEvent::Halted {
            tick,
            coro_id: *coro_id,
        },
        ObsEvent::Invoked { coro_id, role, .. } => ObsEvent::Invoked {
            tick,
            coro_id: *coro_id,
            role: role.clone(),
        },
        ObsEvent::Acquired {
            session, role, layer, ..
        } => ObsEvent::Acquired {
            tick,
            session: *session,
            role: role.clone(),
            layer: layer.clone(),
        },
        ObsEvent::Released {
            session, role, layer, ..
        } => ObsEvent::Released {
            tick,
            session: *session,
            role: role.clone(),
            layer: layer.clone(),
        },
        ObsEvent::Transferred {
            session, role, from, to, ..
        } => ObsEvent::Transferred {
            tick,
            session: *session,
            role: role.clone(),
            from: *from,
            to: *to,
        },
        ObsEvent::Forked {
            session, ghost, ..
        } => ObsEvent::Forked {
            tick,
            session: *session,
            ghost: *ghost,
        },
        ObsEvent::Joined { session, .. } => ObsEvent::Joined {
            tick,
            session: *session,
        },
        ObsEvent::Aborted { session, .. } => ObsEvent::Aborted {
            tick,
            session: *session,
        },
        ObsEvent::Tagged { session, role, fact, .. } => ObsEvent::Tagged {
            tick,
            session: *session,
            role: role.clone(),
            fact: fact.clone(),
        },
        ObsEvent::Checked {
            session,
            role,
            target,
            permitted,
            ..
        } => ObsEvent::Checked {
            tick,
            session: *session,
            role: role.clone(),
            target: target.clone(),
            permitted: *permitted,
        },
        ObsEvent::Faulted { coro_id, fault, .. } => ObsEvent::Faulted {
            tick,
            coro_id: *coro_id,
            fault: fault.clone(),
        },
    }
}

/// Normalize a trace by assigning session-local ticks.
#[must_use]
pub fn normalize_trace(trace: &[ObsEvent]) -> Vec<ObsEvent> {
    let mut counters: HashMap<SessionId, u64> = HashMap::new();
    let mut out = Vec::with_capacity(trace.len());
    for ev in trace {
        if let Some(session) = obs_session(ev) {
            let counter = counters.entry(session).or_insert(0);
            let local_tick = *counter;
            *counter += 1;
            out.push(with_tick(ev, local_tick));
        } else {
            out.push(ev.clone());
        }
    }
    out
}

/// Clone a trace without normalization.
#[must_use]
pub fn strict_trace(trace: &[ObsEvent]) -> Vec<ObsEvent> {
    trace.to_vec()
}
