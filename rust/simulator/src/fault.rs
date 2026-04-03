//! Budgeted adversary middleware for simulator transport and crash disturbances.
#![allow(missing_docs)]

use std::collections::{BTreeSet, HashSet};
use std::sync::Mutex;

use serde::{Deserialize, Serialize};
use telltale_machine::buffer::EnqueueResult;
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_machine::model::state::SessionId;
use telltale_machine::ObsEvent;
use telltale_types::FixedQ32;

use crate::rng::SimRng;
use crate::value_conv::{
    fixed_to_value, fixed_vec_to_value, try_decode_fixed, try_decode_fixed_vec,
};

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, PartialOrd, Ord, Default)]
#[serde(rename_all = "snake_case")]
pub enum AssumptionFailureClass {
    QuorumIntersectionFailure,
    AuthenticationEvidenceFailure,
    #[default]
    FairnessFailure,
    BudgetExhaustion,
    UnsupportedRegime,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum AdversaryAction {
    Withholding,
    TimingDisturbance {
        ticks: usize,
    },
    Corruption,
    Crash {
        role: String,
        duration: Option<usize>,
    },
    ByzantineInterference {
        withholding_probability: FixedQ32,
        corruption_probability: FixedQ32,
        delay_ticks: Option<usize>,
    },
}

impl AdversaryAction {
    #[must_use]
    pub fn default_assumption_failure(&self) -> AssumptionFailureClass {
        match self {
            Self::Withholding | Self::TimingDisturbance { .. } | Self::Crash { .. } => {
                AssumptionFailureClass::FairnessFailure
            }
            Self::Corruption | Self::ByzantineInterference { .. } => {
                AssumptionFailureClass::AuthenticationEvidenceFailure
            }
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "mode", rename_all = "snake_case")]
pub enum AdversaryBudgetMode {
    Activation,
    Independent {
        probability: FixedQ32,
    },
    Windowed {
        window_ticks: u64,
        max_per_window: u64,
    },
    Correlated {
        probability: FixedQ32,
        burst_ticks: u64,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct AdversaryBudget {
    pub total: u64,
    pub assumption_failure: AssumptionFailureClass,
    pub mode: AdversaryBudgetMode,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub enum Trigger {
    Immediate,
    AtTick(u64),
    AfterStep(u64),
    Random(FixedQ32),
    OnEvent { kind: String, role: Option<String> },
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ScheduledAdversary {
    pub adversary_id: String,
    pub action: AdversaryAction,
    pub trigger: Trigger,
    pub budget: AdversaryBudget,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct AdversaryProgram {
    pub adversaries: Vec<ScheduledAdversary>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum AdversaryBudgetRecordKind {
    Activated,
    Consumed,
    Exhausted,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct AdversaryBudgetRecord {
    pub tick: u64,
    pub adversary_id: String,
    pub kind: AdversaryBudgetRecordKind,
    pub total_consumed: u64,
    pub total_remaining: u64,
    pub detail: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct AssumptionDiagnostic {
    pub tick: u64,
    pub class: AssumptionFailureClass,
    pub adversary_id: Option<String>,
    pub detail: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct AdversarySummary {
    pub declared_adversaries: usize,
    pub activated_adversaries: usize,
    pub budget_consumed: u64,
    pub exhausted_adversaries: Vec<String>,
    pub assumption_failures: Vec<AssumptionFailureClass>,
}

#[derive(Debug, Clone)]
struct ScheduledAdversaryState {
    adversary: ScheduledAdversary,
    activated: bool,
}

#[derive(Debug, Clone, Default)]
struct BudgetState {
    total_consumed: u64,
    current_window: Option<u64>,
    consumed_in_window: u64,
    burst_expires_at: Option<u64>,
}

impl BudgetState {
    fn remaining(&self, budget: &AdversaryBudget) -> u64 {
        budget.total.saturating_sub(self.total_consumed)
    }
}

#[derive(Debug, Clone)]
struct ActiveTransportAdversary {
    adversary_id: String,
    action: AdversaryAction,
    budget: AdversaryBudget,
    budget_state: BudgetState,
}

#[derive(Debug, Clone)]
struct ActiveCrash {
    role: String,
    expires_at: Option<u64>,
}

#[derive(Debug, Clone)]
struct InFlightMessage {
    delivery_tick: u64,
    sid: SessionId,
    from: String,
    to: String,
    value: Value,
}

struct AdversaryState {
    scheduled: Vec<ScheduledAdversaryState>,
    active_transport: Vec<ActiveTransportAdversary>,
    active_crashes: Vec<ActiveCrash>,
    rng: SimRng,
    in_flight: Vec<InFlightMessage>,
    current_tick: u64,
    last_trace_len: usize,
    crashed_roles: BTreeSet<String>,
    budget_history: Vec<AdversaryBudgetRecord>,
    assumption_diagnostics: Vec<AssumptionDiagnostic>,
}

impl AdversaryState {
    fn refresh_crashed_roles(&mut self) {
        self.crashed_roles = self
            .active_crashes
            .iter()
            .map(|crash| crash.role.clone())
            .collect();
    }

    fn is_crashed(&self, role: &str) -> bool {
        self.crashed_roles.contains(role)
    }
}

pub struct AdversaryInjector<H: EffectHandler> {
    inner: H,
    program: Vec<ScheduledAdversary>,
    state: Mutex<AdversaryState>,
}

impl<H: EffectHandler> AdversaryInjector<H> {
    fn lock_state(&self) -> Result<std::sync::MutexGuard<'_, AdversaryState>, String> {
        self.state
            .lock()
            .map_err(|_| "adversary state lock poisoned".to_string())
    }

    #[must_use]
    pub fn new(inner: H, program: AdversaryProgram, rng: SimRng) -> Self {
        let scheduled = program
            .adversaries
            .iter()
            .cloned()
            .map(|adversary| ScheduledAdversaryState {
                adversary,
                activated: false,
            })
            .collect();
        Self {
            inner,
            program: program.adversaries,
            state: Mutex::new(AdversaryState {
                scheduled,
                active_transport: Vec::new(),
                active_crashes: Vec::new(),
                rng,
                in_flight: Vec::new(),
                current_tick: 0,
                last_trace_len: 0,
                crashed_roles: BTreeSet::new(),
                budget_history: Vec::new(),
                assumption_diagnostics: Vec::new(),
            }),
        }
    }

    pub fn tick(&self, tick: u64, logical_step: u64, trace: &[ObsEvent]) -> Result<(), String> {
        let mut state = self.lock_state()?;
        state.current_tick = tick;

        let new_events = trace.get(state.last_trace_len..).unwrap_or(&[]);

        state
            .active_crashes
            .retain(|crash| crash.expires_at.map_or(true, |exp| tick < exp));
        state
            .active_transport
            .retain(|adversary| adversary.budget_state.remaining(&adversary.budget) > 0);

        let AdversaryState {
            scheduled,
            active_transport,
            active_crashes,
            rng,
            budget_history,
            assumption_diagnostics,
            ..
        } = &mut *state;

        for scheduled in scheduled.iter_mut() {
            if scheduled.activated {
                continue;
            }
            if !trigger_fires(
                &scheduled.adversary.trigger,
                tick,
                logical_step,
                new_events,
                rng,
            ) {
                continue;
            }
            scheduled.activated = true;
            budget_history.push(AdversaryBudgetRecord {
                tick,
                adversary_id: scheduled.adversary.adversary_id.clone(),
                kind: AdversaryBudgetRecordKind::Activated,
                total_consumed: 0,
                total_remaining: scheduled.adversary.budget.total,
                detail: "activated".to_string(),
            });

            match &scheduled.adversary.action {
                AdversaryAction::Crash { role, duration } => {
                    let mut budget_state = BudgetState::default();
                    if consume_budget(
                        &scheduled.adversary.adversary_id,
                        &scheduled.adversary.budget,
                        &mut budget_state,
                        tick,
                        "crash activation",
                        budget_history,
                        assumption_diagnostics,
                    ) {
                        let expires_at = duration.map(|value| {
                            tick.saturating_add(u64::try_from(value).unwrap_or(u64::MAX))
                        });
                        active_crashes.push(ActiveCrash {
                            role: role.clone(),
                            expires_at,
                        });
                    }
                }
                _ => active_transport.push(ActiveTransportAdversary {
                    adversary_id: scheduled.adversary.adversary_id.clone(),
                    action: scheduled.adversary.action.clone(),
                    budget: scheduled.adversary.budget.clone(),
                    budget_state: BudgetState::default(),
                }),
            }
        }

        state.refresh_crashed_roles();
        state.last_trace_len = trace.len();
        Ok(())
    }

    pub fn deliver<F>(&self, tick: u64, mut inject: F) -> Result<(), String>
    where
        F: FnMut(SessionId, &str, &str, Value) -> Result<EnqueueResult, String>,
    {
        let mut state = self.lock_state()?;
        let mut pending = Vec::new();
        let mut deliver_now = Vec::new();

        for msg in state.in_flight.drain(..) {
            if msg.delivery_tick <= tick {
                deliver_now.push(msg);
            } else {
                pending.push(msg);
            }
        }
        state.in_flight = pending;

        let mut retry = Vec::new();
        for msg in deliver_now {
            let InFlightMessage {
                sid,
                from,
                to,
                value,
                ..
            } = msg;
            match inject(sid, &from, &to, value.clone()) {
                Ok(EnqueueResult::Ok | EnqueueResult::Dropped) => {}
                Ok(EnqueueResult::WouldBlock | EnqueueResult::Full) => {
                    retry.push(InFlightMessage {
                        delivery_tick: tick.saturating_add(1),
                        sid,
                        from,
                        to,
                        value,
                    });
                }
                Err(err) => {
                    return Err(format!(
                        "adversary delivery inject failed for edge {from}->{to} (sid={sid}): {err}"
                    ));
                }
            }
        }
        state.in_flight.extend(retry);
        Ok(())
    }

    pub fn crashed_roles(&self) -> Result<BTreeSet<String>, String> {
        Ok(self.lock_state()?.crashed_roles.clone())
    }

    pub fn program(&self) -> Vec<ScheduledAdversary> {
        self.program.clone()
    }

    pub fn budget_history(&self) -> Result<Vec<AdversaryBudgetRecord>, String> {
        Ok(self.lock_state()?.budget_history.clone())
    }

    pub fn assumption_diagnostics(&self) -> Result<Vec<AssumptionDiagnostic>, String> {
        Ok(self.lock_state()?.assumption_diagnostics.clone())
    }

    pub fn summary(&self) -> Result<AdversarySummary, String> {
        let state = self.lock_state()?;
        let mut activated = HashSet::new();
        let mut exhausted = Vec::new();
        let mut consumed = 0_u64;
        for record in &state.budget_history {
            match record.kind {
                AdversaryBudgetRecordKind::Activated => {
                    activated.insert(record.adversary_id.clone());
                }
                AdversaryBudgetRecordKind::Consumed => {
                    consumed = consumed.saturating_add(1);
                }
                AdversaryBudgetRecordKind::Exhausted => exhausted.push(record.adversary_id.clone()),
            }
        }
        exhausted.sort();
        exhausted.dedup();

        let mut assumption_failures = state
            .assumption_diagnostics
            .iter()
            .map(|diagnostic| diagnostic.class)
            .collect::<Vec<_>>();
        assumption_failures.sort();
        assumption_failures.dedup();

        Ok(AdversarySummary {
            declared_adversaries: self.program.len(),
            activated_adversaries: activated.len(),
            budget_consumed: consumed,
            exhausted_adversaries: exhausted,
            assumption_failures,
        })
    }
}

impl<H: EffectHandler> EffectHandler for AdversaryInjector<H> {
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        self.inner.handle_send(role, partner, label, state)
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        let base = match self.inner.send_decision(input.clone()) {
            EffectResult::Success(base) => base,
            EffectResult::Blocked => return EffectResult::Blocked,
            EffectResult::Failure(failure) => return EffectResult::Failure(failure),
        };
        let SendDecision::Deliver(mut payload) = base else {
            return EffectResult::success(base);
        };

        let mut state = match self.lock_state() {
            Ok(state) => state,
            Err(err) => return EffectResult::failure(EffectFailure::contract_violation(err)),
        };
        if state.is_crashed(input.role) {
            return EffectResult::failure(EffectFailure::topology_disruption("node crashed"));
        }

        let tick = state.current_tick;
        let AdversaryState {
            active_transport,
            rng,
            budget_history,
            assumption_diagnostics,
            in_flight,
            ..
        } = &mut *state;

        let mut should_drop = false;
        let mut max_delay: Option<usize> = None;

        for adversary in active_transport.iter_mut() {
            if !should_apply_transport_adversary(adversary, tick, rng) {
                continue;
            }
            if !consume_budget(
                &adversary.adversary_id,
                &adversary.budget,
                &mut adversary.budget_state,
                tick,
                "transport disturbance",
                budget_history,
                assumption_diagnostics,
            ) {
                continue;
            }
            let outcome = apply_transport_action(&adversary.action, payload, rng);
            payload = outcome.payload;
            should_drop |= outcome.drop;
            if let Some(delay) = outcome.delay_ticks {
                max_delay = Some(max_delay.map_or(delay, |current| current.max(delay)));
            }
            if should_drop {
                break;
            }
        }

        if should_drop {
            return EffectResult::success(SendDecision::Drop);
        }

        if let Some(delay) = max_delay {
            let delivery_tick = tick.saturating_add(u64::try_from(delay).unwrap_or(u64::MAX));
            in_flight.push(InFlightMessage {
                delivery_tick,
                sid: input.sid,
                from: input.role.to_string(),
                to: input.partner.to_string(),
                value: payload,
            });
            return EffectResult::success(SendDecision::Defer);
        }

        EffectResult::success(SendDecision::Deliver(payload))
    }

    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        match self.lock_state() {
            Ok(state_guard) => {
                if state_guard.is_crashed(role) {
                    return EffectResult::failure(EffectFailure::topology_disruption(
                        "node crashed",
                    ));
                }
            }
            Err(err) => return EffectResult::failure(EffectFailure::contract_violation(err)),
        }
        self.inner.handle_recv(role, partner, label, state, payload)
    }

    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> EffectResult<String> {
        self.inner.handle_choose(role, partner, labels, state)
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> EffectResult<()> {
        match self.lock_state() {
            Ok(state_guard) => {
                if state_guard.is_crashed(role) {
                    return EffectResult::failure(EffectFailure::topology_disruption(
                        "node crashed",
                    ));
                }
            }
            Err(err) => return EffectResult::failure(EffectFailure::contract_violation(err)),
        }
        self.inner.step(role, state)
    }
}

#[derive(Debug)]
struct TransportOutcome {
    drop: bool,
    payload: Value,
    delay_ticks: Option<usize>,
}

fn apply_transport_action(
    action: &AdversaryAction,
    payload: Value,
    rng: &mut SimRng,
) -> TransportOutcome {
    match action {
        AdversaryAction::Withholding => TransportOutcome {
            drop: true,
            payload,
            delay_ticks: None,
        },
        AdversaryAction::TimingDisturbance { ticks } => TransportOutcome {
            drop: false,
            payload,
            delay_ticks: Some(*ticks),
        },
        AdversaryAction::Corruption => TransportOutcome {
            drop: false,
            payload: corrupt_value(payload),
            delay_ticks: None,
        },
        AdversaryAction::Crash { .. } => TransportOutcome {
            drop: false,
            payload,
            delay_ticks: None,
        },
        AdversaryAction::ByzantineInterference {
            withholding_probability,
            corruption_probability,
            delay_ticks,
        } => {
            if *withholding_probability > FixedQ32::zero()
                && rng.should_trigger(*withholding_probability)
            {
                return TransportOutcome {
                    drop: true,
                    payload,
                    delay_ticks: None,
                };
            }
            if *corruption_probability > FixedQ32::zero()
                && rng.should_trigger(*corruption_probability)
            {
                return TransportOutcome {
                    drop: false,
                    payload: corrupt_value(payload),
                    delay_ticks: None,
                };
            }
            TransportOutcome {
                drop: false,
                payload,
                delay_ticks: *delay_ticks,
            }
        }
    }
}

fn should_apply_transport_adversary(
    adversary: &mut ActiveTransportAdversary,
    tick: u64,
    rng: &mut SimRng,
) -> bool {
    if adversary.budget_state.remaining(&adversary.budget) == 0 {
        return false;
    }
    match adversary.budget.mode {
        AdversaryBudgetMode::Activation => true,
        AdversaryBudgetMode::Independent { probability } => rng.should_trigger(probability),
        AdversaryBudgetMode::Windowed {
            window_ticks,
            max_per_window,
        } => {
            let width = window_ticks.max(1);
            let window = tick / width;
            if adversary.budget_state.current_window != Some(window) {
                adversary.budget_state.current_window = Some(window);
                adversary.budget_state.consumed_in_window = 0;
            }
            adversary.budget_state.consumed_in_window < max_per_window
        }
        AdversaryBudgetMode::Correlated {
            probability,
            burst_ticks,
        } => {
            if let Some(expiry) = adversary.budget_state.burst_expires_at {
                if tick < expiry {
                    return true;
                }
            }
            if rng.should_trigger(probability) {
                adversary.budget_state.burst_expires_at =
                    Some(tick.saturating_add(burst_ticks.max(1)));
                return true;
            }
            false
        }
    }
}

fn consume_budget(
    adversary_id: &str,
    budget: &AdversaryBudget,
    budget_state: &mut BudgetState,
    tick: u64,
    detail: &str,
    budget_history: &mut Vec<AdversaryBudgetRecord>,
    assumption_diagnostics: &mut Vec<AssumptionDiagnostic>,
) -> bool {
    if budget_state.remaining(budget) == 0 {
        return false;
    }
    if let AdversaryBudgetMode::Windowed { max_per_window, .. } = budget.mode {
        if budget_state.consumed_in_window >= max_per_window {
            return false;
        }
        budget_state.consumed_in_window = budget_state.consumed_in_window.saturating_add(1);
    }

    budget_state.total_consumed = budget_state.total_consumed.saturating_add(1);
    let remaining = budget_state.remaining(budget);
    budget_history.push(AdversaryBudgetRecord {
        tick,
        adversary_id: adversary_id.to_string(),
        kind: AdversaryBudgetRecordKind::Consumed,
        total_consumed: budget_state.total_consumed,
        total_remaining: remaining,
        detail: detail.to_string(),
    });
    if remaining == 0 {
        budget_history.push(AdversaryBudgetRecord {
            tick,
            adversary_id: adversary_id.to_string(),
            kind: AdversaryBudgetRecordKind::Exhausted,
            total_consumed: budget_state.total_consumed,
            total_remaining: 0,
            detail: "budget exhausted".to_string(),
        });
        assumption_diagnostics.push(AssumptionDiagnostic {
            tick,
            class: AssumptionFailureClass::BudgetExhaustion,
            adversary_id: Some(adversary_id.to_string()),
            detail: format!("budget exhausted for adversary '{adversary_id}'"),
        });
        if budget.assumption_failure != AssumptionFailureClass::BudgetExhaustion {
            assumption_diagnostics.push(AssumptionDiagnostic {
                tick,
                class: budget.assumption_failure,
                adversary_id: Some(adversary_id.to_string()),
                detail: format!(
                    "budget exhaustion violates declared assumption clause {:?}",
                    budget.assumption_failure
                ),
            });
        }
    }
    true
}

fn trigger_fires(
    trigger: &Trigger,
    tick: u64,
    logical_step: u64,
    events: &[ObsEvent],
    rng: &mut SimRng,
) -> bool {
    match trigger {
        Trigger::Immediate => true,
        Trigger::AtTick(t) => tick >= *t,
        Trigger::AfterStep(n) => logical_step >= *n,
        Trigger::Random(p) => rng.should_trigger(*p),
        Trigger::OnEvent { kind, role } => {
            let kind = kind.to_lowercase();
            events
                .iter()
                .any(|event| event_matches(event, &kind, role.as_deref()))
        }
    }
}

fn event_matches(event: &ObsEvent, kind: &str, role: Option<&str>) -> bool {
    match event {
        ObsEvent::Sent { from, to, .. } => {
            if kind != "sent" {
                return false;
            }
            role.map_or(true, |r| r == from || r == to)
        }
        ObsEvent::Received { from, to, .. } => {
            if kind != "received" {
                return false;
            }
            role.map_or(true, |r| r == from || r == to)
        }
        ObsEvent::Opened { .. } => kind == "opened" && role.is_none(),
        ObsEvent::Closed { .. } => kind == "closed" && role.is_none(),
        ObsEvent::Invoked { role: r, .. } => {
            if kind != "invoked" {
                return false;
            }
            role.map_or(true, |rr| rr == r)
        }
        ObsEvent::Halted { .. } => kind == "halted" && role.is_none(),
        ObsEvent::Faulted { .. } => kind == "faulted" && role.is_none(),
        _ => false,
    }
}

// RECURSION_SAFE: recurses only through finite product value nesting.
fn corrupt_value(val: Value) -> Value {
    match val {
        Value::Unit => Value::Unit,
        Value::Nat(n) => Value::Nat(n.wrapping_add(1)),
        Value::Bool(b) => Value::Bool(!b),
        Value::Str(s) => {
            if let Some(v) = try_decode_fixed(&Value::Str(s.clone())) {
                return fixed_to_value(-v);
            }
            if let Some(mut vals) = try_decode_fixed_vec(&Value::Str(s.clone())) {
                if let Some(first) = vals.first_mut() {
                    *first = -*first;
                }
                return fixed_vec_to_value(&vals);
            }
            Value::Str(format!("corrupt:{s}"))
        }
        Value::Prod(a, b) => Value::Prod(Box::new(corrupt_value(*a)), b),
        Value::Endpoint(_) => val,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn after_step_trigger_uses_logical_step_not_tick() {
        let trigger = Trigger::AfterStep(3);
        assert!(!trigger_fires(&trigger, 10, 2, &[], &mut SimRng::new(1),));
        assert!(trigger_fires(&trigger, 1, 3, &[], &mut SimRng::new(1),));
    }

    #[test]
    fn windowed_budget_exhaustion_emits_assumption_diagnostic() {
        let budget = AdversaryBudget {
            total: 2,
            assumption_failure: AssumptionFailureClass::FairnessFailure,
            mode: AdversaryBudgetMode::Windowed {
                window_ticks: 4,
                max_per_window: 2,
            },
        };
        let mut state = BudgetState::default();
        let mut history = Vec::new();
        let mut diagnostics = Vec::new();

        assert!(consume_budget(
            "adv",
            &budget,
            &mut state,
            1,
            "first",
            &mut history,
            &mut diagnostics,
        ));
        assert!(consume_budget(
            "adv",
            &budget,
            &mut state,
            1,
            "second",
            &mut history,
            &mut diagnostics,
        ));
        assert_eq!(
            diagnostics
                .iter()
                .filter(|entry| entry.class == AssumptionFailureClass::BudgetExhaustion)
                .count(),
            1
        );
        assert!(diagnostics
            .iter()
            .any(|entry| entry.class == AssumptionFailureClass::FairnessFailure));
    }
}
