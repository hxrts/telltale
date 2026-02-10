//! Fault injection middleware for simulation.

use std::collections::BTreeSet;
use std::sync::Mutex;
use telltale_types::FixedQ32;

use serde_json::Value as JsonValue;
use telltale_vm::buffer::EnqueueResult;
use telltale_vm::coroutine::Value;
use telltale_vm::effect::{EffectHandler, SendDecision};
use telltale_vm::session::SessionId;
use telltale_vm::vm::ObsEvent;

use crate::rng::SimRng;

/// Fault types that can be injected during simulation.
#[derive(Debug, Clone)]
pub enum Fault {
    /// Drop messages with given probability.
    MessageDrop {
        /// Probability of dropping each message (0.0 to 1.0).
        probability: FixedQ32,
    },
    /// Delay messages by N ticks.
    MessageDelay {
        /// Number of ticks to delay message delivery.
        ticks: usize,
    },
    /// Corrupt message payload with given probability.
    MessageCorruption {
        /// Probability of corrupting each message (0.0 to 1.0).
        probability: FixedQ32,
    },
    /// Crash a role (stop executing its coroutines) for optional duration.
    NodeCrash {
        /// The role to crash.
        role: String,
        /// Duration in ticks before recovery. None means permanent.
        duration: Option<usize>,
    },
    /// Partition roles into disconnected groups.
    NetworkPartition {
        /// Groups of roles that can communicate within but not across.
        groups: Vec<Vec<String>>,
        /// Duration in ticks before partition heals.
        duration: usize,
    },
}

/// When to activate a fault.
#[derive(Debug, Clone)]
pub enum Trigger {
    /// Activate immediately when the fault is scheduled.
    Immediate,
    /// Activate at a specific simulation tick.
    AtTick(u64),
    /// Activate after a specific number of steps.
    AfterStep(u64),
    /// Activate randomly with the given probability each tick.
    Random(FixedQ32),
    /// Activate when a specific event occurs.
    OnEvent {
        /// The event kind to match (e.g., "sent", "received").
        kind: String,
        /// Optional role filter for the event.
        role: Option<String>,
    },
}

/// A fault with its activation trigger and optional duration.
#[derive(Debug, Clone)]
pub struct ScheduledFault {
    /// The fault to inject.
    pub fault: Fault,
    /// When to activate the fault.
    pub trigger: Trigger,
    /// Optional duration in ticks. Overrides fault-specific duration.
    pub duration: Option<usize>,
}

/// A collection of scheduled faults with concurrency limits.
#[derive(Debug, Clone)]
pub struct FaultSchedule {
    /// The list of faults to schedule.
    pub faults: Vec<ScheduledFault>,
    /// Maximum number of faults active simultaneously.
    pub max_concurrent: usize,
}

impl Default for FaultSchedule {
    fn default() -> Self {
        Self {
            faults: Vec::new(),
            max_concurrent: usize::MAX,
        }
    }
}

#[derive(Debug, Clone)]
struct ActiveFault {
    fault: Fault,
    expires_at: Option<u64>,
}

#[derive(Debug, Clone)]
struct ScheduledFaultState {
    fault: Fault,
    trigger: Trigger,
    duration: Option<usize>,
    activated: bool,
}

#[derive(Debug, Clone)]
struct InFlightMessage {
    delivery_tick: u64,
    sid: SessionId,
    from: String,
    to: String,
    value: Value,
}

struct FaultState {
    scheduled: Vec<ScheduledFaultState>,
    active: Vec<ActiveFault>,
    rng: SimRng,
    in_flight: Vec<InFlightMessage>,
    current_tick: u64,
    last_trace_len: usize,
    crashed_roles: BTreeSet<String>,
}

impl FaultState {
    fn refresh_crashed_roles(&mut self) {
        let mut crashed = BTreeSet::new();
        for fault in &self.active {
            if let Fault::NodeCrash { role, .. } = &fault.fault {
                crashed.insert(role.clone());
            }
        }
        self.crashed_roles = crashed;
    }

    fn is_crashed(&self, role: &str) -> bool {
        self.crashed_roles.contains(role)
    }

    fn message_drop_probability(&self) -> FixedQ32 {
        let one = FixedQ32::one();
        let zero = FixedQ32::zero();
        let mut p_not = one;
        for fault in &self.active {
            if let Fault::MessageDrop { probability } = &fault.fault {
                p_not = p_not * (one - (*probability).clamp(zero, one));
            }
        }
        one - p_not
    }

    fn message_delay_ticks(&self) -> Option<usize> {
        let mut delay: Option<usize> = None;
        for fault in &self.active {
            if let Fault::MessageDelay { ticks } = &fault.fault {
                delay = Some(delay.map_or(*ticks, |d| d.max(*ticks)));
            }
        }
        delay
    }

    fn message_corruption_probability(&self) -> FixedQ32 {
        let one = FixedQ32::one();
        let zero = FixedQ32::zero();
        let mut p_not = one;
        for fault in &self.active {
            if let Fault::MessageCorruption { probability } = &fault.fault {
                p_not = p_not * (one - (*probability).clamp(zero, one));
            }
        }
        one - p_not
    }

    fn partitioned(&self, from: &str, to: &str) -> bool {
        for fault in &self.active {
            if let Fault::NetworkPartition { groups, .. } = &fault.fault {
                let mut from_group = None;
                let mut to_group = None;
                for (idx, group) in groups.iter().enumerate() {
                    if group.iter().any(|r| r == from) {
                        from_group = Some(idx);
                    }
                    if group.iter().any(|r| r == to) {
                        to_group = Some(idx);
                    }
                }
                if from_group != to_group {
                    return true;
                }
            }
        }
        false
    }
}

/// Runtime fault state. Manages active faults, expiration, RNG.
pub struct FaultInjector<H: EffectHandler> {
    inner: H,
    state: Mutex<FaultState>,
    max_concurrent: usize,
}

impl<H: EffectHandler> FaultInjector<H> {
    /// Creates a new fault injector wrapping an inner handler.
    #[must_use]
    pub fn new(inner: H, schedule: FaultSchedule, rng: SimRng) -> Self {
        let scheduled = schedule
            .faults
            .into_iter()
            .map(|f| ScheduledFaultState {
                fault: f.fault,
                trigger: f.trigger,
                duration: f.duration,
                activated: false,
            })
            .collect();
        Self {
            inner,
            state: Mutex::new(FaultState {
                scheduled,
                active: Vec::new(),
                rng,
                in_flight: Vec::new(),
                current_tick: 0,
                last_trace_len: 0,
                crashed_roles: BTreeSet::new(),
            }),
            max_concurrent: schedule.max_concurrent.max(1),
        }
    }

    /// Advance fault schedule, activating and expiring faults.
    /// Uses the VM's global tick (not session-local normalization).
    pub fn tick(&self, tick: u64, trace: &[ObsEvent]) {
        let mut state = self.state.lock().expect("fault state lock poisoned");
        state.current_tick = tick;

        let new_events = trace.get(state.last_trace_len..).unwrap_or(&[]);

        // Expire active faults.
        state.active.retain(|fault| match fault.expires_at {
            Some(exp) => tick < exp,
            None => true,
        });

        // Activate scheduled faults.
        let FaultState {
            scheduled,
            active,
            rng,
            ..
        } = &mut *state;
        for scheduled in scheduled.iter_mut() {
            if scheduled.activated {
                continue;
            }
            if active.len() >= self.max_concurrent {
                break;
            }
            if trigger_fires(&scheduled.trigger, tick, new_events, rng) {
                let expires_at = fault_expiry(tick, &scheduled.fault, scheduled.duration);
                active.push(ActiveFault {
                    fault: scheduled.fault.clone(),
                    expires_at,
                });
                scheduled.activated = true;
            }
        }

        state.refresh_crashed_roles();
        state.last_trace_len = trace.len();
    }

    /// Deliver any delayed messages whose time has arrived.
    pub fn deliver<F>(&self, tick: u64, mut inject: F)
    where
        F: FnMut(SessionId, &str, &str, Value) -> Result<EnqueueResult, String>,
    {
        let mut state = self.state.lock().expect("fault state lock poisoned");
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
                delivery_tick: _,
                sid,
                from,
                to,
                value,
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
                Err(_) => {}
            }
        }
        state.in_flight.extend(retry);
    }

    /// Current crashed roles (for pausing VM execution).
    #[must_use]
    pub fn crashed_roles(&self) -> BTreeSet<String> {
        let state = self.state.lock().expect("fault state lock poisoned");
        state.crashed_roles.clone()
    }
}

impl<H: EffectHandler> EffectHandler for FaultInjector<H> {
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> Result<Value, String> {
        self.inner.handle_send(role, partner, label, state)
    }

    fn send_decision(
        &self,
        sid: SessionId,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
        payload: Option<Value>,
    ) -> Result<SendDecision, String> {
        let base = self
            .inner
            .send_decision(sid, role, partner, label, state, payload)?;

        let SendDecision::Deliver(payload) = base else {
            return Ok(base);
        };

        let mut state = self.state.lock().expect("fault state lock poisoned");
        if state.is_crashed(role) {
            return Err("node crashed".into());
        }
        if state.partitioned(role, partner) {
            return Ok(SendDecision::Drop);
        }
        let drop_p = state.message_drop_probability();
        let zero = FixedQ32::zero();
        if drop_p > zero && state.rng.should_trigger(drop_p) {
            return Ok(SendDecision::Drop);
        }

        let mut payload = payload;
        let corrupt_p = state.message_corruption_probability();
        if corrupt_p > zero && state.rng.should_trigger(corrupt_p) {
            payload = corrupt_value(payload);
        }

        if let Some(delay) = state.message_delay_ticks() {
            let delivery_tick = state.current_tick.saturating_add(delay as u64);
            state.in_flight.push(InFlightMessage {
                delivery_tick,
                sid,
                from: role.to_string(),
                to: partner.to_string(),
                value: payload,
            });
            return Ok(SendDecision::Defer);
        }

        Ok(SendDecision::Deliver(payload))
    }

    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> Result<(), String> {
        if self
            .state
            .lock()
            .expect("fault state lock poisoned")
            .is_crashed(role)
        {
            return Err("node crashed".into());
        }
        self.inner.handle_recv(role, partner, label, state, payload)
    }

    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[Value],
    ) -> Result<String, String> {
        self.inner.handle_choose(role, partner, labels, state)
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> Result<(), String> {
        if self
            .state
            .lock()
            .expect("fault state lock poisoned")
            .is_crashed(role)
        {
            return Err("node crashed".into());
        }
        self.inner.step(role, state)
    }
}

fn trigger_fires(trigger: &Trigger, tick: u64, events: &[ObsEvent], rng: &mut SimRng) -> bool {
    match trigger {
        Trigger::Immediate => true,
        Trigger::AtTick(t) => tick >= *t,
        Trigger::AfterStep(n) => tick >= *n,
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

fn fault_expiry(tick: u64, fault: &Fault, scheduled: Option<usize>) -> Option<u64> {
    let duration = match fault {
        Fault::NodeCrash { duration, .. } => duration.or(scheduled),
        Fault::NetworkPartition { duration, .. } => Some(*duration),
        _ => scheduled,
    };
    duration.map(|d| tick.saturating_add(d as u64))
}

fn corrupt_value(val: Value) -> Value {
    match val {
        Value::Bool(b) => Value::Bool(!b),
        Value::Int(i) => Value::Int(-i),
        Value::Real(r) => Value::Real(-r),
        Value::Str(s) => Value::Str(format!("corrupt:{s}")),
        Value::Vec(mut v) => {
            if let Some(first) = v.first_mut() {
                *first = -*first;
            }
            Value::Vec(v)
        }
        Value::Label(l) => Value::Label(format!("corrupt_{l}")),
        Value::Json(mut j) => {
            if let Some(n) = j.as_f64() {
                j = JsonValue::from(-n);
            } else {
                j = JsonValue::String("corrupt".into());
            }
            Value::Json(j)
        }
        Value::Endpoint(_) => val,
        Value::Knowledge { .. } => val,
        Value::Unit => Value::Unit,
    }
}
