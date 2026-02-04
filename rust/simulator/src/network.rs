//! Network simulation middleware.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Duration;

use telltale_vm::buffer::EnqueueResult;
use telltale_vm::coroutine::Value;
use telltale_vm::effect::{EffectHandler, SendDecision};
use telltale_vm::session::SessionId;

use crate::rng::SimRng;

/// Network simulation configuration.
#[derive(Debug, Clone)]
pub struct NetworkConfig {
    /// Base message latency.
    pub base_latency: Duration,
    /// Relative variance for latency sampling.
    pub latency_variance: f64,
    /// Probability of dropping each message.
    pub loss_probability: f64,
    /// Network partition definitions.
    pub partitions: Vec<Partition>,
}

impl Default for NetworkConfig {
    fn default() -> Self {
        Self {
            base_latency: Duration::from_millis(0),
            latency_variance: 0.0,
            loss_probability: 0.0,
            partitions: Vec::new(),
        }
    }
}

/// Network partition definition.
#[derive(Debug, Clone)]
pub struct Partition {
    /// Groups of roles that can communicate within but not across.
    pub groups: Vec<Vec<String>>,
    /// Tick when the partition becomes active.
    pub start_tick: u64,
    /// Tick when the partition heals.
    pub end_tick: u64,
}

#[derive(Debug, Clone)]
struct InFlightMessage {
    delivery_tick: u64,
    sid: SessionId,
    from: String,
    to: String,
    value: Value,
}

/// Network simulation middleware. Wraps an inner EffectHandler and
/// intercepts sends to model latency, loss, and partitions.
pub struct NetworkModel<H: EffectHandler> {
    inner: H,
    config: NetworkConfig,
    rng: Mutex<SimRng>,
    in_flight: Mutex<Vec<InFlightMessage>>,
    current_tick: AtomicU64,
    tick_duration: Duration,
}

impl<H: EffectHandler> NetworkModel<H> {
    /// Creates a new network model wrapping an inner handler.
    #[must_use]
    pub fn new(inner: H, config: NetworkConfig, rng: SimRng, tick_duration: Duration) -> Self {
        Self {
            inner,
            config,
            rng: Mutex::new(rng),
            in_flight: Mutex::new(Vec::new()),
            current_tick: AtomicU64::new(0),
            tick_duration,
        }
    }

    /// Update the logical tick (VM global tick, called by the runner).
    pub fn set_tick(&self, tick: u64) {
        self.current_tick.store(tick, Ordering::Relaxed);
    }

    /// Access the inner handler.
    #[must_use]
    pub fn inner(&self) -> &H {
        &self.inner
    }

    /// Access the inner handler mutably.
    pub fn inner_mut(&mut self) -> &mut H {
        &mut self.inner
    }

    /// Deliver any in-flight messages whose delivery time has arrived.
    pub fn deliver<F>(&self, tick: u64, mut inject: F)
    where
        F: FnMut(SessionId, &str, &str, Value) -> Result<EnqueueResult, String>,
    {
        let mut pending = Vec::new();
        let mut deliver_now = Vec::new();

        {
            let mut in_flight = self.in_flight.lock().expect("network lock poisoned");
            for msg in in_flight.drain(..) {
                if msg.delivery_tick <= tick {
                    deliver_now.push(msg);
                } else {
                    pending.push(msg);
                }
            }
            *in_flight = pending;
        }

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
                Err(_) => {
                    // Session missing or injection failed; drop.
                }
            }
        }

        if !retry.is_empty() {
            let mut in_flight = self.in_flight.lock().expect("network lock poisoned");
            in_flight.extend(retry);
        }
    }

    fn latency_ticks(&self, latency: Duration) -> u64 {
        let tick_secs = self.tick_duration.as_secs_f64();
        if tick_secs <= 0.0 {
            return 0;
        }
        let ticks = latency.as_secs_f64() / tick_secs;
        if ticks.is_finite() {
            ticks.round().max(0.0) as u64
        } else {
            0
        }
    }

    fn is_partitioned(&self, from: &str, to: &str, tick: u64) -> bool {
        for partition in &self.config.partitions {
            if tick < partition.start_tick || tick > partition.end_tick {
                continue;
            }
            let mut from_group = None;
            let mut to_group = None;
            for (idx, group) in partition.groups.iter().enumerate() {
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
        false
    }
}

impl<H: EffectHandler> EffectHandler for NetworkModel<H> {
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

        let tick = self.current_tick.load(Ordering::Relaxed);
        if self.is_partitioned(role, partner, tick) {
            return Ok(SendDecision::Drop);
        }

        let delay_ticks = {
            let mut rng = self.rng.lock().expect("network rng lock poisoned");
            if rng.should_trigger(self.config.loss_probability) {
                return Ok(SendDecision::Drop);
            }
            let latency =
                rng.sample_duration(self.config.base_latency, self.config.latency_variance);
            self.latency_ticks(latency)
        };

        if delay_ticks == 0 {
            return Ok(SendDecision::Deliver(payload));
        }

        let delivery_tick = tick.saturating_add(delay_ticks);
        let mut in_flight = self.in_flight.lock().expect("network lock poisoned");
        in_flight.push(InFlightMessage {
            delivery_tick,
            sid,
            from: role.to_string(),
            to: partner.to_string(),
            value: payload,
        });

        Ok(SendDecision::Defer)
    }

    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> Result<(), String> {
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
        self.inner.step(role, state)
    }
}
