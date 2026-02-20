//! Network simulation middleware.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Duration;
use telltale_types::FixedQ32;

use telltale_vm::buffer::EnqueueResult;
use telltale_vm::coroutine::Value;
use telltale_vm::effect::{EffectHandler, SendDecision, SendDecisionInput};
use telltale_vm::session::SessionId;

use crate::rng::SimRng;

/// Network simulation configuration.
#[derive(Debug, Clone)]
pub struct NetworkConfig {
    /// Base message latency.
    pub base_latency: Duration,
    /// Relative variance for latency sampling.
    pub latency_variance: FixedQ32,
    /// Probability of dropping each message.
    pub loss_probability: FixedQ32,
    /// Network partition definitions.
    pub partitions: Vec<Partition>,
    /// Per-link policy overrides for role-to-role traffic.
    pub links: Vec<LinkPolicy>,
}

impl Default for NetworkConfig {
    fn default() -> Self {
        Self {
            base_latency: Duration::from_millis(0),
            latency_variance: FixedQ32::zero(),
            loss_probability: FixedQ32::zero(),
            partitions: Vec::new(),
            links: Vec::new(),
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

/// Per-link policy override for role-to-role traffic.
#[derive(Debug, Clone)]
pub struct LinkPolicy {
    /// Source role.
    pub from: String,
    /// Destination role.
    pub to: String,
    /// Tick when link policy becomes active. None means always active.
    pub start_tick: Option<u64>,
    /// Tick when link policy becomes inactive. None means no end.
    pub end_tick: Option<u64>,
    /// Whether this link is enabled while active.
    pub enabled: bool,
    /// Optional latency override for this link.
    pub base_latency: Option<Duration>,
    /// Optional latency variance override for this link.
    pub latency_variance: Option<FixedQ32>,
    /// Optional loss probability override for this link.
    pub loss_probability: Option<FixedQ32>,
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

    fn link_active(link: &LinkPolicy, tick: u64) -> bool {
        if let Some(start) = link.start_tick {
            if tick < start {
                return false;
            }
        }
        if let Some(end) = link.end_tick {
            if tick > end {
                return false;
            }
        }
        true
    }

    fn link_policy(&self, from: &str, to: &str, tick: u64) -> Option<&LinkPolicy> {
        self.config
            .links
            .iter()
            .rev()
            .find(|link| link.from == from && link.to == to && Self::link_active(link, tick))
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

    fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
        let base = self.inner.send_decision(input.clone())?;
        let sid = input.sid;
        let role = input.role;
        let partner = input.partner;

        let SendDecision::Deliver(payload) = base else {
            return Ok(base);
        };

        let tick = self.current_tick.load(Ordering::Relaxed);
        if self.is_partitioned(role, partner, tick) {
            return Ok(SendDecision::Drop);
        }

        let mut loss_probability = self.config.loss_probability;
        let mut base_latency = self.config.base_latency;
        let mut latency_variance = self.config.latency_variance;

        if let Some(link) = self.link_policy(role, partner, tick) {
            if !link.enabled {
                return Ok(SendDecision::Drop);
            }
            if let Some(override_loss) = link.loss_probability {
                loss_probability = override_loss;
            }
            if let Some(override_latency) = link.base_latency {
                base_latency = override_latency;
            }
            if let Some(override_variance) = link.latency_variance {
                latency_variance = override_variance;
            }
        }

        let delay_ticks = {
            let mut rng = self.rng.lock().expect("network rng lock poisoned");
            if rng.should_trigger(loss_probability) {
                return Ok(SendDecision::Drop);
            }
            let latency = rng.sample_duration(base_latency, latency_variance);
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

#[cfg(test)]
mod tests {
    use super::*;

    struct PassthroughHandler;

    impl EffectHandler for PassthroughHandler {
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

    fn model(config: NetworkConfig) -> NetworkModel<PassthroughHandler> {
        NetworkModel::new(
            PassthroughHandler,
            config,
            SimRng::new(7),
            Duration::from_millis(1),
        )
    }

    #[test]
    fn link_disabled_drops_message() {
        let config = NetworkConfig {
            links: vec![LinkPolicy {
                from: "A".to_string(),
                to: "B".to_string(),
                start_tick: None,
                end_tick: None,
                enabled: false,
                base_latency: None,
                latency_variance: None,
                loss_probability: None,
            }],
            ..NetworkConfig::default()
        };
        let model = model(config);
        model.set_tick(0);
        let decision = model
            .send_decision(SendDecisionInput {
                sid: 0,
                role: "A",
                partner: "B",
                label: "msg",
                state: &[],
                payload: Some(Value::Nat(1)),
            })
            .expect("send decision");
        assert!(matches!(decision, SendDecision::Drop));
    }

    #[test]
    fn link_window_inactive_uses_global_policy() {
        let config = NetworkConfig {
            links: vec![LinkPolicy {
                from: "A".to_string(),
                to: "B".to_string(),
                start_tick: Some(10),
                end_tick: Some(20),
                enabled: false,
                base_latency: None,
                latency_variance: None,
                loss_probability: None,
            }],
            ..NetworkConfig::default()
        };
        let model = model(config);
        model.set_tick(5);
        let decision = model
            .send_decision(SendDecisionInput {
                sid: 0,
                role: "A",
                partner: "B",
                label: "msg",
                state: &[],
                payload: Some(Value::Nat(1)),
            })
            .expect("send decision");
        assert!(matches!(decision, SendDecision::Deliver(Value::Nat(1))));
    }

    #[test]
    fn link_latency_override_defers_delivery() {
        let config = NetworkConfig {
            links: vec![LinkPolicy {
                from: "A".to_string(),
                to: "B".to_string(),
                start_tick: None,
                end_tick: None,
                enabled: true,
                base_latency: Some(Duration::from_millis(10)),
                latency_variance: Some(FixedQ32::zero()),
                loss_probability: Some(FixedQ32::zero()),
            }],
            ..NetworkConfig::default()
        };
        let model = model(config);
        model.set_tick(3);
        let decision = model
            .send_decision(SendDecisionInput {
                sid: 0,
                role: "A",
                partner: "B",
                label: "msg",
                state: &[],
                payload: Some(Value::Nat(1)),
            })
            .expect("send decision");
        assert!(matches!(decision, SendDecision::Defer));
    }

    #[test]
    fn link_loss_override_applies() {
        let config = NetworkConfig {
            links: vec![LinkPolicy {
                from: "A".to_string(),
                to: "B".to_string(),
                start_tick: None,
                end_tick: None,
                enabled: true,
                base_latency: None,
                latency_variance: None,
                loss_probability: Some(FixedQ32::one()),
            }],
            ..NetworkConfig::default()
        };
        let model = model(config);
        model.set_tick(0);
        let decision = model
            .send_decision(SendDecisionInput {
                sid: 0,
                role: "A",
                partner: "B",
                label: "msg",
                state: &[],
                payload: Some(Value::Nat(1)),
            })
            .expect("send decision");
        assert!(matches!(decision, SendDecision::Drop));
    }
}
