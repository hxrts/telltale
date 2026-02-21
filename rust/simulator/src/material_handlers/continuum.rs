//! Continuum field effect handler (two-site discretization).
//!
//! Implements diffusion dynamics between two sites connected by a kernel K.
//! The nonlocal operator at each site: drift = K * (field_peer - field_self).
//! Integration uses Euler stepping.
//!
//! Protocol: same 2-role send/recv structure as Ising (exchange field values).
//! State vector per role: `[field_value]`.

use std::collections::BTreeMap;
use std::sync::Mutex;
use telltale_types::FixedQ32;

use crate::material::ContinuumFieldParams;
use crate::value_conv::{fixed_to_value, registers_to_f64s, value_to_f64, write_f64s};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::EffectHandler;

/// Effect handler for two-site continuum field dynamics.
///
/// Each role holds a scalar field value. Per protocol tick:
///   1. Send own field value to peer
///   2. Receive peer's field value
///   3. Compute diffusion drift: K * (peer_field - self_field)
///   4. Euler step: field += drift * dt
///
/// Conservation property: total field (sum across sites) is preserved
/// because drift_A + drift_B = K*(f_B - f_A) + K*(f_A - f_B) = 0.
pub struct ContinuumFieldHandler {
    params: ContinuumFieldParams,
    /// Per-role: received peer field value.
    peer_fields: Mutex<BTreeMap<String, FixedQ32>>,
    /// Tick counter per role (2-tick cycle: send then recv).
    tick_count: Mutex<BTreeMap<String, usize>>,
}

impl ContinuumFieldHandler {
    /// Create a new continuum field handler.
    #[must_use]
    pub fn new(params: ContinuumFieldParams) -> Self {
        Self {
            params,
            peer_fields: Mutex::new(BTreeMap::new()),
            tick_count: Mutex::new(BTreeMap::new()),
        }
    }
}

impl EffectHandler for ContinuumFieldHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        state: &[Value],
    ) -> Result<Value, String> {
        let vals = registers_to_f64s(state);
        if vals.is_empty() {
            return Err("continuum field expects at least 1 field component".into());
        }
        Ok(fixed_to_value(vals[0]))
    }

    fn handle_recv(
        &self,
        role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        payload: &Value,
    ) -> Result<(), String> {
        let val = value_to_f64(payload)?;
        self.peer_fields
            .lock()
            .expect("continuum handler lock poisoned")
            .insert(role.to_string(), val);
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
            .ok_or_else(|| "no labels available".into())
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> Result<(), String> {
        let mut vals = registers_to_f64s(state);
        if vals.is_empty() {
            return Err("continuum field expects at least 1 field component".into());
        }

        let phase = {
            let mut ticks = self
                .tick_count
                .lock()
                .expect("continuum handler lock poisoned");
            let tick = ticks.entry(role.to_string()).or_insert(0);
            let phase = *tick % 2;
            *tick += 1;
            phase
        };

        // Only integrate on tick 1 (after recv, when peer field is available).
        if phase != 1 {
            return Ok(());
        }

        let peer_field = self
            .peer_fields
            .lock()
            .expect("continuum handler lock poisoned")
            .get(role)
            .copied()
            .unwrap_or(vals[0]);

        let dt = self.params.step_size;
        let k = self.params.coupling;

        // Diffusion drift: K * (peer - self).
        let drift = k * (peer_field - vals[0]);
        vals[0] += drift * dt;

        write_f64s(state, &vals);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::material::ContinuumFieldParams;
    use crate::value_conv::{registers_to_f64s, write_f64s};

    fn test_params() -> ContinuumFieldParams {
        ContinuumFieldParams {
            coupling: FixedQ32::one(),
            components: 1,
            initial_fields: vec![FixedQ32::one(), FixedQ32::zero()],
            step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
        }
    }

    #[test]
    fn test_diffusion_conserves_total_field() {
        let handler = ContinuumFieldHandler::new(test_params());

        let mut state_a = vec![Value::Unit, Value::Unit];
        let mut state_b = vec![Value::Unit, Value::Unit];
        write_f64s(&mut state_a, &[FixedQ32::one()]);
        write_f64s(&mut state_b, &[FixedQ32::zero()]);
        let initial_total = registers_to_f64s(&state_a)[0] + registers_to_f64s(&state_b)[0];

        for _ in 0..1000 {
            // Tick 0: A sends, B recvs.
            let payload_a = handler.handle_send("A", "B", "field", &state_a).unwrap();
            handler
                .handle_recv("B", "A", "field", &mut state_b, &payload_a)
                .unwrap();
            handler.step("A", &mut state_a).unwrap(); // tick 0 for A (no-op)
            handler.step("B", &mut state_b).unwrap(); // tick 0 for B (no-op)

            // Tick 1: B sends, A recvs.
            let payload_b = handler.handle_send("B", "A", "field", &state_b).unwrap();
            handler
                .handle_recv("A", "B", "field", &mut state_a, &payload_b)
                .unwrap();
            handler.step("A", &mut state_a).unwrap(); // tick 1 for A (integrate)
            handler.step("B", &mut state_b).unwrap(); // tick 1 for B (integrate)
        }

        let final_total = registers_to_f64s(&state_a)[0] + registers_to_f64s(&state_b)[0];
        // Allow for some fixed-point rounding error accumulation over 1000 iterations
        let eps = FixedQ32::from_ratio(1, 1_000_000).expect("epsilon");
        assert!(
            (final_total - initial_total).abs() < eps,
            "total field should be conserved: initial={initial_total}, final={final_total}"
        );
    }

    #[test]
    fn test_diffusion_converges_to_equilibrium() {
        let handler = ContinuumFieldHandler::new(test_params());

        let mut state_a = vec![Value::Unit, Value::Unit];
        let mut state_b = vec![Value::Unit, Value::Unit];
        write_f64s(&mut state_a, &[FixedQ32::one()]);
        write_f64s(&mut state_b, &[FixedQ32::zero()]);

        for _ in 0..10000 {
            // Tick 0: A→B send, B recv.
            let payload_a = handler.handle_send("A", "B", "field", &state_a).unwrap();
            handler
                .handle_recv("B", "A", "field", &mut state_b, &payload_a)
                .unwrap();
            handler.step("A", &mut state_a).unwrap();
            handler.step("B", &mut state_b).unwrap();

            // Tick 1: B→A send, A recv.
            let payload_b = handler.handle_send("B", "A", "field", &state_b).unwrap();
            handler
                .handle_recv("A", "B", "field", &mut state_a, &payload_b)
                .unwrap();
            handler.step("A", &mut state_a).unwrap();
            handler.step("B", &mut state_b).unwrap();
        }

        // Should converge to equal field values (average = 0.5).
        let vals_a = registers_to_f64s(&state_a);
        let vals_b = registers_to_f64s(&state_b);
        let half = FixedQ32::half();
        let eps = FixedQ32::from_ratio(1, 10000).expect("1e-4");
        assert!(
            (vals_a[0] - half).abs() < eps,
            "A should converge to 0.5, got {}",
            vals_a[0]
        );
        assert!(
            (vals_b[0] - half).abs() < eps,
            "B should converge to 0.5, got {}",
            vals_b[0]
        );
    }
}
