//! Continuum field effect handler (two-site discretization).
//!
//! Implements diffusion dynamics between two sites connected by a kernel K.
//! The nonlocal operator at each site: drift = K * (field_peer - field_self).
//! Integration uses Euler stepping.
//!
//! Protocol: same 2-role send/recv structure as Ising (exchange field values).
//! State vector per role: `[field_value]`.

use std::cell::RefCell;
use std::collections::HashMap;

use serde_json::Value;

use crate::material::ContinuumFieldParams;
use crate::scheduler::EffectHandler;

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
    peer_fields: RefCell<HashMap<String, f64>>,
    /// Tick counter per role (2-tick cycle: send then recv).
    tick_count: RefCell<HashMap<String, usize>>,
}

impl ContinuumFieldHandler {
    /// Create a new continuum field handler.
    #[must_use]
    pub fn new(params: ContinuumFieldParams) -> Self {
        Self {
            params,
            peer_fields: RefCell::new(HashMap::new()),
            tick_count: RefCell::new(HashMap::new()),
        }
    }
}

impl EffectHandler for ContinuumFieldHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        state: &[f64],
    ) -> Result<Value, String> {
        if state.is_empty() {
            return Err("continuum field expects at least 1 field component".into());
        }
        serde_json::to_value(state[0]).map_err(|e| e.to_string())
    }

    fn handle_recv(
        &self,
        role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<f64>,
        payload: &Value,
    ) -> Result<(), String> {
        let val: f64 = serde_json::from_value(payload.clone()).map_err(|e| e.to_string())?;
        self.peer_fields
            .borrow_mut()
            .insert(role.to_string(), val);
        Ok(())
    }

    fn step(&self, role: &str, state: &mut Vec<f64>) -> Result<(), String> {
        if state.is_empty() {
            return Err("continuum field expects at least 1 field component".into());
        }

        let mut ticks = self.tick_count.borrow_mut();
        let tick = ticks.entry(role.to_string()).or_insert(0);
        let phase = *tick % 2;
        *tick += 1;

        // Only integrate on tick 1 (after recv, when peer field is available).
        if phase != 1 {
            return Ok(());
        }

        let peer_field = self
            .peer_fields
            .borrow()
            .get(role)
            .copied()
            .unwrap_or(state[0]);

        let dt = self.params.step_size;
        let k = self.params.coupling;

        // Diffusion drift: K * (peer - self).
        let drift = k * (peer_field - state[0]);
        state[0] += drift * dt;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::material::ContinuumFieldParams;

    fn test_params() -> ContinuumFieldParams {
        ContinuumFieldParams {
            coupling: 1.0,
            components: 1,
            initial_fields: vec![1.0, 0.0],
            step_size: 0.01,
        }
    }

    #[test]
    fn test_diffusion_conserves_total_field() {
        let handler = ContinuumFieldHandler::new(test_params());

        let mut state_a = vec![1.0];
        let mut state_b = vec![0.0];
        let initial_total = state_a[0] + state_b[0];

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

        let final_total = state_a[0] + state_b[0];
        assert!(
            (final_total - initial_total).abs() < 1e-10,
            "total field should be conserved: initial={initial_total}, final={final_total}"
        );
    }

    #[test]
    fn test_diffusion_converges_to_equilibrium() {
        let handler = ContinuumFieldHandler::new(test_params());

        let mut state_a = vec![1.0];
        let mut state_b = vec![0.0];

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
        assert!(
            (state_a[0] - 0.5).abs() < 1e-4,
            "A should converge to 0.5, got {}",
            state_a[0]
        );
        assert!(
            (state_b[0] - 0.5).abs() < 1e-4,
            "B should converge to 0.5, got {}",
            state_b[0]
        );
    }
}
