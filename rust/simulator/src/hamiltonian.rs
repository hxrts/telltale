//! Hamiltonian 2-body effect handler.
//!
//! Implements leapfrog (Störmer-Verlet) integration for a 2-body system
//! with harmonic coupling potential V = k/2 * (q_A - q_B)^2.
//!
//! State vector per role: [position, momentum].
//! The protocol exchanges positions and forces between roles in a 4-step
//! cycle: A→B:pos, B→A:pos, A→B:force, B→A:force. Integration happens
//! once per full cycle (every 4 scheduler ticks).

use std::cell::RefCell;
use std::collections::HashMap;

use serde_json::Value;

use crate::material::HamiltonianParams;
use crate::scheduler::EffectHandler;

/// Effect handler for Hamiltonian 2-body dynamics.
///
/// Uses leapfrog integration: half-kick, drift, half-kick.
/// The protocol cycle is:
///   tick 0: exchange positions
///   tick 1: exchange positions (reverse)
///   tick 2: exchange forces
///   tick 3: exchange forces (reverse)
/// Integration happens at tick 3 (after all forces received).
pub struct HamiltonianHandler {
    params: HamiltonianParams,
    /// Per-role: received peer position.
    peer_positions: RefCell<HashMap<String, f64>>,
    /// Per-role: received peer force.
    peer_forces: RefCell<HashMap<String, f64>>,
    /// Tick counter per role to track protocol phase.
    tick_count: RefCell<HashMap<String, usize>>,
}

impl HamiltonianHandler {
    /// Create a new Hamiltonian handler from material parameters.
    #[must_use]
    pub fn new(params: HamiltonianParams) -> Self {
        Self {
            params,
            peer_positions: RefCell::new(HashMap::new()),
            peer_forces: RefCell::new(HashMap::new()),
            tick_count: RefCell::new(HashMap::new()),
        }
    }

    /// Compute force on a role given its position and its peer's position.
    ///
    /// For harmonic potential V = k/2 * (q_A - q_B)^2:
    ///   F = -dV/dq = -k * (q_self - q_peer)
    fn force(&self, my_position: f64, peer_position: f64) -> f64 {
        -self.params.spring_constant * (my_position - peer_position)
    }
}

impl EffectHandler for HamiltonianHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        state: &[f64],
    ) -> Result<Value, String> {
        match label {
            "position" => serde_json::to_value(state[0]).map_err(|e| e.to_string()),
            "force" => {
                let peer_pos = self
                    .peer_positions
                    .borrow()
                    .get(_role)
                    .copied()
                    .unwrap_or(0.0);
                let f = self.force(state[0], peer_pos);
                serde_json::to_value(f).map_err(|e| e.to_string())
            }
            other => Err(format!("unknown label: {other}")),
        }
    }

    fn handle_recv(
        &self,
        role: &str,
        _partner: &str,
        label: &str,
        _state: &mut Vec<f64>,
        payload: &Value,
    ) -> Result<(), String> {
        let val: f64 =
            serde_json::from_value(payload.clone()).map_err(|e| e.to_string())?;
        match label {
            "position" => {
                self.peer_positions
                    .borrow_mut()
                    .insert(role.to_string(), val);
            }
            "force" => {
                self.peer_forces
                    .borrow_mut()
                    .insert(role.to_string(), val);
            }
            other => return Err(format!("unknown label: {other}")),
        }
        Ok(())
    }

    fn step(&self, role: &str, state: &mut Vec<f64>) -> Result<(), String> {
        if state.len() != 2 {
            return Err(format!(
                "Hamiltonian expects [position, momentum], got {} elements",
                state.len()
            ));
        }

        let mut ticks = self.tick_count.borrow_mut();
        let tick = ticks.entry(role.to_string()).or_insert(0);
        let phase = *tick % 4;
        *tick += 1;

        // Only integrate on tick 3 (after force exchange complete).
        if phase != 3 {
            return Ok(());
        }

        let dt = self.params.step_size;
        let mass = self.params.mass;

        // Get the received force from peer.
        let received_force = self
            .peer_forces
            .borrow()
            .get(role)
            .copied()
            .unwrap_or(0.0);

        // Get peer position for own force computation.
        let peer_pos = self
            .peer_positions
            .borrow()
            .get(role)
            .copied()
            .unwrap_or(0.0);

        // Use own force computation (from received peer position).
        // The received_force is the peer's force on itself, not on us.
        let _ = received_force;
        let force = self.force(state[0], peer_pos);

        // Leapfrog integration:
        // 1. Half-kick: p += F * dt/2
        state[1] += force * dt / 2.0;
        // 2. Drift: q += p/m * dt
        state[0] += state[1] / mass * dt;
        // 3. Half-kick with new force: p += F(new_q) * dt/2
        let peer_pos_for_new = peer_pos; // peer position hasn't changed this tick
        let new_force = self.force(state[0], peer_pos_for_new);
        state[1] += new_force * dt / 2.0;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::material::HamiltonianParams;

    fn test_params() -> HamiltonianParams {
        HamiltonianParams {
            spring_constant: 1.0,
            mass: 1.0,
            dimensions: 1,
            initial_positions: vec![1.0, -1.0],
            initial_momenta: vec![0.0, 0.0],
            step_size: 0.01,
        }
    }

    #[test]
    fn test_force_harmonic() {
        let handler = HamiltonianHandler::new(test_params());
        // F = -k * (q_A - q_B) = -1.0 * (1.0 - (-1.0)) = -2.0
        let f = handler.force(1.0, -1.0);
        assert!((f - (-2.0)).abs() < 1e-10);
    }

    #[test]
    fn test_leapfrog_preserves_energy_approx() {
        let params = test_params();
        let handler = HamiltonianHandler::new(params.clone());

        // Set up peer position for role A
        handler
            .peer_positions
            .borrow_mut()
            .insert("A".to_string(), -1.0);
        handler
            .peer_forces
            .borrow_mut()
            .insert("A".to_string(), 0.0);

        let mut state_a = vec![1.0, 0.0];
        let peer_pos = -1.0_f64;

        let ke = |s: &[f64]| -> f64 { s[1] * s[1] / (2.0 * params.mass) };
        let pe = |s: &[f64]| -> f64 {
            params.spring_constant / 2.0 * (s[0] - peer_pos) * (s[0] - peer_pos)
        };
        let initial_energy = ke(&state_a) + pe(&state_a);

        // Simulate 100 integration steps (each needs 4 ticks)
        for _ in 0..400 {
            handler.step("A", &mut state_a).unwrap();
        }

        let final_energy = ke(&state_a) + pe(&state_a);

        let relative_error = (final_energy - initial_energy).abs() / initial_energy;
        assert!(
            relative_error < 0.01,
            "energy drift too large: initial={initial_energy}, final={final_energy}, relative_error={relative_error}"
        );
    }
}
