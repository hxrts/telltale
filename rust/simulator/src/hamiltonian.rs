//! Hamiltonian 2-body effect handler.
//!
//! Implements leapfrog (Störmer-Verlet) integration for a 2-body system
//! with harmonic coupling potential V = k/2 * (q_A - q_B)^2.
//!
//! State vector per role: [position, momentum].
//! The protocol exchanges positions and forces between roles in a 4-step
//! cycle: A→B:pos, B→A:pos, A→B:force, B→A:force. Integration happens
//! once per full cycle (every 4 scheduler ticks).

use std::collections::BTreeMap;
use std::sync::Mutex;
use telltale_types::FixedQ32;

use crate::material::HamiltonianParams;
use crate::value_conv::{registers_to_f64s, value_to_f64, write_f64s};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::EffectHandler;

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
    peer_positions: Mutex<BTreeMap<String, FixedQ32>>,
    /// Per-role: received peer force.
    peer_forces: Mutex<BTreeMap<String, FixedQ32>>,
    /// Tick counter per role to track protocol phase.
    tick_count: Mutex<BTreeMap<String, usize>>,
}

impl HamiltonianHandler {
    /// Create a new Hamiltonian handler from material parameters.
    #[must_use]
    pub fn new(params: HamiltonianParams) -> Self {
        Self {
            params,
            peer_positions: Mutex::new(BTreeMap::new()),
            peer_forces: Mutex::new(BTreeMap::new()),
            tick_count: Mutex::new(BTreeMap::new()),
        }
    }

    /// Compute force on a role given its position and its peer's position.
    ///
    /// For harmonic potential V = k/2 * (q_A - q_B)^2:
    ///   F = -dV/dq = -k * (q_self - q_peer)
    fn force(&self, my_position: FixedQ32, peer_position: FixedQ32) -> FixedQ32 {
        -self.params.spring_constant * (my_position - peer_position)
    }
}

impl EffectHandler for HamiltonianHandler {
    fn handle_send(
        &self,
        role: &str,
        _partner: &str,
        label: &str,
        state: &[Value],
    ) -> Result<Value, String> {
        let vals = registers_to_f64s(state);
        match label {
            "position" => vals
                .first()
                .copied()
                .map(Value::Real)
                .ok_or_else(|| "missing position state".into()),
            "force" => {
                let peer_pos = self
                    .peer_positions
                    .lock()
                    .expect("hamiltonian handler lock poisoned")
                    .get(role)
                    .copied()
                    .unwrap_or_else(FixedQ32::zero);
                let my_pos = vals.first().copied().unwrap_or_else(FixedQ32::zero);
                let f = self.force(my_pos, peer_pos);
                Ok(Value::Real(f))
            }
            other => Err(format!("unknown label: {other}")),
        }
    }

    fn handle_recv(
        &self,
        role: &str,
        _partner: &str,
        label: &str,
        _state: &mut Vec<Value>,
        payload: &Value,
    ) -> Result<(), String> {
        let val = value_to_f64(payload)?;
        match label {
            "position" => {
                self.peer_positions
                    .lock()
                    .expect("hamiltonian handler lock poisoned")
                    .insert(role.to_string(), val);
            }
            "force" => {
                self.peer_forces
                    .lock()
                    .expect("hamiltonian handler lock poisoned")
                    .insert(role.to_string(), val);
            }
            other => return Err(format!("unknown label: {other}")),
        }
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
        if vals.len() != 2 {
            return Err(format!(
                "Hamiltonian expects [position, momentum], got {} elements",
                vals.len()
            ));
        }

        let phase = {
            let mut ticks = self
                .tick_count
                .lock()
                .expect("hamiltonian handler lock poisoned");
            let tick = ticks.entry(role.to_string()).or_insert(0);
            let phase = *tick % 4;
            *tick += 1;
            phase
        };

        // Only integrate on tick 3 (after force exchange complete).
        if phase != 3 {
            return Ok(());
        }

        let dt = self.params.step_size;
        let mass = self.params.mass;

        // Get the received force from peer.
        let received_force = self
            .peer_forces
            .lock()
            .expect("hamiltonian handler lock poisoned")
            .get(role)
            .copied()
            .unwrap_or_else(FixedQ32::zero);

        // Get peer position for own force computation.
        let peer_pos = self
            .peer_positions
            .lock()
            .expect("hamiltonian handler lock poisoned")
            .get(role)
            .copied()
            .unwrap_or_else(FixedQ32::zero);

        // Use own force computation (from received peer position).
        // The received_force is the peer's force on itself, not on us.
        let _unused_peer_force = received_force;
        let force = self.force(vals[0], peer_pos);

        let two = FixedQ32::from_ratio(2, 1).expect("2 must be representable");
        // Leapfrog integration:
        // 1. Half-kick: p += F * dt/2
        vals[1] = vals[1] + force * dt / two;
        // 2. Drift: q += p/m * dt
        vals[0] = vals[0] + vals[1] / mass * dt;
        // 3. Half-kick with new force: p += F(new_q) * dt/2
        let peer_pos_for_new = peer_pos; // peer position hasn't changed this tick
        let new_force = self.force(vals[0], peer_pos_for_new);
        vals[1] = vals[1] + new_force * dt / two;

        write_f64s(state, &vals);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::material::HamiltonianParams;
    use crate::value_conv::{registers_to_f64s, write_f64s};

    fn test_params() -> HamiltonianParams {
        HamiltonianParams {
            spring_constant: FixedQ32::one(),
            mass: FixedQ32::one(),
            dimensions: 1,
            initial_positions: vec![FixedQ32::one(), -FixedQ32::one()],
            initial_momenta: vec![FixedQ32::zero(), FixedQ32::zero()],
            step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
        }
    }

    #[test]
    fn test_force_harmonic() {
        let handler = HamiltonianHandler::new(test_params());
        // F = -k * (q_A - q_B) = -1.0 * (1.0 - (-1.0)) = -2.0
        let one = FixedQ32::one();
        let f = handler.force(one, -one);
        let expected = -FixedQ32::from_ratio(2, 1).expect("2");
        let tol = FixedQ32::from_ratio(1, 1_000_000_000).expect("tolerance");
        assert!((f - expected).abs() < tol);
    }

    #[test]
    fn test_leapfrog_preserves_energy_approx() {
        let params = test_params();
        let handler = HamiltonianHandler::new(params.clone());

        // Set up peer position for role A
        handler
            .peer_positions
            .lock()
            .expect("hamiltonian handler lock poisoned")
            .insert("A".to_string(), -FixedQ32::one());
        handler
            .peer_forces
            .lock()
            .expect("hamiltonian handler lock poisoned")
            .insert("A".to_string(), FixedQ32::zero());

        let mut state_a = vec![Value::Unit, Value::Unit];
        write_f64s(&mut state_a, &[FixedQ32::one(), FixedQ32::zero()]);
        let peer_pos = -FixedQ32::one();
        let two = FixedQ32::from_ratio(2, 1).expect("2");

        let ke = |s: &[FixedQ32]| -> FixedQ32 { s[1] * s[1] / (two * params.mass) };
        let pe = |s: &[FixedQ32]| -> FixedQ32 {
            params.spring_constant / two * (s[0] - peer_pos) * (s[0] - peer_pos)
        };
        let initial_vals = registers_to_f64s(&state_a);
        let initial_energy = ke(&initial_vals) + pe(&initial_vals);

        // Simulate 100 integration steps (each needs 4 ticks)
        for _ in 0..400 {
            handler.step("A", &mut state_a).unwrap();
        }

        let final_vals = registers_to_f64s(&state_a);
        let final_energy = ke(&final_vals) + pe(&final_vals);

        let relative_error = (final_energy - initial_energy).abs() / initial_energy;
        let threshold = FixedQ32::from_ratio(1, 100).expect("0.01");
        assert!(
            relative_error < threshold,
            "energy drift too large: initial={initial_energy}, final={final_energy}, relative_error={relative_error}"
        );
    }
}
