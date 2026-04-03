//! Hamiltonian 2-body effect handler.

use std::collections::BTreeMap;
use std::sync::Mutex;
use telltale_types::FixedQ32;

use crate::field::HamiltonianFieldSpec;
use crate::value_conv::{fixed_to_value, registers_to_f64s, value_to_f64, write_f64s};
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};

/// Hamiltonian field effect handler using symplectic integration.
pub struct HamiltonianHandler {
    params: HamiltonianFieldSpec,
    peer_positions: Mutex<BTreeMap<String, FixedQ32>>,
    peer_forces: Mutex<BTreeMap<String, FixedQ32>>,
    tick_count: Mutex<BTreeMap<String, usize>>,
}

impl HamiltonianHandler {
    /// Create a new handler from a Hamiltonian field spec.
    #[must_use]
    pub fn new(params: HamiltonianFieldSpec) -> Self {
        Self {
            params,
            peer_positions: Mutex::new(BTreeMap::new()),
            peer_forces: Mutex::new(BTreeMap::new()),
            tick_count: Mutex::new(BTreeMap::new()),
        }
    }

    fn lock_peer_positions(
        &self,
    ) -> Result<std::sync::MutexGuard<'_, BTreeMap<String, FixedQ32>>, String> {
        self.peer_positions
            .lock()
            .map_err(|_| "hamiltonian handler peer-position lock poisoned".to_string())
    }

    fn lock_peer_forces(
        &self,
    ) -> Result<std::sync::MutexGuard<'_, BTreeMap<String, FixedQ32>>, String> {
        self.peer_forces
            .lock()
            .map_err(|_| "hamiltonian handler peer-force lock poisoned".to_string())
    }

    fn lock_tick_count(
        &self,
    ) -> Result<std::sync::MutexGuard<'_, BTreeMap<String, usize>>, String> {
        self.tick_count
            .lock()
            .map_err(|_| "hamiltonian handler tick-counter lock poisoned".to_string())
    }

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
    ) -> EffectResult<Value> {
        let vals = registers_to_f64s(state);
        match label {
            "position" => vals
                .first()
                .copied()
                .map(fixed_to_value)
                .map(EffectResult::success)
                .unwrap_or_else(|| {
                    EffectResult::failure(EffectFailure::invalid_input("missing position state"))
                }),
            "force" => {
                let peer_pos = match self.lock_peer_positions() {
                    Ok(peer_positions) => peer_positions
                        .get(role)
                        .copied()
                        .unwrap_or_else(FixedQ32::zero),
                    Err(err) => {
                        return EffectResult::failure(EffectFailure::contract_violation(err));
                    }
                };
                let my_pos = vals.first().copied().unwrap_or_else(FixedQ32::zero);
                let f = self.force(my_pos, peer_pos);
                EffectResult::success(fixed_to_value(f))
            }
            other => EffectResult::failure(EffectFailure::invalid_input(format!(
                "unknown label: {other}"
            ))),
        }
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        self.handle_send(input.role, input.partner, input.label, input.state)
            .map_success(SendDecision::Deliver)
    }

    fn handle_recv(
        &self,
        role: &str,
        _partner: &str,
        label: &str,
        _state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        let val = match value_to_f64(payload) {
            Ok(val) => val,
            Err(err) => return EffectResult::failure(EffectFailure::invalid_input(err)),
        };
        match label {
            "position" => {
                let mut peer_positions = match self.lock_peer_positions() {
                    Ok(peer_positions) => peer_positions,
                    Err(err) => {
                        return EffectResult::failure(EffectFailure::contract_violation(err));
                    }
                };
                peer_positions.insert(role.to_string(), val);
            }
            "force" => {
                let mut peer_forces = match self.lock_peer_forces() {
                    Ok(peer_forces) => peer_forces,
                    Err(err) => {
                        return EffectResult::failure(EffectFailure::contract_violation(err));
                    }
                };
                peer_forces.insert(role.to_string(), val);
            }
            other => {
                return EffectResult::failure(EffectFailure::invalid_input(format!(
                    "unknown label: {other}"
                )));
            }
        }
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> EffectResult<String> {
        match labels.first().cloned() {
            Some(label) => EffectResult::success(label),
            None => EffectResult::failure(EffectFailure::invalid_input("no labels available")),
        }
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> EffectResult<()> {
        let mut vals = registers_to_f64s(state);
        if vals.len() != 2 {
            return EffectResult::failure(EffectFailure::invalid_input(format!(
                "Hamiltonian expects [position, momentum], got {} elements",
                vals.len()
            )));
        }

        let phase = {
            let mut ticks = match self.lock_tick_count() {
                Ok(ticks) => ticks,
                Err(err) => return EffectResult::failure(EffectFailure::contract_violation(err)),
            };
            let tick = ticks.entry(role.to_string()).or_insert(0);
            let phase = *tick % 4;
            *tick += 1;
            phase
        };

        if phase != 3 {
            return EffectResult::success(());
        }

        let dt = self.params.step_size;
        let mass = self.params.mass;

        let peer_pos = match self.lock_peer_positions() {
            Ok(peer_positions) => peer_positions
                .get(role)
                .copied()
                .unwrap_or_else(FixedQ32::zero),
            Err(err) => return EffectResult::failure(EffectFailure::contract_violation(err)),
        };

        let force = self.force(vals[0], peer_pos);
        let two = FixedQ32::from_ratio(2, 1).expect("2 must be representable");
        vals[1] += force * dt / two;
        vals[0] = vals[0] + vals[1] / mass * dt;
        let new_force = self.force(vals[0], peer_pos);
        vals[1] += new_force * dt / two;

        write_f64s(state, &vals);
        EffectResult::success(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::HamiltonianFieldSpec;
    use crate::value_conv::{registers_to_f64s, write_f64s};
    use telltale_machine::model::effects::{EffectFailure, EffectResult};

    fn expect_success<T>(result: EffectResult<T>) -> T {
        result
            .expect_success(|| EffectFailure::contract_violation("unexpected blocked effect"))
            .expect("effect should succeed")
    }

    fn test_params() -> HamiltonianFieldSpec {
        HamiltonianFieldSpec {
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

        for _ in 0..400 {
            expect_success(handler.step("A", &mut state_a));
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
