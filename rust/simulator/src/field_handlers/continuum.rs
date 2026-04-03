//! Continuum field effect handler (two-site discretization).

use std::collections::BTreeMap;
use std::sync::Mutex;
use telltale_types::FixedQ32;

use crate::field::ContinuumFieldSpec;
use crate::value_conv::{fixed_to_value, registers_to_f64s, value_to_f64, write_f64s};
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{EffectFailure, EffectHandler, EffectResult};

/// Continuum field effect handler using two-site discretization.
pub struct ContinuumFieldHandler {
    params: ContinuumFieldSpec,
    peer_fields: Mutex<BTreeMap<String, FixedQ32>>,
    tick_count: Mutex<BTreeMap<String, usize>>,
}

impl ContinuumFieldHandler {
    /// Create a new handler from a continuum field spec.
    #[must_use]
    pub fn new(params: ContinuumFieldSpec) -> Self {
        Self {
            params,
            peer_fields: Mutex::new(BTreeMap::new()),
            tick_count: Mutex::new(BTreeMap::new()),
        }
    }

    fn lock_peer_fields(
        &self,
    ) -> Result<std::sync::MutexGuard<'_, BTreeMap<String, FixedQ32>>, String> {
        self.peer_fields
            .lock()
            .map_err(|_| "continuum handler peer field state lock poisoned".to_string())
    }

    fn lock_tick_count(
        &self,
    ) -> Result<std::sync::MutexGuard<'_, BTreeMap<String, usize>>, String> {
        self.tick_count
            .lock()
            .map_err(|_| "continuum handler tick counter lock poisoned".to_string())
    }
}

impl EffectHandler for ContinuumFieldHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        state: &[Value],
    ) -> EffectResult<Value> {
        let vals = registers_to_f64s(state);
        if vals.is_empty() {
            return EffectResult::failure(EffectFailure::invalid_input(
                "continuum field expects at least 1 field component",
            ));
        }
        EffectResult::success(fixed_to_value(vals[0]))
    }

    fn handle_recv(
        &self,
        role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        payload: &Value,
    ) -> EffectResult<()> {
        let val = match value_to_f64(payload) {
            Ok(val) => val,
            Err(err) => return EffectResult::failure(EffectFailure::invalid_input(err)),
        };
        let mut peer_fields = match self.lock_peer_fields() {
            Ok(peer_fields) => peer_fields,
            Err(err) => return EffectResult::failure(EffectFailure::contract_violation(err)),
        };
        peer_fields.insert(role.to_string(), val);
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
        if vals.is_empty() {
            return EffectResult::failure(EffectFailure::invalid_input(
                "continuum field expects at least 1 field component",
            ));
        }

        let phase = {
            let mut ticks = match self.lock_tick_count() {
                Ok(ticks) => ticks,
                Err(err) => return EffectResult::failure(EffectFailure::contract_violation(err)),
            };
            let tick = ticks.entry(role.to_string()).or_insert(0);
            let phase = *tick % 2;
            *tick += 1;
            phase
        };

        if phase != 1 {
            return EffectResult::success(());
        }

        let peer_field = match self.lock_peer_fields() {
            Ok(peer_fields) => peer_fields.get(role).copied().unwrap_or(vals[0]),
            Err(err) => return EffectResult::failure(EffectFailure::contract_violation(err)),
        };

        let dt = self.params.step_size;
        let k = self.params.coupling;
        let drift = k * (peer_field - vals[0]);
        vals[0] += drift * dt;

        write_f64s(state, &vals);
        EffectResult::success(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::ContinuumFieldSpec;
    use crate::value_conv::{registers_to_f64s, write_f64s};
    use telltale_machine::model::effects::{EffectFailure, EffectResult};

    fn expect_success<T>(result: EffectResult<T>) -> T {
        result
            .expect_success(|| EffectFailure::contract_violation("unexpected blocked effect"))
            .expect("effect should succeed")
    }

    fn test_params() -> ContinuumFieldSpec {
        ContinuumFieldSpec {
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
            let payload_a = expect_success(handler.handle_send("A", "B", "field", &state_a));
            expect_success(handler.handle_recv("B", "A", "field", &mut state_b, &payload_a));
            expect_success(handler.step("A", &mut state_a));
            expect_success(handler.step("B", &mut state_b));

            let payload_b = expect_success(handler.handle_send("B", "A", "field", &state_b));
            expect_success(handler.handle_recv("A", "B", "field", &mut state_a, &payload_b));
            expect_success(handler.step("A", &mut state_a));
            expect_success(handler.step("B", &mut state_b));
        }

        let final_total = registers_to_f64s(&state_a)[0] + registers_to_f64s(&state_b)[0];
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
            let payload_a = expect_success(handler.handle_send("A", "B", "field", &state_a));
            expect_success(handler.handle_recv("B", "A", "field", &mut state_b, &payload_a));
            expect_success(handler.step("A", &mut state_a));
            expect_success(handler.step("B", &mut state_b));

            let payload_b = expect_success(handler.handle_send("B", "A", "field", &state_b));
            expect_success(handler.handle_recv("A", "B", "field", &mut state_a, &payload_b));
            expect_success(handler.step("A", &mut state_a));
            expect_success(handler.step("B", &mut state_b));
        }

        let vals_a = registers_to_f64s(&state_a);
        let vals_b = registers_to_f64s(&state_b);
        let half = FixedQ32::half();
        let eps = FixedQ32::from_ratio(1, 10000).expect("1e-4");
        assert!((vals_a[0] - half).abs() < eps);
        assert!((vals_b[0] - half).abs() < eps);
    }
}
