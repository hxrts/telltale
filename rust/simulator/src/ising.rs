//! Mean-field Ising effect handler.
//!
//! Implements the drift function `tanh(beta * magnetization)` with Euler
//! integration. Each protocol tick: receive peer concentrations, compute
//! local drift, advance state, send updated concentrations.

use crate::material::MeanFieldParams;
use crate::value_conv::{registers_to_f64s, write_f64s};
use telltale_types::FixedQ32;
use telltale_vm::coroutine::Value;
use telltale_vm::effect::EffectHandler;

/// Effect handler for the mean-field Ising model.
pub struct IsingHandler {
    params: MeanFieldParams,
}

impl IsingHandler {
    /// Create a new Ising handler from material parameters.
    #[must_use]
    pub fn new(params: MeanFieldParams) -> Self {
        Self { params }
    }
}

impl EffectHandler for IsingHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        state: &[Value],
    ) -> Result<Value, String> {
        // Send current concentrations as the payload.
        Ok(Value::Q32Vec(registers_to_f64s(state)))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> Result<(), String> {
        // For mean-field: receiving peer concentrations doesn't immediately
        // modify local state. The drift computation in `step` uses only the
        // local state (mean-field approximation: each species sees the global
        // magnetization through its own concentration).
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

    fn step(&self, _role: &str, state: &mut Vec<Value>) -> Result<(), String> {
        let mut vals = registers_to_f64s(state);
        if vals.len() != 2 {
            return Err(format!(
                "mean-field Ising expects 2-species state, got {}",
                vals.len()
            ));
        }

        let dt = self.params.step_size;
        let beta = self.params.beta;

        // Magnetization m = x_up - x_down (where x_up = state[0], x_down = state[1]).
        let m = vals[0] - vals[1];

        // Drift toward equilibrium: dx_up/dt = tanh(beta * m) - m
        // This drives concentrations toward the mean-field fixed point.
        let drift = (beta * m).tanh() - m;

        // Euler step: state[0] += drift * dt, state[1] -= drift * dt.
        // This preserves the constraint state[0] + state[1] = 1.
        vals[0] += drift * dt;
        vals[1] -= drift * dt;

        // Clamp to simplex (numerical safety).
        let zero = FixedQ32::zero();
        let one = FixedQ32::one();
        for x in vals.iter_mut() {
            *x = (*x).clamp(zero, one);
        }

        // Renormalize to ensure exact simplex membership.
        let sum: FixedQ32 = vals.iter().sum();
        if sum > zero {
            for x in vals.iter_mut() {
                *x = *x / sum;
            }
        }

        write_f64s(state, &vals);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::material::MeanFieldParams;
    use crate::value_conv::{registers_to_f64s, write_f64s};

    fn test_params(beta: FixedQ32) -> MeanFieldParams {
        MeanFieldParams {
            beta,
            species: vec!["up".into(), "down".into()],
            initial_state: vec![
                FixedQ32::from_ratio(6, 10).expect("0.6"),
                FixedQ32::from_ratio(4, 10).expect("0.4"),
            ],
            step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
        }
    }

    #[test]
    fn test_ising_step_preserves_simplex() {
        let handler = IsingHandler::new(test_params(FixedQ32::half()));
        let mut state = vec![Value::Unit, Value::Unit];
        write_f64s(
            &mut state,
            &[
                FixedQ32::from_ratio(6, 10).expect("0.6"),
                FixedQ32::from_ratio(4, 10).expect("0.4"),
            ],
        );

        for _ in 0..1000 {
            handler.step("A", &mut state).unwrap();
        }

        let vals = registers_to_f64s(&state);
        let sum: FixedQ32 = vals.iter().sum();
        let one = FixedQ32::one();
        let eps = FixedQ32::from_ratio(1, 1_000_000_000).expect("epsilon");
        assert!((sum - one).abs() < eps, "sum should be 1.0, got {sum}");
        let zero = FixedQ32::zero();
        assert!(vals.iter().all(|&x| x >= zero), "all non-negative");
    }

    #[test]
    fn test_ising_subcritical_converges_to_half() {
        // beta < 1: unique fixed point at m=0 (x_up = x_down = 0.5).
        let handler = IsingHandler::new(test_params(FixedQ32::half()));
        let mut state = vec![Value::Unit, Value::Unit];
        write_f64s(
            &mut state,
            &[
                FixedQ32::from_ratio(7, 10).expect("0.7"),
                FixedQ32::from_ratio(3, 10).expect("0.3"),
            ],
        );

        for _ in 0..10000 {
            handler.step("A", &mut state).unwrap();
        }

        let vals = registers_to_f64s(&state);
        let half = FixedQ32::half();
        let eps = FixedQ32::from_ratio(1, 10000).expect("1e-4");
        assert!(
            (vals[0] - half).abs() < eps,
            "subcritical should converge to 0.5, got {}",
            vals[0]
        );
    }

    #[test]
    fn test_ising_send_returns_state() {
        let handler = IsingHandler::new(test_params(FixedQ32::from_ratio(3, 2).expect("1.5")));
        let mut state = vec![Value::Unit, Value::Unit];
        let v06 = FixedQ32::from_ratio(6, 10).expect("0.6");
        let v04 = FixedQ32::from_ratio(4, 10).expect("0.4");
        write_f64s(&mut state, &[v06, v04]);
        let payload = handler
            .handle_send("A", "B", "concentration", &state)
            .unwrap();
        assert_eq!(payload, Value::Q32Vec(vec![v06, v04]));
    }
}
