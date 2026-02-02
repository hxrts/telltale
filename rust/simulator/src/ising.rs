//! Mean-field Ising effect handler.
//!
//! Implements the drift function `tanh(beta * magnetization)` with Euler
//! integration. Each protocol tick: receive peer concentrations, compute
//! local drift, advance state, send updated concentrations.

use serde_json::Value;

use crate::material::MeanFieldParams;
use crate::scheduler::EffectHandler;

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
        state: &[f64],
    ) -> Result<Value, String> {
        // Send current concentrations as the payload.
        serde_json::to_value(state).map_err(|e| e.to_string())
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<f64>,
        _payload: &Value,
    ) -> Result<(), String> {
        // For mean-field: receiving peer concentrations doesn't immediately
        // modify local state. The drift computation in `step` uses only the
        // local state (mean-field approximation: each species sees the global
        // magnetization through its own concentration).
        Ok(())
    }

    fn step(&self, _role: &str, state: &mut Vec<f64>) -> Result<(), String> {
        if state.len() != 2 {
            return Err(format!(
                "mean-field Ising expects 2-species state, got {}",
                state.len()
            ));
        }

        let dt = self.params.step_size;
        let beta = self.params.beta;

        // Magnetization m = x_up - x_down (where x_up = state[0], x_down = state[1]).
        let m = state[0] - state[1];

        // Drift toward equilibrium: dx_up/dt = tanh(beta * m) - m
        // This drives concentrations toward the mean-field fixed point.
        let drift = (beta * m).tanh() - m;

        // Euler step: state[0] += drift * dt, state[1] -= drift * dt.
        // This preserves the constraint state[0] + state[1] = 1.
        state[0] += drift * dt;
        state[1] -= drift * dt;

        // Clamp to simplex (numerical safety).
        for x in state.iter_mut() {
            *x = x.clamp(0.0, 1.0);
        }

        // Renormalize to ensure exact simplex membership.
        let sum: f64 = state.iter().sum();
        if sum > 0.0 {
            for x in state.iter_mut() {
                *x /= sum;
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::material::MeanFieldParams;

    fn test_params(beta: f64) -> MeanFieldParams {
        MeanFieldParams {
            beta,
            species: vec!["up".into(), "down".into()],
            initial_state: vec![0.6, 0.4],
            step_size: 0.01,
        }
    }

    #[test]
    fn test_ising_step_preserves_simplex() {
        let handler = IsingHandler::new(test_params(0.5));
        let mut state = vec![0.6, 0.4];

        for _ in 0..1000 {
            handler.step("A", &mut state).unwrap();
        }

        let sum: f64 = state.iter().sum();
        assert!(
            (sum - 1.0).abs() < 1e-10,
            "sum should be 1.0, got {sum}"
        );
        assert!(state.iter().all(|&x| x >= 0.0), "all non-negative");
    }

    #[test]
    fn test_ising_subcritical_converges_to_half() {
        // beta < 1: unique fixed point at m=0 (x_up = x_down = 0.5).
        let handler = IsingHandler::new(test_params(0.5));
        let mut state = vec![0.7, 0.3];

        for _ in 0..10000 {
            handler.step("A", &mut state).unwrap();
        }

        assert!(
            (state[0] - 0.5).abs() < 1e-4,
            "subcritical should converge to 0.5, got {}",
            state[0]
        );
    }

    #[test]
    fn test_ising_send_returns_state() {
        let handler = IsingHandler::new(test_params(1.5));
        let state = vec![0.6, 0.4];
        let payload = handler.handle_send("A", "B", "concentration", &state).unwrap();
        let arr: Vec<f64> = serde_json::from_value(payload).unwrap();
        assert_eq!(arr, vec![0.6, 0.4]);
    }
}
