//! Mean-field Ising effect handler.
//!
//! Implements the drift function `tanh(beta * magnetization)` with Euler
//! integration. Each protocol tick: receive peer concentrations, compute
//! local drift, advance state, send updated concentrations.

use crate::field::MeanFieldSpec;
use crate::value_conv::{fixed_vec_to_value, registers_to_f64s, write_f64s};
use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{EffectFailure, EffectHandler, EffectResult};
use telltale_types::FixedQ32;

/// Effect handler for the mean-field Ising model.
pub struct IsingHandler {
    params: MeanFieldSpec,
}

impl IsingHandler {
    /// Create a new Ising handler from field parameters.
    #[must_use]
    pub fn new(params: MeanFieldSpec) -> Self {
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
    ) -> EffectResult<Value> {
        EffectResult::success(fixed_vec_to_value(&registers_to_f64s(state)))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> EffectResult<()> {
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

    fn step(&self, _role: &str, state: &mut Vec<Value>) -> EffectResult<()> {
        let mut vals = registers_to_f64s(state);
        if vals.len() != 2 {
            return EffectResult::failure(EffectFailure::invalid_input(format!(
                "mean-field Ising expects 2-species state, got {}",
                vals.len()
            )));
        }

        let dt = self.params.step_size;
        let beta = self.params.beta;
        let m = vals[0] - vals[1];
        let drift = (beta * m).tanh() - m;
        vals[0] += drift * dt;
        vals[1] -= drift * dt;

        let zero = FixedQ32::zero();
        let one = FixedQ32::one();
        for x in vals.iter_mut() {
            *x = (*x).clamp(zero, one);
        }

        let sum: FixedQ32 = vals.iter().sum();
        if sum > zero {
            for x in vals.iter_mut() {
                *x /= sum;
            }
        }

        write_f64s(state, &vals);
        EffectResult::success(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::MeanFieldSpec;
    use crate::value_conv::{registers_to_f64s, write_f64s};
    use telltale_machine::model::effects::{EffectFailure, EffectResult};

    fn expect_success<T>(result: EffectResult<T>) -> T {
        result
            .expect_success(|| EffectFailure::contract_violation("unexpected blocked effect"))
            .expect("effect should succeed")
    }

    fn test_params(beta: FixedQ32) -> MeanFieldSpec {
        MeanFieldSpec {
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
            expect_success(handler.step("A", &mut state));
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
            expect_success(handler.step("A", &mut state));
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
            .expect_success(|| EffectFailure::contract_violation("unexpected blocked effect"))
            .expect("effect should succeed");
        assert_eq!(payload, fixed_vec_to_value(&[v06, v04]));
    }
}
