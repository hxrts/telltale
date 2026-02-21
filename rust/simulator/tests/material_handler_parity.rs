//! Material-handler parity fixtures mirrored by Lean `Runtime.Tests.SimulatorParity`.

use telltale_simulator::handler_from_material;
use telltale_simulator::material::{
    ContinuumFieldParams, HamiltonianParams, MaterialParams, MeanFieldParams,
};
use telltale_simulator::material_handlers::{
    ContinuumFieldHandler, HamiltonianHandler, IsingHandler,
};
use telltale_types::FixedQ32;
use telltale_vm::coroutine::Value;
use telltale_vm::effect::EffectHandler;

fn q32(value: FixedQ32) -> Value {
    Value::Str(format!("q32:{}", value.to_bits()))
}

fn decode_q32(value: &Value) -> FixedQ32 {
    match value {
        Value::Str(text) => {
            let bits = text
                .strip_prefix("q32:")
                .expect("q32 scalar payload")
                .parse::<i64>()
                .expect("valid q32 bits");
            FixedQ32::from_bits(bits)
        }
        other => panic!("expected q32 string payload, got {other:?}"),
    }
}

fn regs(values: &[FixedQ32]) -> Vec<Value> {
    let mut out = vec![Value::Unit, Value::Unit];
    out.extend(values.iter().copied().map(q32));
    out
}

fn state_at(regs: &[Value], idx: usize) -> FixedQ32 {
    decode_q32(&regs[idx + 2])
}

fn approx_eq(lhs: FixedQ32, rhs: FixedQ32, eps: FixedQ32) -> bool {
    (lhs - rhs).abs() <= eps
}

#[test]
fn ising_equilibrium_fixture_matches_lean_mirror() {
    let params = MeanFieldParams {
        beta: FixedQ32::from_ratio(3, 2).expect("1.5"),
        species: vec!["up".into(), "down".into()],
        initial_state: vec![FixedQ32::half(), FixedQ32::half()],
        step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
    };
    let handler = IsingHandler::new(params);
    let mut state = regs(&[FixedQ32::half(), FixedQ32::half()]);

    handler.step("A", &mut state).expect("step succeeds");

    assert_eq!(state_at(&state, 0), FixedQ32::half());
    assert_eq!(state_at(&state, 1), FixedQ32::half());
}

#[test]
fn ising_zero_beta_drift_fixture_matches_lean_mirror() {
    let params = MeanFieldParams {
        beta: FixedQ32::zero(),
        species: vec!["up".into(), "down".into()],
        initial_state: vec![
            FixedQ32::from_ratio(3, 5).expect("0.6"),
            FixedQ32::from_ratio(2, 5).expect("0.4"),
        ],
        step_size: FixedQ32::from_ratio(1, 10).expect("0.1"),
    };
    let handler = IsingHandler::new(params);
    let mut state = regs(&[
        FixedQ32::from_ratio(3, 5).expect("0.6"),
        FixedQ32::from_ratio(2, 5).expect("0.4"),
    ]);

    handler.step("A", &mut state).expect("step succeeds");

    let eps = FixedQ32::from_ratio(1, 1_000_000).expect("epsilon");
    let expected_up = FixedQ32::from_ratio(29, 50).expect("0.58");
    let expected_down = FixedQ32::from_ratio(21, 50).expect("0.42");
    assert!(approx_eq(state_at(&state, 0), expected_up, eps));
    assert!(approx_eq(state_at(&state, 1), expected_down, eps));
}

#[test]
fn hamiltonian_phase_gate_fixture_matches_lean_mirror() {
    let params = HamiltonianParams {
        spring_constant: FixedQ32::one(),
        mass: FixedQ32::one(),
        dimensions: 1,
        initial_positions: vec![FixedQ32::one(), FixedQ32::neg_one()],
        initial_momenta: vec![FixedQ32::zero(), FixedQ32::zero()],
        step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
    };
    let handler = HamiltonianHandler::new(params);
    let mut state = regs(&[FixedQ32::one(), FixedQ32::zero()]);

    handler.step("A", &mut state).expect("step succeeds");

    assert_eq!(state_at(&state, 0), FixedQ32::one());
    assert_eq!(state_at(&state, 1), FixedQ32::zero());
}

#[test]
fn hamiltonian_leapfrog_fixture_matches_lean_mirror() {
    let params = HamiltonianParams {
        spring_constant: FixedQ32::one(),
        mass: FixedQ32::one(),
        dimensions: 1,
        initial_positions: vec![FixedQ32::one(), FixedQ32::neg_one()],
        initial_momenta: vec![FixedQ32::zero(), FixedQ32::zero()],
        step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
    };
    let handler = HamiltonianHandler::new(params);
    let mut state = regs(&[FixedQ32::one(), FixedQ32::zero()]);
    let mut recv_state = Vec::new();
    handler
        .handle_recv(
            "A",
            "B",
            "position",
            &mut recv_state,
            &q32(FixedQ32::neg_one()),
        )
        .expect("seed peer position");

    for _ in 0..3 {
        handler.step("A", &mut state).expect("phase gate steps");
    }
    handler.step("A", &mut state).expect("integration step");

    let eps = FixedQ32::from_ratio(1, 1_000_000).expect("epsilon");
    let expected_pos = FixedQ32::from_ratio(9_999, 10_000).expect("0.9999");
    let expected_mom = FixedQ32::from_ratio(-39_999, 2_000_000).expect("-0.0199995");
    assert!(approx_eq(state_at(&state, 0), expected_pos, eps));
    assert!(approx_eq(state_at(&state, 1), expected_mom, eps));
}

#[test]
fn continuum_phase_and_diffusion_fixtures_match_lean_mirror() {
    let params = ContinuumFieldParams {
        coupling: FixedQ32::one(),
        components: 1,
        initial_fields: vec![FixedQ32::one(), FixedQ32::zero()],
        step_size: FixedQ32::from_ratio(1, 10).expect("0.1"),
    };
    let handler = ContinuumFieldHandler::new(params);
    let mut state = regs(&[FixedQ32::one()]);
    let mut recv_state = Vec::new();
    handler
        .handle_recv("A", "B", "field", &mut recv_state, &q32(FixedQ32::zero()))
        .expect("seed peer field");

    handler.step("A", &mut state).expect("phase 0");
    assert_eq!(state_at(&state, 0), FixedQ32::one());

    handler.step("A", &mut state).expect("phase 1");
    let eps = FixedQ32::from_ratio(1, 1_000_000).expect("epsilon");
    let expected = FixedQ32::from_ratio(9, 10).expect("0.9");
    assert!(approx_eq(state_at(&state, 0), expected, eps));
}

#[test]
fn material_handler_factory_dispatches_all_variants() {
    let mean = MaterialParams::MeanField(MeanFieldParams {
        beta: FixedQ32::one(),
        species: vec!["up".into(), "down".into()],
        initial_state: vec![FixedQ32::half(), FixedQ32::half()],
        step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
    });
    let ham = MaterialParams::Hamiltonian(HamiltonianParams {
        spring_constant: FixedQ32::one(),
        mass: FixedQ32::one(),
        dimensions: 1,
        initial_positions: vec![FixedQ32::one(), FixedQ32::neg_one()],
        initial_momenta: vec![FixedQ32::zero(), FixedQ32::zero()],
        step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
    });
    let cont = MaterialParams::ContinuumField(ContinuumFieldParams {
        coupling: FixedQ32::one(),
        components: 1,
        initial_fields: vec![FixedQ32::one(), FixedQ32::zero()],
        step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
    });

    let _ = handler_from_material(&mean);
    let _ = handler_from_material(&ham);
    let _ = handler_from_material(&cont);
}
