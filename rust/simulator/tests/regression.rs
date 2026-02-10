//! Regression test suite (B4).
//!
//! Runs both materials (mean-field Ising and Hamiltonian 2-body) through
//! both Lean and Rust projection paths, verifying identical traces.

use std::collections::{BTreeMap, HashMap};
use telltale_types::FixedQ32;

use telltale_lean_bridge::export::global_to_json;
use telltale_lean_bridge::import::json_to_local;
use telltale_lean_bridge::runner::LeanRunner;
use telltale_simulator::analysis;
use telltale_simulator::hamiltonian::HamiltonianHandler;
use telltale_simulator::ising::IsingHandler;
use telltale_simulator::material::{HamiltonianParams, MeanFieldParams};
use telltale_simulator::runner;
use telltale_simulator::trace::Trace;
use telltale_simulator::EffectHandler;
use telltale_theory::project;
use telltale_types::{GlobalType, Label, LocalTypeR, PayloadSort};

/// Skip if Lean validator binary is unavailable.
fn require_lean() -> LeanRunner {
    if !LeanRunner::is_projection_available() {
        eprintln!(
            "SKIP: telltale_validator not found, run `cd lean && lake build telltale_validator`"
        );
        std::process::exit(0);
    }
    LeanRunner::for_projection().expect("validator available")
}

/// Project via Lean, returning local types per role.
fn project_lean(
    runner: &LeanRunner,
    g: &GlobalType,
    roles: &[&str],
) -> BTreeMap<String, LocalTypeR> {
    let json = global_to_json(g);
    let role_strings: Vec<String> = roles.iter().map(|r| (*r).to_string()).collect();
    let projections = runner
        .project(&json, &role_strings)
        .expect("Lean projection");
    roles
        .iter()
        .map(|r| {
            let local = json_to_local(&projections[*r]).expect("parse local type");
            ((*r).to_string(), local)
        })
        .collect()
}

/// Project via Rust, returning local types per role.
fn project_rust(g: &GlobalType, roles: &[&str]) -> BTreeMap<String, LocalTypeR> {
    roles
        .iter()
        .map(|r| {
            let local = project(g, r).expect("Rust projection");
            ((*r).to_string(), local)
        })
        .collect()
}

/// Run a simulation and return the trace.
fn run_sim(
    global: &GlobalType,
    projections: &BTreeMap<String, LocalTypeR>,
    initial_states: &BTreeMap<String, Vec<FixedQ32>>,
    steps: usize,
    handler: &dyn EffectHandler,
) -> Trace {
    runner::run(projections, global, initial_states, steps, handler).expect("simulation succeeds")
}

/// Assert two traces are identical within tolerance (comparing by step+role key).
fn assert_traces_equal(lean_trace: &Trace, rust_trace: &Trace, tolerance: FixedQ32) {
    assert_eq!(
        lean_trace.records.len(),
        rust_trace.records.len(),
        "trace lengths differ"
    );

    // Index by (step, role) to handle different HashMap iteration orders.
    let lean_map: HashMap<(u64, &str), &[FixedQ32]> = lean_trace
        .records
        .iter()
        .map(|r| ((r.step, r.role.as_str()), r.state.as_slice()))
        .collect();

    for r in &rust_trace.records {
        let key = (r.step, r.role.as_str());
        let lean_state = lean_map
            .get(&key)
            .unwrap_or_else(|| panic!("missing lean record for step {} role {}", r.step, r.role));
        assert_eq!(lean_state.len(), r.state.len(), "state length mismatch");
        for (i, (lv, rv)) in lean_state.iter().zip(r.state.iter()).enumerate() {
            assert!(
                (*lv - *rv).abs() < tolerance,
                "step {} role {} state[{i}]: lean={lv}, rust={rv}",
                r.step,
                r.role,
            );
        }
    }
}

// ============================================================================
// Mean-field Ising regression
// ============================================================================

fn ising_global_type() -> GlobalType {
    GlobalType::mu(
        "step",
        GlobalType::send(
            "A",
            "B",
            Label::with_sort("concentration", PayloadSort::Vector(2)),
            GlobalType::send(
                "B",
                "A",
                Label::with_sort("concentration", PayloadSort::Vector(2)),
                GlobalType::var("step"),
            ),
        ),
    )
}

fn ising_params() -> MeanFieldParams {
    MeanFieldParams {
        beta: FixedQ32::half(),
        species: vec!["up".into(), "down".into()],
        initial_state: vec![
            FixedQ32::from_ratio(6, 10).expect("0.6"),
            FixedQ32::from_ratio(4, 10).expect("0.4"),
        ],
        step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
    }
}

#[test]
fn test_ising_lean_vs_rust_identical_traces() {
    let runner = require_lean();
    let g = ising_global_type();
    let params = ising_params();
    let handler = IsingHandler::new(params.clone());

    let mut initial_states = BTreeMap::new();
    initial_states.insert("A".to_string(), params.initial_state.clone());
    initial_states.insert("B".to_string(), params.initial_state.clone());

    let lean_projs = project_lean(&runner, &g, &["A", "B"]);
    let rust_projs = project_rust(&g, &["A", "B"]);

    let lean_trace = run_sim(&g, &lean_projs, &initial_states, 100, &handler);
    let rust_trace = run_sim(&g, &rust_projs, &initial_states, 100, &handler);

    let tolerance = FixedQ32::from_ratio(1, 1_000_000_000i64).expect("1e-9");
    assert_traces_equal(&lean_trace, &rust_trace, tolerance);

    // Validate both traces pass analysis checks.
    let eq = [FixedQ32::half(), FixedQ32::half()];
    let lean_result = analysis::validate(&lean_trace, &["A", "B"], &eq);
    let rust_result = analysis::validate(&rust_trace, &["A", "B"], &eq);
    assert!(
        lean_result.passed,
        "Lean-projected trace should pass validation"
    );
    assert!(
        rust_result.passed,
        "Rust-projected trace should pass validation"
    );
}

// ============================================================================
// Hamiltonian 2-body regression
// ============================================================================

fn hamiltonian_global_type() -> GlobalType {
    GlobalType::mu(
        "step",
        GlobalType::send(
            "A",
            "B",
            Label::with_sort("position", PayloadSort::Real),
            GlobalType::send(
                "B",
                "A",
                Label::with_sort("position", PayloadSort::Real),
                GlobalType::send(
                    "A",
                    "B",
                    Label::with_sort("force", PayloadSort::Real),
                    GlobalType::send(
                        "B",
                        "A",
                        Label::with_sort("force", PayloadSort::Real),
                        GlobalType::var("step"),
                    ),
                ),
            ),
        ),
    )
}

fn hamiltonian_params() -> HamiltonianParams {
    HamiltonianParams {
        spring_constant: FixedQ32::one(),
        mass: FixedQ32::one(),
        dimensions: 1,
        initial_positions: vec![FixedQ32::one(), FixedQ32::neg_one()],
        initial_momenta: vec![FixedQ32::zero(), FixedQ32::zero()],
        step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
    }
}

#[test]
fn test_hamiltonian_lean_vs_rust_identical_traces() {
    let runner = require_lean();
    let g = hamiltonian_global_type();
    let params = hamiltonian_params();

    let mut initial_states = BTreeMap::new();
    initial_states.insert(
        "A".to_string(),
        vec![params.initial_positions[0], params.initial_momenta[0]],
    );
    initial_states.insert(
        "B".to_string(),
        vec![params.initial_positions[1], params.initial_momenta[1]],
    );

    let lean_projs = project_lean(&runner, &g, &["A", "B"]);
    let rust_projs = project_rust(&g, &["A", "B"]);

    // Use separate handlers since HamiltonianHandler has internal mutable state.
    let lean_handler = HamiltonianHandler::new(params.clone());
    let rust_handler = HamiltonianHandler::new(params.clone());

    let lean_trace = run_sim(&g, &lean_projs, &initial_states, 100, &lean_handler);
    let rust_trace = run_sim(&g, &rust_projs, &initial_states, 100, &rust_handler);

    let tolerance = FixedQ32::from_ratio(1, 1_000_000_000i64).expect("1e-9");
    assert_traces_equal(&lean_trace, &rust_trace, tolerance);

    // Validate energy conservation on both traces.
    let lean_energy = analysis::check_energy_conservation(
        &lean_trace,
        &["A", "B"],
        params.mass,
        params.spring_constant,
    );
    let rust_energy = analysis::check_energy_conservation(
        &rust_trace,
        &["A", "B"],
        params.mass,
        params.spring_constant,
    );
    assert!(
        lean_energy.passed,
        "Lean-projected trace should conserve energy"
    );
    assert!(
        rust_energy.passed,
        "Rust-projected trace should conserve energy"
    );
}
