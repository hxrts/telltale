//! End-to-end integration test: GlobalType → Lean projection → simulation → analysis.

use std::collections::HashMap;

use telltale_lean_bridge::export::global_to_json;
use telltale_lean_bridge::import::json_to_local;
use telltale_lean_bridge::runner::LeanRunner;
use telltale_simulator::analysis;
use telltale_simulator::hamiltonian::HamiltonianHandler;
use telltale_simulator::ising::IsingHandler;
use telltale_simulator::material::{HamiltonianParams, MeanFieldParams};
use telltale_simulator::scheduler::Scheduler;
use telltale_types::{GlobalType, Label, PayloadSort};

/// Skip if the Lean projection binary is unavailable.
fn require_lean() -> LeanRunner {
    if !LeanRunner::is_projection_available() {
        eprintln!("SKIP: projection_runner not found, run `cd lean && lake build`");
        std::process::exit(0);
    }
    LeanRunner::for_projection().expect("projection runner available")
}

#[test]
fn test_mean_field_ising_end_to_end() {
    let runner = require_lean();

    // 1. Construct mean-field Ising GlobalType:
    //    mu step. A -> B: concentration(vector 2). B -> A: concentration(vector 2). var step
    let g = GlobalType::mu(
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
    );

    // 2. Project via Lean.
    let json = global_to_json(&g);
    let roles = vec!["A".to_string(), "B".to_string()];
    let projections = runner.project(&json, &roles).expect("projection succeeds");

    let a_local = json_to_local(&projections["A"]).expect("parse A local type");
    let b_local = json_to_local(&projections["B"]).expect("parse B local type");

    // 3. Set up simulator.
    let params = MeanFieldParams {
        beta: 0.5, // subcritical: converges to [0.5, 0.5]
        species: vec!["up".into(), "down".into()],
        initial_state: vec![0.6, 0.4],
        step_size: 0.01,
    };

    let handler = IsingHandler::new(params.clone());

    let mut scheduler = Scheduler::new();
    let mut local_types = HashMap::new();
    local_types.insert("A".to_string(), a_local);
    local_types.insert("B".to_string(), b_local);

    let mut initial_states = HashMap::new();
    initial_states.insert("A".to_string(), params.initial_state.clone());
    initial_states.insert("B".to_string(), params.initial_state.clone());

    scheduler.add_choreography(local_types, &initial_states);

    // 4. Run simulation.
    let trace = scheduler.run(100, &handler).expect("simulation succeeds");

    // 5. Validate.
    let equilibrium = [0.5, 0.5];
    let result = analysis::validate(&trace, &["A", "B"], &equilibrium);

    for check in &result.checks {
        eprintln!("  {}: {} - {}", check.name, check.passed, check.message);
    }
    assert!(result.passed, "all validation checks should pass");
}

#[test]
fn test_hamiltonian_2body_end_to_end() {
    let runner = require_lean();

    // 1. Construct Hamiltonian 2-body GlobalType:
    //    mu step.
    //      A -> B: position. B -> A: position.
    //      A -> B: force. B -> A: force.
    //      var step
    let g = GlobalType::mu(
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
    );

    // 2. Project via Lean.
    let json = global_to_json(&g);
    let roles = vec!["A".to_string(), "B".to_string()];
    let projections = runner.project(&json, &roles).expect("projection succeeds");

    let a_local = json_to_local(&projections["A"]).expect("parse A local type");
    let b_local = json_to_local(&projections["B"]).expect("parse B local type");

    // 3. Set up simulator.
    let params = HamiltonianParams {
        spring_constant: 1.0,
        mass: 1.0,
        dimensions: 1,
        initial_positions: vec![1.0, -1.0],
        initial_momenta: vec![0.0, 0.0],
        step_size: 0.01,
    };

    let handler = HamiltonianHandler::new(params.clone());

    let mut scheduler = Scheduler::new();
    let mut local_types = HashMap::new();
    local_types.insert("A".to_string(), a_local);
    local_types.insert("B".to_string(), b_local);

    // State per role: [position, momentum]
    let mut initial_states = HashMap::new();
    initial_states.insert("A".to_string(), vec![params.initial_positions[0], params.initial_momenta[0]]);
    initial_states.insert("B".to_string(), vec![params.initial_positions[1], params.initial_momenta[1]]);

    scheduler.add_choreography(local_types, &initial_states);

    // 4. Run simulation. Protocol has 4 steps per cycle (2 position + 2 force exchanges).
    //    To get 250 integration steps, run 1000 scheduler ticks.
    let trace = scheduler.run(1000, &handler).expect("simulation succeeds");

    // 5. Validate energy conservation.
    let energy_check = analysis::check_energy_conservation(
        &trace,
        &["A", "B"],
        params.mass,
        params.spring_constant,
    );
    eprintln!("  {}: {} - {}", energy_check.name, energy_check.passed, energy_check.message);
    assert!(energy_check.passed, "energy should be conserved");
}
