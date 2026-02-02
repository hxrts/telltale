//! Behavioral equivalence tests: lightweight scheduler vs VM.
//!
//! Verifies that both execution backends produce equivalent final states
//! for the same choreography and effect handler.

use std::collections::{BTreeMap, HashMap};

use telltale_simulator::ising::IsingHandler;
use telltale_simulator::material::MeanFieldParams;
use telltale_simulator::scheduler::Scheduler;
use telltale_simulator::vm_runner;
use telltale_types::{GlobalType, Label, LocalTypeR};

/// Build the standard 2-role Ising choreography.
fn ising_choreography() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::mu(
        "step",
        GlobalType::send(
            "A",
            "B",
            Label::new("concentration"),
            GlobalType::send(
                "B",
                "A",
                Label::new("concentration"),
                GlobalType::var("step"),
            ),
        ),
    );
    let local_a = LocalTypeR::mu(
        "step",
        LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(
                Label::new("concentration"),
                None,
                LocalTypeR::Recv {
                    partner: "B".into(),
                    branches: vec![(Label::new("concentration"), None, LocalTypeR::var("step"))],
                },
            )],
        },
    );
    let local_b = LocalTypeR::mu(
        "step",
        LocalTypeR::Recv {
            partner: "A".into(),
            branches: vec![(
                Label::new("concentration"),
                None,
                LocalTypeR::Send {
                    partner: "A".into(),
                    branches: vec![(Label::new("concentration"), None, LocalTypeR::var("step"))],
                },
            )],
        },
    );

    let mut locals = BTreeMap::new();
    locals.insert("A".to_string(), local_a);
    locals.insert("B".to_string(), local_b);
    (global, locals)
}

fn ising_params() -> MeanFieldParams {
    MeanFieldParams {
        beta: 0.5,
        species: vec!["up".into(), "down".into()],
        initial_state: vec![0.6, 0.4],
        step_size: 0.01,
    }
}

fn initial_states() -> HashMap<String, Vec<f64>> {
    let mut m = HashMap::new();
    m.insert("A".to_string(), vec![0.6, 0.4]);
    m.insert("B".to_string(), vec![0.6, 0.4]);
    m
}

#[test]
fn test_ising_lightweight_vs_vm_final_state() {
    let (global, locals) = ising_choreography();
    let params = ising_params();
    let init = initial_states();
    let steps = 100;

    // Run lightweight scheduler.
    let handler = IsingHandler::new(params.clone());
    let mut scheduler = Scheduler::new();
    scheduler.add_choreography(
        locals.iter().map(|(k, v)| (k.clone(), v.clone())).collect(),
        &init,
    );
    let lightweight_trace = scheduler.run(steps, &handler).expect("lightweight run");

    // Run VM.
    let vm_handler = IsingHandler::new(params);
    let vm_trace =
        vm_runner::run_vm(&locals, &global, &init, steps, &vm_handler).expect("vm run");

    // Compare final states.
    for role in &["A", "B"] {
        let lw_final = lightweight_trace
            .final_state(role)
            .expect("lightweight final");
        let vm_final = vm_trace.final_state(role).expect("vm final");

        assert_eq!(
            lw_final.len(),
            vm_final.len(),
            "state vector length mismatch for role {role}"
        );

        for (i, (lw, vm)) in lw_final.iter().zip(vm_final.iter()).enumerate() {
            assert!(
                (lw - vm).abs() < 0.05,
                "role {role} component {i}: lightweight={lw}, vm={vm}, diff={}",
                (lw - vm).abs()
            );
        }
    }
}
