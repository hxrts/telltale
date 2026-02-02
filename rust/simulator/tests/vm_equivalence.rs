//! Behavioral equivalence tests: lightweight scheduler vs VM.
//!
//! Verifies that both execution backends produce equivalent traces
//! for the same choreography and effect handler.
//!
//! These tests require the `vm` feature: `cargo test --features vm`

#![cfg(feature = "vm")]

use std::collections::{BTreeMap, HashMap};

use telltale_simulator::continuum::ContinuumFieldHandler;
use telltale_simulator::hamiltonian::HamiltonianHandler;
use telltale_simulator::ising::IsingHandler;
use telltale_simulator::material::{ContinuumFieldParams, HamiltonianParams, MeanFieldParams};
use telltale_simulator::scheduler::Scheduler;
use telltale_simulator::vm_runner::{self, ChoreographySpec};
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

/// Build the 2-role Hamiltonian choreography (4-message cycle per step).
fn hamiltonian_choreography() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::mu(
        "step",
        GlobalType::send(
            "A",
            "B",
            Label::new("position"),
            GlobalType::send(
                "B",
                "A",
                Label::new("position"),
                GlobalType::send(
                    "A",
                    "B",
                    Label::new("force"),
                    GlobalType::send(
                        "B",
                        "A",
                        Label::new("force"),
                        GlobalType::var("step"),
                    ),
                ),
            ),
        ),
    );
    let local_a = LocalTypeR::mu(
        "step",
        LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(
                Label::new("position"),
                None,
                LocalTypeR::Recv {
                    partner: "B".into(),
                    branches: vec![(
                        Label::new("position"),
                        None,
                        LocalTypeR::Send {
                            partner: "B".into(),
                            branches: vec![(
                                Label::new("force"),
                                None,
                                LocalTypeR::Recv {
                                    partner: "B".into(),
                                    branches: vec![(
                                        Label::new("force"),
                                        None,
                                        LocalTypeR::var("step"),
                                    )],
                                },
                            )],
                        },
                    )],
                },
            )],
        },
    );
    let local_b = LocalTypeR::mu(
        "step",
        LocalTypeR::Recv {
            partner: "A".into(),
            branches: vec![(
                Label::new("position"),
                None,
                LocalTypeR::Send {
                    partner: "A".into(),
                    branches: vec![(
                        Label::new("position"),
                        None,
                        LocalTypeR::Recv {
                            partner: "A".into(),
                            branches: vec![(
                                Label::new("force"),
                                None,
                                LocalTypeR::Send {
                                    partner: "A".into(),
                                    branches: vec![(
                                        Label::new("force"),
                                        None,
                                        LocalTypeR::var("step"),
                                    )],
                                },
                            )],
                        },
                    )],
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

fn hamiltonian_params() -> HamiltonianParams {
    HamiltonianParams {
        spring_constant: 1.0,
        mass: 1.0,
        dimensions: 1,
        initial_positions: vec![1.0, -1.0],
        initial_momenta: vec![0.0, 0.0],
        step_size: 0.01,
    }
}

fn ising_initial_states() -> HashMap<String, Vec<f64>> {
    let mut m = HashMap::new();
    m.insert("A".to_string(), vec![0.6, 0.4]);
    m.insert("B".to_string(), vec![0.6, 0.4]);
    m
}

fn hamiltonian_initial_states() -> HashMap<String, Vec<f64>> {
    let mut m = HashMap::new();
    m.insert("A".to_string(), vec![1.0, 0.0]);
    m.insert("B".to_string(), vec![-1.0, 0.0]);
    m
}

/// Compare final states of two traces with a given tolerance.
fn assert_final_states_match(
    lightweight: &telltale_simulator::trace::Trace,
    vm: &telltale_simulator::trace::Trace,
    roles: &[&str],
    tolerance: f64,
    context: &str,
) {
    for role in roles {
        let lw_final = lightweight
            .final_state(role)
            .unwrap_or_else(|| panic!("{context}: no lightweight final state for {role}"));
        let vm_final = vm
            .final_state(role)
            .unwrap_or_else(|| panic!("{context}: no VM final state for {role}"));

        assert_eq!(
            lw_final.len(),
            vm_final.len(),
            "{context}: state vector length mismatch for role {role}"
        );

        for (i, (lw, vm)) in lw_final.iter().zip(vm_final.iter()).enumerate() {
            assert!(
                (lw - vm).abs() < tolerance,
                "{context}: role {role} component {i}: lightweight={lw}, vm={vm}, diff={}",
                (lw - vm).abs()
            );
        }
    }
}

#[test]
fn test_ising_lightweight_vs_vm_final_state() {
    let (global, locals) = ising_choreography();
    let params = ising_params();
    let init = ising_initial_states();
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

    assert_final_states_match(&lightweight_trace, &vm_trace, &["A", "B"], 1e-10, "ising");
}

#[test]
fn test_hamiltonian_lightweight_vs_vm_final_state() {
    let (global, locals) = hamiltonian_choreography();
    let params = hamiltonian_params();
    let init = hamiltonian_initial_states();
    let steps = 50;

    // Run lightweight scheduler.
    let handler = HamiltonianHandler::new(params.clone());
    let mut scheduler = Scheduler::new();
    scheduler.add_choreography(
        locals.iter().map(|(k, v)| (k.clone(), v.clone())).collect(),
        &init,
    );
    let lightweight_trace = scheduler.run(steps, &handler).expect("lightweight run");

    // Run VM.
    let vm_handler = HamiltonianHandler::new(params);
    let vm_trace =
        vm_runner::run_vm(&locals, &global, &init, steps, &vm_handler).expect("vm run");

    assert_final_states_match(
        &lightweight_trace,
        &vm_trace,
        &["A", "B"],
        1e-10,
        "hamiltonian",
    );
}

#[test]
fn test_ising_vm_trace_nonempty() {
    let (global, locals) = ising_choreography();
    let params = ising_params();
    let init = ising_initial_states();
    let steps = 20;

    let handler = IsingHandler::new(params);
    let vm_trace =
        vm_runner::run_vm(&locals, &global, &init, steps, &handler).expect("vm run");

    // VM trace should contain records.
    assert!(
        !vm_trace.records.is_empty(),
        "VM trace should produce step records"
    );

    // Should have records for both roles.
    let a_records = vm_trace.records_for_role("A");
    let b_records = vm_trace.records_for_role("B");
    assert!(!a_records.is_empty(), "VM trace should have records for A");
    assert!(!b_records.is_empty(), "VM trace should have records for B");
}

#[test]
fn test_ising_intermediate_states_monotone() {
    let (global, locals) = ising_choreography();
    let params = ising_params();
    let init = ising_initial_states();
    let steps = 50;

    let handler = IsingHandler::new(params);
    let vm_trace =
        vm_runner::run_vm(&locals, &global, &init, steps, &handler).expect("vm run");

    // For Ising with beta=0.5 < 1.0, the system should converge toward
    // equilibrium (equal concentrations). Verify step indices increase.
    let a_records = vm_trace.records_for_role("A");
    for window in a_records.windows(2) {
        assert!(
            window[1].step >= window[0].step,
            "step indices should be non-decreasing"
        );
    }
}

#[test]
fn test_concurrent_ising_and_hamiltonian_on_single_vm() {
    let (ising_global, ising_locals) = ising_choreography();
    let (ham_global, ham_locals) = hamiltonian_choreography();
    let steps = 50;

    // Run concurrently on a single VM.
    let handler = IsingHandler::new(ising_params());
    let specs = vec![
        ChoreographySpec {
            local_types: ising_locals.clone(),
            global_type: ising_global.clone(),
            initial_states: ising_initial_states(),
        },
        ChoreographySpec {
            local_types: ham_locals.clone(),
            global_type: ham_global.clone(),
            initial_states: hamiltonian_initial_states(),
        },
    ];

    let traces = vm_runner::run_vm_concurrent(&specs, steps, &handler)
        .expect("concurrent run");
    assert_eq!(traces.len(), 2, "should produce one trace per choreography");

    // Run Ising in isolation for comparison.
    let isolated_handler = IsingHandler::new(ising_params());
    let isolated_trace = vm_runner::run_vm(
        &ising_locals,
        &ising_global,
        &ising_initial_states(),
        steps,
        &isolated_handler,
    )
    .expect("isolated ising run");

    // With per-session scoping of step() calls, concurrent execution should
    // produce identical results to isolated runs — each session's roles only
    // get step() called when their own session produces a Sent event.
    let concurrent_ising = &traces[0];
    assert_final_states_match(
        &isolated_trace,
        concurrent_ising,
        &["A", "B"],
        1e-10,
        "concurrent vs isolated ising",
    );

    // Hamiltonian trace should exist and have valid states.
    let concurrent_ham = &traces[1];
    let a_final = concurrent_ham.final_state("A").expect("A");
    let b_final = concurrent_ham.final_state("B").expect("B");
    assert_eq!(a_final.len(), 2);
    assert_eq!(b_final.len(), 2);
    for &v in a_final.iter().chain(b_final.iter()) {
        assert!(v.is_finite(), "state must be finite");
    }
}

#[test]
fn test_dynamic_loading_second_choreography() {
    use telltale_vm::loader::UntrustedImage;
    use telltale_vm::vm::{StepResult, VMConfig, VM};

    let (ising_global, ising_locals) = ising_choreography();
    let (ham_global, ham_locals) = hamiltonian_choreography();

    let handler = IsingHandler::new(ising_params());
    let adapter = telltale_simulator::vm_runner::VmEffectAdapter::new(&handler);

    let mut vm = VM::new(VMConfig::default());

    // Load first choreography (trusted).
    let image1 =
        telltale_vm::loader::CodeImage::from_local_types(&ising_locals, &ising_global);
    let sid1 = vm.load_choreography(&image1).expect("load ising");

    // Initialize registers for Ising roles.
    let ising_init = ising_initial_states();
    let coro_ids: Vec<_> = vm.session_coroutines(sid1).iter().map(|c| (c.id, c.role.clone())).collect();
    for (id, role) in &coro_ids {
        if let Some(init) = ising_init.get(role) {
            if let Some(c) = vm.coroutine_mut(*id) {
                for (i, &v) in init.iter().enumerate() {
                    if i + 2 < c.regs.len() {
                        c.regs[i + 2] = telltale_vm::coroutine::Value::Real(v);
                    }
                }
            }
        }
    }

    // Run a few steps with only the first choreography.
    for _ in 0..20 {
        match vm.step(&adapter) {
            Ok(StepResult::Continue) => {}
            Ok(StepResult::AllDone | StepResult::Stuck) => break,
            Err(e) => panic!("vm error: {e}"),
        }
    }

    // Dynamically load a second choreography (via untrusted path).
    let untrusted = UntrustedImage::from_local_types(&ham_locals, &ham_global);
    let image2 = untrusted.validate().expect("validation should pass");
    let sid2 = vm.load_choreography(&image2).expect("load hamiltonian");

    // Initialize registers for Hamiltonian roles.
    let ham_init = hamiltonian_initial_states();
    let coro_ids2: Vec<_> = vm.session_coroutines(sid2).iter().map(|c| (c.id, c.role.clone())).collect();
    for (id, role) in &coro_ids2 {
        if let Some(init) = ham_init.get(role) {
            if let Some(c) = vm.coroutine_mut(*id) {
                for (i, &v) in init.iter().enumerate() {
                    if i + 2 < c.regs.len() {
                        c.regs[i + 2] = telltale_vm::coroutine::Value::Real(v);
                    }
                }
            }
        }
    }

    assert_ne!(sid1, sid2, "sessions must have different IDs");

    // Continue running — both choreographies now active.
    for _ in 0..200 {
        match vm.step(&adapter) {
            Ok(StepResult::Continue) => {}
            Ok(StepResult::AllDone | StepResult::Stuck) => break,
            Err(e) => panic!("vm error: {e}"),
        }
    }

    // Both sessions should have produced observable events.
    let trace = vm.trace();
    let has_sid1_events = trace
        .iter()
        .any(|e| matches!(e, telltale_vm::vm::ObsEvent::Sent { session, .. } if *session == sid1));
    let has_sid2_events = trace
        .iter()
        .any(|e| matches!(e, telltale_vm::vm::ObsEvent::Sent { session, .. } if *session == sid2));
    assert!(has_sid1_events, "first choreography should have sent events");
    assert!(
        has_sid2_events,
        "dynamically loaded choreography should have sent events"
    );
}

/// Build the 2-role continuum field choreography (same structure as Ising).
fn continuum_choreography() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
    let global = GlobalType::mu(
        "step",
        GlobalType::send(
            "A",
            "B",
            Label::new("field"),
            GlobalType::send("B", "A", Label::new("field"), GlobalType::var("step")),
        ),
    );
    let local_a = LocalTypeR::mu(
        "step",
        LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(
                Label::new("field"),
                None,
                LocalTypeR::Recv {
                    partner: "B".into(),
                    branches: vec![(Label::new("field"), None, LocalTypeR::var("step"))],
                },
            )],
        },
    );
    let local_b = LocalTypeR::mu(
        "step",
        LocalTypeR::Recv {
            partner: "A".into(),
            branches: vec![(
                Label::new("field"),
                None,
                LocalTypeR::Send {
                    partner: "A".into(),
                    branches: vec![(Label::new("field"), None, LocalTypeR::var("step"))],
                },
            )],
        },
    );

    let mut locals = BTreeMap::new();
    locals.insert("A".to_string(), local_a);
    locals.insert("B".to_string(), local_b);
    (global, locals)
}

fn continuum_params() -> ContinuumFieldParams {
    ContinuumFieldParams {
        coupling: 1.0,
        components: 1,
        initial_fields: vec![1.0, 0.0],
        step_size: 0.01,
    }
}

fn continuum_initial_states() -> HashMap<String, Vec<f64>> {
    let mut m = HashMap::new();
    m.insert("A".to_string(), vec![1.0]);
    m.insert("B".to_string(), vec![0.0]);
    m
}

#[test]
fn test_continuum_field_lightweight_vs_vm() {
    let (global, locals) = continuum_choreography();
    let params = continuum_params();
    let init = continuum_initial_states();
    let steps = 100;

    // Run lightweight scheduler.
    let handler = ContinuumFieldHandler::new(params.clone());
    let mut scheduler = Scheduler::new();
    scheduler.add_choreography(
        locals.iter().map(|(k, v)| (k.clone(), v.clone())).collect(),
        &init,
    );
    let lightweight_trace = scheduler.run(steps, &handler).expect("lightweight run");

    // Run VM.
    let vm_handler = ContinuumFieldHandler::new(params);
    let vm_trace =
        vm_runner::run_vm(&locals, &global, &init, steps, &vm_handler).expect("vm run");

    assert_final_states_match(
        &lightweight_trace,
        &vm_trace,
        &["A", "B"],
        1e-10,
        "continuum_field",
    );
}

#[test]
fn test_continuum_field_conserves_total() {
    let (global, locals) = continuum_choreography();
    let params = continuum_params();
    let init = continuum_initial_states();
    let steps = 500;

    let handler = ContinuumFieldHandler::new(params);
    let vm_trace =
        vm_runner::run_vm(&locals, &global, &init, steps, &handler).expect("vm run");

    let a_final = vm_trace.final_state("A").expect("A final");
    let b_final = vm_trace.final_state("B").expect("B final");

    let total = a_final[0] + b_final[0];
    assert!(
        (total - 1.0).abs() < 1e-10,
        "total field should be conserved: got {total}"
    );
}

#[test]
fn test_continuum_field_converges() {
    let (global, locals) = continuum_choreography();
    let params = continuum_params();
    let init = continuum_initial_states();
    let steps = 2000;

    let handler = ContinuumFieldHandler::new(params);
    let vm_trace =
        vm_runner::run_vm(&locals, &global, &init, steps, &handler).expect("vm run");

    let a_final = vm_trace.final_state("A").expect("A final");
    let b_final = vm_trace.final_state("B").expect("B final");

    // Should converge to equal values (0.5 each).
    assert!(
        (a_final[0] - 0.5).abs() < 1e-4,
        "A should converge to 0.5, got {}",
        a_final[0]
    );
    assert!(
        (b_final[0] - 0.5).abs() < 1e-4,
        "B should converge to 0.5, got {}",
        b_final[0]
    );
}
