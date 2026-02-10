#![cfg(not(target_arch = "wasm32"))]
//! Scheduler-robustness invariants for strict Lean-observable behavior.

use std::collections::BTreeMap;

use telltale_vm::scheduler::{PriorityPolicy, SchedPolicy};
use telltale_vm::trace::normalize_trace;
use telltale_vm::vm::{ObsEvent, VMConfig, VM};

#[allow(dead_code, unreachable_pub)]
mod helpers;

use helpers::PassthroughHandler;

type CommEvent = (String, String, String, String);

fn canonical_comm_trace(vm: &VM) -> Vec<Vec<CommEvent>> {
    let mut per_session: BTreeMap<usize, Vec<CommEvent>> = BTreeMap::new();
    for event in normalize_trace(vm.trace()) {
        match event {
            ObsEvent::Sent {
                session,
                from,
                to,
                label,
                ..
            } => {
                per_session
                    .entry(session)
                    .or_default()
                    .push(("sent".to_string(), from, to, label))
            }
            ObsEvent::Received {
                session,
                from,
                to,
                label,
                ..
            } => {
                per_session
                    .entry(session)
                    .or_default()
                    .push(("recv".to_string(), from, to, label))
            }
            _ => {}
        }
    }

    let mut traces: Vec<Vec<CommEvent>> = per_session.into_values().collect();
    traces.sort();
    traces
}

fn run_for_policy(policy: SchedPolicy) -> Vec<Vec<CommEvent>> {
    let mut vm = VM::new(VMConfig {
        sched_policy: policy,
        ..VMConfig::default()
    });
    vm.load_choreography(&helpers::simple_send_recv_image("A", "B", "m1"))
        .expect("load image m1");
    vm.load_choreography(&helpers::simple_send_recv_image("A", "B", "m2"))
        .expect("load image m2");
    vm.run_concurrent(&PassthroughHandler, 256, 2)
        .expect("run under scheduler policy");
    canonical_comm_trace(&vm)
}

#[test]
fn scheduler_policies_preserve_normalized_comm_observations() {
    let baseline = run_for_policy(SchedPolicy::Cooperative);
    let policies = vec![
        SchedPolicy::RoundRobin,
        SchedPolicy::Priority(PriorityPolicy::Aging),
        SchedPolicy::ProgressAware,
    ];

    for policy in policies {
        let trace = run_for_policy(policy.clone());
        assert_eq!(
            baseline, trace,
            "normalized comm trace diverged under policy {policy:?}"
        );
    }
}
