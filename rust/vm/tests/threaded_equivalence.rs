//! Threaded vs cooperative VM equivalence tests.

#![cfg(feature = "multi-thread")]

#[allow(dead_code, unreachable_pub)]
mod helpers;

use std::collections::BTreeMap;

use helpers::{
    choice_image, recursive_send_recv_image, simple_send_recv_image, PassthroughHandler,
};
use telltale_vm::threaded::ThreadedVM;
use telltale_vm::vm::{ObsEvent, VMConfig, VM};

type Normalized = (String, String, String, String);

fn normalize_event(ev: &ObsEvent) -> Option<(usize, Normalized)> {
    match ev {
        ObsEvent::Sent {
            session,
            from,
            to,
            label,
            ..
        } => Some((
            *session,
            ("sent".into(), from.clone(), to.clone(), label.clone()),
        )),
        ObsEvent::Received {
            session,
            from,
            to,
            label,
            ..
        } => Some((
            *session,
            ("recv".into(), from.clone(), to.clone(), label.clone()),
        )),
        _ => None,
    }
}

fn per_session(trace: &[ObsEvent]) -> BTreeMap<usize, Vec<Normalized>> {
    let mut map: BTreeMap<usize, Vec<Normalized>> = BTreeMap::new();
    for ev in trace {
        if let Some((sid, norm)) = normalize_event(ev) {
            map.entry(sid).or_default().push(norm);
        }
    }
    map
}

fn run_cooperative(
    images: &[telltale_vm::loader::CodeImage],
    concurrency: usize,
) -> BTreeMap<usize, Vec<Normalized>> {
    let handler = PassthroughHandler;
    let mut vm = VM::new(VMConfig::default());
    for image in images {
        vm.load_choreography(image).expect("load image");
    }
    vm.run_concurrent(&handler, 200, concurrency)
        .expect("cooperative run");
    per_session(vm.trace())
}

fn run_threaded(
    images: &[telltale_vm::loader::CodeImage],
    workers: usize,
) -> BTreeMap<usize, Vec<Normalized>> {
    let handler = PassthroughHandler;
    let mut vm = ThreadedVM::with_workers(VMConfig::default(), workers);
    for image in images {
        vm.load_choreography(image).expect("load image");
    }
    vm.run(&handler, 200).expect("threaded run");
    per_session(vm.trace())
}

#[test]
fn test_threaded_matches_cooperative() {
    let images = vec![
        simple_send_recv_image("A", "B", "msg"),
        choice_image("A", "B", &["yes", "no"]),
        recursive_send_recv_image("A", "B", "tick"),
    ];

    let total_coros: usize = images.iter().map(|img| img.roles().len()).sum();
    let workers = total_coros.max(1);

    let coop = run_cooperative(&images, workers);
    let threaded = run_threaded(&images, workers);

    assert_eq!(coop, threaded, "per-session traces should match");
}
