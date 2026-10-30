#![allow(missing_docs)]
//! Deterministic LocalTypeR trace corpus tests.
//!
//! These tests run on both native and WASM targets using wasm_bindgen_test's
//! `unsupported = test` fallback.

use std::collections::BTreeMap;

use wasm_bindgen_test::wasm_bindgen_test;

use telltale_machine::coroutine::Value;
use telltale_machine::model::effects::{EffectFailure, EffectHandler, EffectResult};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::trace::normalize_trace;
use telltale_machine::{ObsEvent, ProtocolMachine, ProtocolMachineConfig};
use telltale_types::{GlobalType, Label, LocalTypeR};

struct NoOpHandler;

type TraceRow = (u64, String, String, String, String);

impl EffectHandler for NoOpHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Unit)
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

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }
}

fn run_trace(locals: &BTreeMap<String, LocalTypeR>, global: &GlobalType) -> Vec<TraceRow> {
    let image = CodeImage::from_local_types(locals, global);
    let handler = NoOpHandler;
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine.load_choreography(&image).unwrap();
    machine.run(&handler, 200).unwrap();

    normalize_trace(machine.trace())
        .iter()
        .filter_map(|ev| match ev {
            ObsEvent::Sent {
                tick,
                from,
                to,
                label,
                ..
            } => Some((
                *tick,
                "sent".into(),
                from.clone(),
                to.clone(),
                label.clone(),
            )),
            ObsEvent::Received {
                tick,
                from,
                to,
                label,
                ..
            } => Some((
                *tick,
                "recv".into(),
                from.clone(),
                to.clone(),
                label.clone(),
            )),
            _ => None,
        })
        .collect()
}

#[wasm_bindgen_test(unsupported = test)]
fn test_trace_corpus_send_recv() {
    let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
    let mut locals = BTreeMap::new();
    locals.insert(
        "A".to_string(),
        LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );
    locals.insert(
        "B".to_string(),
        LocalTypeR::Recv {
            partner: "A".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        },
    );

    let trace = run_trace(&locals, &global);

    let expected = vec![
        (1, "sent".into(), "A".into(), "B".into(), "msg".into()),
        (2, "recv".into(), "A".into(), "B".into(), "msg".into()),
    ];

    assert_eq!(trace, expected);
}

fn row(tick: u64, kind: &str, from: &str, to: &str, label: &str) -> TraceRow {
    (tick, kind.into(), from.into(), to.into(), label.into())
}

/// Recursive: `mu X. A->B: tick; A->B: {stop: end, continue: X}`. The
/// local-type compiler offers the first branch, so the loop unfolds once and
/// terminates.
#[wasm_bindgen_test(unsupported = test)]
fn test_trace_corpus_bounded_loop() {
    let choice = |end: LocalTypeR, var: LocalTypeR| {
        vec![
            (Label::new("stop"), None, end),
            (Label::new("continue"), None, var),
        ]
    };
    let global = GlobalType::mu(
        "X",
        GlobalType::send(
            "A",
            "B",
            Label::new("tick"),
            GlobalType::comm(
                "A",
                "B",
                vec![
                    (Label::new("stop"), GlobalType::End),
                    (Label::new("continue"), GlobalType::var("X")),
                ],
            ),
        ),
    );
    let mut locals = BTreeMap::new();
    locals.insert(
        "A".to_string(),
        LocalTypeR::mu(
            "X",
            LocalTypeR::send(
                "B",
                Label::new("tick"),
                LocalTypeR::send_choice("B", choice(LocalTypeR::End, LocalTypeR::var("X"))),
            ),
        ),
    );
    locals.insert(
        "B".to_string(),
        LocalTypeR::mu(
            "X",
            LocalTypeR::recv(
                "A",
                Label::new("tick"),
                LocalTypeR::recv_choice("A", choice(LocalTypeR::End, LocalTypeR::var("X"))),
            ),
        ),
    );

    let trace = run_trace(&locals, &global);
    let expected = vec![
        row(1, "sent", "A", "B", "tick"),
        row(2, "recv", "A", "B", "tick"),
        row(3, "sent", "A", "B", "stop"),
        // External choice on B consumes one extra scheduler tick.
        row(5, "recv", "A", "B", "stop"),
    ];
    assert_eq!(trace, expected);
}

/// Asynchronous: `A->B: m1; C->D: m2` with disjoint participants.
#[wasm_bindgen_test(unsupported = test)]
fn test_trace_corpus_independent_pairs() {
    let global = GlobalType::send(
        "A",
        "B",
        Label::new("m1"),
        GlobalType::send("C", "D", Label::new("m2"), GlobalType::End),
    );
    let mut locals = BTreeMap::new();
    locals.insert(
        "A".to_string(),
        LocalTypeR::send("B", Label::new("m1"), LocalTypeR::End),
    );
    locals.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new("m1"), LocalTypeR::End),
    );
    locals.insert(
        "C".to_string(),
        LocalTypeR::send("D", Label::new("m2"), LocalTypeR::End),
    );
    locals.insert(
        "D".to_string(),
        LocalTypeR::recv("C", Label::new("m2"), LocalTypeR::End),
    );

    let trace = run_trace(&locals, &global);
    let expected = vec![
        row(1, "sent", "A", "B", "m1"),
        row(2, "recv", "A", "B", "m1"),
        row(3, "sent", "C", "D", "m2"),
        row(4, "recv", "C", "D", "m2"),
    ];
    assert_eq!(trace, expected);
}

/// Asynchronous fan-out: `A->B: x; A->C: y`.
#[wasm_bindgen_test(unsupported = test)]
fn test_trace_corpus_fan_out() {
    let global = GlobalType::send(
        "A",
        "B",
        Label::new("x"),
        GlobalType::send("A", "C", Label::new("y"), GlobalType::End),
    );
    let mut locals = BTreeMap::new();
    locals.insert(
        "A".to_string(),
        LocalTypeR::send(
            "B",
            Label::new("x"),
            LocalTypeR::send("C", Label::new("y"), LocalTypeR::End),
        ),
    );
    locals.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new("x"), LocalTypeR::End),
    );
    locals.insert(
        "C".to_string(),
        LocalTypeR::recv("A", Label::new("y"), LocalTypeR::End),
    );

    let trace = run_trace(&locals, &global);
    let expected = vec![
        row(1, "sent", "A", "B", "x"),
        row(2, "recv", "A", "B", "x"),
        row(3, "sent", "A", "C", "y"),
        row(4, "recv", "A", "C", "y"),
    ];
    assert_eq!(trace, expected);
}
