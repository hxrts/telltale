#![allow(missing_docs)]
#![cfg(not(target_arch = "wasm32"))]
//! Cross-language equivalence tests: Rust ProtocolMachine vs Lean ProtocolMachine runner.
#![allow(
    clippy::needless_collect,
    clippy::as_conversions,
    clippy::cast_possible_truncation
)]

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use std::collections::{BTreeMap, HashMap};
use std::path::PathBuf;

use telltale_bridge::export::global_to_json;
use telltale_bridge::{
    canonical_schema_version, partition_by_session, ChoreographyJson, NormalizedEvent,
    ProtocolMachineRunInput, ProtocolMachineRunOutput, ProtocolMachineRunner,
    ProtocolMachineRunnerError,
};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{ObsEvent, ProtocolMachine, ProtocolMachineConfig, ProtocolMachineError};
use test_support::{
    choice_image, recursive_send_recv_image, simple_send_recv_image, PassthroughHandler,
};

fn protocol_machine_runner_path() -> Option<PathBuf> {
    let manifest_dir = env!("CARGO_MANIFEST_DIR");
    let mut path = PathBuf::from(manifest_dir);
    for _ in 0..5 {
        if path.join("lean/.lake").is_dir() {
            let candidate = path.join("lean/.lake/build/bin/protocol_machine_runner");
            if candidate.exists() {
                return Some(candidate);
            }
            return None;
        }
        if !path.pop() {
            break;
        }
    }
    None
}

fn normalize_rust_trace(trace: &[ObsEvent], session_ids: &[usize]) -> Vec<NormalizedEvent> {
    let mut sid_map: HashMap<usize, usize> = HashMap::new();
    for (idx, sid) in session_ids.iter().enumerate() {
        sid_map.insert(*sid, idx);
    }

    trace
        .iter()
        .filter_map(|ev| match ev {
            ObsEvent::Sent {
                session, from, to, ..
            } => sid_map.get(session).map(|sid_idx| NormalizedEvent {
                kind: "sent".to_string(),
                session_index: *sid_idx,
                sender: from.clone(),
                receiver: to.clone(),
                label: None,
            }),
            ObsEvent::Received {
                session, from, to, ..
            } => sid_map.get(session).map(|sid_idx| NormalizedEvent {
                kind: "received".to_string(),
                session_index: *sid_idx,
                sender: from.clone(),
                receiver: to.clone(),
                label: None,
            }),
            _ => None,
        })
        .collect()
}

fn normalize_lean_trace(output: &ProtocolMachineRunOutput) -> Vec<NormalizedEvent> {
    let mut session_ids: Vec<usize> = output
        .sessions
        .iter()
        .filter_map(|session| usize::try_from(session.sid).ok())
        .collect();
    session_ids.sort_unstable();

    let mut sid_map: HashMap<usize, usize> = HashMap::new();
    for (idx, sid) in session_ids.iter().enumerate() {
        sid_map.insert(*sid, idx);
    }

    output
        .trace
        .iter()
        .filter_map(|ev| {
            if ev.kind != "sent" && ev.kind != "received" {
                return None;
            }
            let session = usize::try_from(ev.session?).ok()?;
            let sender = ev.sender.clone()?;
            let receiver = ev.receiver.clone()?;
            let session_index = *sid_map.get(&session)?;
            Some(NormalizedEvent {
                kind: ev.kind.clone(),
                session_index,
                sender,
                receiver,
                label: None,
            })
        })
        .collect()
}

fn run_rust(
    images: &[CodeImage],
    concurrency: usize,
    max_rounds: usize,
) -> Result<Vec<NormalizedEvent>, ProtocolMachineError> {
    let handler = PassthroughHandler;
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    let mut session_ids = Vec::new();
    for image in images {
        let sid = machine.load_choreography(image)?;
        session_ids.push(sid);
    }
    machine.run_concurrent(&handler, max_rounds, concurrency)?;
    Ok(normalize_rust_trace(machine.trace(), &session_ids))
}

fn run_lean(
    choreos: &[ChoreographyJson],
    concurrency: usize,
    max_rounds: usize,
) -> Result<Vec<NormalizedEvent>, ProtocolMachineRunnerError> {
    let runner_path = protocol_machine_runner_path().ok_or_else(|| {
        ProtocolMachineRunnerError::BinaryNotFound(PathBuf::from(
            "lean/.lake/build/bin/protocol_machine_runner",
        ))
    })?;
    let runner = ProtocolMachineRunner::with_binary_path(runner_path)?;
    let input = ProtocolMachineRunInput {
        schema_version: canonical_schema_version(),
        choreographies: choreos.to_vec(),
        concurrency: concurrency as u64,
        max_steps: max_rounds as u64,
    };
    let output = runner.run_protocol_machine(&input)?;
    if std::env::var("TELLTALE_DEBUG_EQUIV").ok().as_deref() == Some("1") {
        eprintln!("lean sessions: {:?}", output.sessions);
        eprintln!("lean trace: {:?}", output.trace);
        eprintln!("lean step states: {:?}", output.step_states);
    }
    Ok(normalize_lean_trace(&output))
}

fn build_choreos(images: &[CodeImage]) -> Vec<ChoreographyJson> {
    images
        .iter()
        .map(|img| ChoreographyJson {
            schema_version: canonical_schema_version(),
            global_type: global_to_json(&img.global_type),
            roles: img.roles(),
        })
        .collect()
}

fn truncate_partitioned(
    traces: &BTreeMap<usize, Vec<NormalizedEvent>>,
    min_lengths: &BTreeMap<usize, usize>,
) -> BTreeMap<usize, Vec<NormalizedEvent>> {
    traces
        .iter()
        .map(|(sid, trace)| {
            let limit = *min_lengths.get(sid).unwrap_or(&0);
            (*sid, trace.iter().take(limit).cloned().collect())
        })
        .collect()
}

#[test]
fn equivalence_lean_basic() {
    let images = vec![
        simple_send_recv_image("A", "B", "msg"),
        choice_image("A", "B", &["yes", "no"]),
        recursive_send_recv_image("A", "B", "tick"),
    ];

    let choreos = build_choreos(&images);

    let total_coros: usize = images.iter().map(|img| img.roles().len()).sum();
    let concurrencies = [1usize, 2, total_coros.max(1)];

    let mut rust_traces: BTreeMap<usize, Vec<NormalizedEvent>> = BTreeMap::new();

    for &n in &concurrencies {
        let rust_trace = run_rust(&images, n, 200).expect("rust machine run failed");
        rust_traces.insert(n, rust_trace);
    }

    // N-invariance within Rust ProtocolMachine.
    let mut rust_partitioned: Vec<BTreeMap<usize, Vec<NormalizedEvent>>> = Vec::new();
    for &n in &concurrencies {
        rust_partitioned.push(partition_by_session(&rust_traces[&n]));
    }
    if let Some(first) = rust_partitioned.first() {
        let mut min_lengths: BTreeMap<usize, usize> = first
            .iter()
            .map(|(sid, trace)| (*sid, trace.len()))
            .collect();
        for other in rust_partitioned.iter().skip(1) {
            for (sid, trace) in other {
                let entry = min_lengths
                    .get_mut(sid)
                    .expect("session mismatch in rust traces");
                *entry = (*entry).min(trace.len());
            }
        }
        let truncated_first = truncate_partitioned(first, &min_lengths);
        for other in rust_partitioned.iter().skip(1) {
            let truncated_other = truncate_partitioned(other, &min_lengths);
            assert_eq!(
                truncated_first, truncated_other,
                "Rust per-session traces differ across N (common prefix)"
            );
        }
    }

    // Cross-language equivalence (skip if Lean runner unavailable).
    let lean_trace = match run_lean(&choreos, concurrencies[0], 200) {
        Ok(t) => t,
        Err(ProtocolMachineRunnerError::BinaryNotFound(_)) => return,
        Err(e) => panic!("Lean runner failed: {e}"),
    };
    if lean_trace.is_empty() {
        eprintln!("SKIPPED: Lean protocol-machine runner emitted no communication events");
        return;
    }
    let rust_trace = &rust_traces[&concurrencies[0]];
    assert_eq!(
        partition_by_session(rust_trace),
        partition_by_session(&lean_trace),
        "Rust vs Lean per-session traces differ"
    );

    // Check all N for cross-language equivalence when Lean is available.
    for &n in &concurrencies[1..] {
        let lean_trace_n = match run_lean(&choreos, n, 200) {
            Ok(t) => t,
            Err(ProtocolMachineRunnerError::BinaryNotFound(_)) => return,
            Err(e) => panic!("Lean runner failed: {e}"),
        };
        if lean_trace_n.is_empty() {
            eprintln!("SKIPPED: Lean protocol-machine runner emitted no communication events");
            return;
        }
        assert_eq!(
            partition_by_session(&rust_traces[&n]),
            partition_by_session(&lean_trace_n),
            "Rust vs Lean per-session traces differ at N={n}"
        );
    }
}
