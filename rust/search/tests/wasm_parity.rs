#![allow(clippy::expect_used, missing_docs)]
//! Cross-target parity checks for the canonical search machine.

mod support;

use std::collections::BTreeSet;

use support::FixtureDomain;
use telltale_search::{
    replay_observation, run_with_executor, EpsilonMilli, ReplayExpectation, SearchExecutionPolicy,
    SearchFairnessAssumption, SearchMachine, SearchRunConfig, SearchSchedulerProfile,
    SerialProposalExecutor,
};

type CanonicalRun = (
    telltale_search::SearchExecutionReport<u8, u64, u64>,
    telltale_search::SearchReplayArtifact<u8, u64, &'static str, u64>,
);

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::wasm_bindgen_test;

fn make_domain() -> FixtureDomain {
    let mut domain = FixtureDomain::default();
    domain.edge(0, 1, "0-1", 1);
    domain.edge(0, 2, "0-2", 1);
    domain.edge(1, 3, "1-3", 1);
    domain.edge(2, 3, "2-3", 1);
    domain.heuristic_value(1, 1, 0);
    domain.heuristic_value(1, 2, 0);
    domain
}

fn canonical_run() -> CanonicalRun {
    let mut machine = SearchMachine::new(make_domain(), 1, 0, 3, EpsilonMilli::one());
    run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        SearchRunConfig::new(
            SearchExecutionPolicy::new(SearchSchedulerProfile::CanonicalSerial, 1),
            BTreeSet::from([SearchFairnessAssumption::DeterministicSchedulerConfluence]),
        ),
    )
    .expect("canonical run")
}

fn assert_serial_and_replay_contracts() {
    let (report, replay) = canonical_run();
    assert_eq!(report.observation.selected_result_cost, Some(2));
    assert_eq!(report.observation.graph_epoch_trace, vec![1]);
    let replayed = replay_observation(
        &replay,
        &ReplayExpectation {
            expected_epochs: vec![1],
            expected_snapshots: replay
                .rounds
                .iter()
                .map(|round| round.snapshot_id)
                .collect(),
            expected_phases: replay.rounds.iter().map(|round| round.phase).collect(),
            expected_batch_nodes: replay
                .rounds
                .iter()
                .map(|round| round.batch_nodes.clone())
                .collect(),
            required_fairness: BTreeSet::from([
                SearchFairnessAssumption::DeterministicSchedulerConfluence,
            ]),
        },
    )
    .expect("replay must succeed");
    assert_eq!(replayed, report.observation);
}

#[test]
fn native_serial_and_replay_parity_hold() {
    assert_serial_and_replay_contracts();
}

#[cfg(target_arch = "wasm32")]
#[wasm_bindgen_test]
fn wasm_serial_and_replay_parity_hold() {
    assert_serial_and_replay_contracts();
}
