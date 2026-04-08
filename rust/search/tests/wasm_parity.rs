#![allow(clippy::expect_used)]
//! Cross-target parity checks for the canonical search machine.

use std::collections::BTreeMap;

use telltale_search::{
    replay_observation, run_with_executor, EpsilonMilli, ReplayExpectation, SearchDomain,
    SearchFairnessAssumption, SearchMachine, SearchSchedulerProfile, SerialProposalExecutor,
};

#[cfg(target_arch = "wasm32")]
use wasm_bindgen_test::wasm_bindgen_test;

#[derive(Clone, Debug, Default)]
struct TestDomain {
    edges: BTreeMap<u8, Vec<(u8, &'static str, u64)>>,
    heuristics: BTreeMap<(u64, u8), u64>,
}

impl SearchDomain for TestDomain {
    type Node = u8;
    type EdgeMeta = &'static str;
    type Cost = u64;
    type GraphEpoch = u64;
    type SnapshotId = &'static str;
    type Error = &'static str;

    fn successors(
        &self,
        _epoch: &Self::GraphEpoch,
        node: &Self::Node,
        out: &mut Vec<(Self::Node, Self::EdgeMeta, Self::Cost)>,
    ) -> Result<(), Self::Error> {
        if let Some(edges) = self.edges.get(node) {
            out.extend(edges.iter().cloned());
        }
        Ok(())
    }

    fn heuristic(
        &self,
        epoch: &Self::GraphEpoch,
        node: &Self::Node,
        _goal: &Self::Node,
    ) -> Self::Cost {
        *self.heuristics.get(&(*epoch, *node)).unwrap_or(&0)
    }

    fn snapshot_id(&self, epoch: &Self::GraphEpoch) -> Self::SnapshotId {
        if *epoch == 1 {
            "epoch-1"
        } else {
            "epoch-2"
        }
    }
}

fn make_domain() -> TestDomain {
    let mut domain = TestDomain::default();
    domain.edges.insert(0, vec![(1, "0-1", 1), (2, "0-2", 1)]);
    domain.edges.insert(1, vec![(3, "1-3", 1)]);
    domain.edges.insert(2, vec![(3, "2-3", 1)]);
    domain.heuristics.insert((1, 1), 0);
    domain.heuristics.insert((1, 2), 0);
    domain
}

fn canonical_run() -> (
    telltale_search::SearchExecutionReport<u8, u64, u64>,
    telltale_search::SearchReplayArtifact<u8, u64, &'static str, u64>,
) {
    let mut machine = SearchMachine::new(make_domain(), 1, 0, 3, EpsilonMilli::one());
    run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        SearchSchedulerProfile::CanonicalSerial,
        1,
        vec![SearchFairnessAssumption::DeterministicSchedulerConfluence],
    )
    .expect("canonical run")
}

fn assert_serial_and_replay_contracts() {
    let (report, replay) = canonical_run();
    assert_eq!(report.observation.incumbent_cost, Some(2));
    assert_eq!(report.observation.graph_epoch_trace, vec![1]);
    let replayed = replay_observation(
        &replay,
        &ReplayExpectation {
            expected_epochs: vec![1],
            expected_phases: replay.rounds.iter().map(|round| round.phase).collect(),
            required_fairness: vec![SearchFairnessAssumption::DeterministicSchedulerConfluence],
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
