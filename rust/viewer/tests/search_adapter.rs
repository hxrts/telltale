#![allow(clippy::expect_used)]
//! Integration checks for the optional `telltale-search` viewer adapter.

use std::collections::{BTreeMap, BTreeSet};

use telltale_search::{
    run_with_executor, EpsilonMilli, SearchDomain, SearchFairnessAssumption, SearchMachine,
    SearchRunConfig, SearchSchedulerProfile, SerialProposalExecutor,
};
use telltale_viewer::project_search_artifacts;

#[derive(Clone, Debug, Default)]
struct TestDomain {
    edges: BTreeMap<u8, Vec<(u8, &'static str, u64)>>,
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
        _epoch: &Self::GraphEpoch,
        _node: &Self::Node,
        _goal: &Self::Node,
    ) -> Self::Cost {
        0
    }

    fn snapshot_id(&self, _epoch: &Self::GraphEpoch) -> Self::SnapshotId {
        "epoch-1"
    }
}

#[test]
fn viewer_adapter_projects_search_artifacts() {
    let mut domain = TestDomain::default();
    domain.edges.insert(0, vec![(1, "0-1", 1)]);
    domain.edges.insert(1, vec![(2, "1-2", 1)]);
    let mut machine = SearchMachine::new(domain, 1, 0, 2, EpsilonMilli::one());
    let (report, replay) = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        SearchRunConfig {
            scheduler_profile: SearchSchedulerProfile::CanonicalSerial,
            batch_width: 1,
            fairness_assumptions: BTreeSet::from([
                SearchFairnessAssumption::DeterministicSchedulerConfluence,
            ]),
        },
    )
    .expect("search run");

    let artifact = project_search_artifacts(&report.observation, &replay);
    assert_eq!(artifact.incumbent_cost, Some(2));
    assert_eq!(artifact.rounds, replay.rounds);
}
