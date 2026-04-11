#![allow(missing_docs)]
//! Export stable search artifact vectors as JSON.

use std::collections::BTreeMap;

use telltale_search::{
    run_with_executor, EpsilonMilli, SearchDomain, SearchExecutionPolicy, SearchFairnessAssumption,
    SearchRunConfig, SearchSchedulerProfile, SerialProposalExecutor,
};

#[derive(Clone, Debug, Default)]
struct VectorDomain {
    edges: BTreeMap<u8, Vec<(u8, &'static str, u64)>>,
}

impl SearchDomain for VectorDomain {
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

    fn snapshot_id(&self, epoch: &Self::GraphEpoch) -> Self::SnapshotId {
        if *epoch == 1 {
            "epoch-1"
        } else {
            "epoch-2"
        }
    }
}

fn main() {
    let mut domain = VectorDomain::default();
    domain.edges.insert(0, vec![(1, "0-1", 1), (2, "0-2", 1)]);
    domain.edges.insert(1, vec![(3, "1-3", 1)]);
    domain.edges.insert(2, vec![(3, "2-3", 2)]);

    let mut machine = telltale_search::SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
    let (report, replay) = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        SearchRunConfig::new(
            SearchExecutionPolicy::new(SearchSchedulerProfile::CanonicalSerial, 1),
            [SearchFairnessAssumption::DeterministicSchedulerConfluence]
                .into_iter()
                .collect(),
        ),
    )
    .expect("vector run");

    println!(
        "{}",
        serde_json::to_string_pretty(&serde_json::json!({
            "schema_version": "search_vectors_v1",
            "theorem_pack": report.theorem_pack,
            "route_bounds": report.route_bounds,
            "final_state": report.final_state,
            "fairness_certificate_trace": report.fairness_certificate_trace,
            "observation": report.observation,
            "replay_rounds": replay.rounds,
        }))
        .expect("serialize search vectors")
    );
}
