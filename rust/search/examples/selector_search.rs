#![allow(clippy::expect_used)]
//! Selector-style search example for `telltale-search`.

use std::collections::BTreeMap;
use std::collections::BTreeSet;

use telltale_search::{
    run_with_executor, EpsilonMilli, SearchDomain, SearchExecutionPolicy, SearchFairnessAssumption,
    SearchMachine, SearchQuery, SearchRunConfig, SearchSchedulerProfile, SerialProposalExecutor,
};

#[derive(Clone, Debug, Default)]
struct ExampleDomain {
    edges: BTreeMap<&'static str, Vec<(&'static str, &'static str, u64)>>,
    heuristics: BTreeMap<(&'static str, &'static str), u64>,
}

impl SearchDomain for ExampleDomain {
    type Node = &'static str;
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
        node: &Self::Node,
        goal: &Self::Node,
    ) -> Self::Cost {
        *self.heuristics.get(&(*node, *goal)).unwrap_or(&0)
    }

    fn snapshot_id(&self, _epoch: &Self::GraphEpoch) -> Self::SnapshotId {
        "selector-demo"
    }
}

fn main() {
    let mut domain = ExampleDomain::default();
    domain.edges.insert(
        "seed",
        vec![("left", "seed-left", 1), ("right", "seed-right", 1)],
    );
    domain
        .edges
        .insert("left", vec![("candidate-a", "left-a", 2)]);
    domain
        .edges
        .insert("right", vec![("candidate-b", "right-b", 1)]);
    domain.heuristics.insert(("seed", "candidate-a"), 2);
    domain.heuristics.insert(("seed", "candidate-b"), 1);
    domain.heuristics.insert(("left", "candidate-a"), 1);
    domain.heuristics.insert(("right", "candidate-b"), 0);

    let query = SearchQuery::candidate_set(
        "seed",
        vec!["candidate-a", "candidate-b"],
        Some("candidate-b"),
    );
    let mut machine = SearchMachine::new_with_query(domain, 1, query, EpsilonMilli::one());
    let (report, replay) = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        SearchRunConfig::new(
            SearchExecutionPolicy::new(SearchSchedulerProfile::CanonicalSerial, 1),
            BTreeSet::from([SearchFairnessAssumption::DeterministicSchedulerConfluence]),
        ),
    )
    .expect("selector example run");

    println!(
        "selected_cost={:?}",
        report.observation.selected_result_cost
    );
    println!(
        "selected_witness={:?}",
        report.observation.selected_result_witness
    );
    println!("query={:?}", replay.query);
}
