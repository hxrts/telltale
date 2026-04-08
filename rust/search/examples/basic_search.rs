#![allow(clippy::expect_used)]
//! Minimal generic weighted-graph example for `telltale-search`.

use std::collections::BTreeMap;

use telltale_search::{
    run_with_executor, EpsilonMilli, SearchDomain, SearchFairnessAssumption, SearchMachine,
    SearchSchedulerProfile, SerialProposalExecutor,
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
        "static-demo"
    }
}

fn main() {
    let mut domain = ExampleDomain::default();
    domain
        .edges
        .insert("A", vec![("B", "A-B", 1), ("C", "A-C", 3)]);
    domain.edges.insert("B", vec![("D", "B-D", 2)]);
    domain.edges.insert("C", vec![("D", "C-D", 1)]);
    domain.heuristics.insert(("A", "D"), 2);
    domain.heuristics.insert(("B", "D"), 1);
    domain.heuristics.insert(("C", "D"), 1);

    let mut machine = SearchMachine::new(domain, 1, "A", "D", EpsilonMilli::one());
    let (report, replay) = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        SearchSchedulerProfile::CanonicalSerial,
        1,
        vec![SearchFairnessAssumption::DeterministicSchedulerConfluence],
    )
    .expect("example run");

    println!("incumbent_cost={:?}", report.observation.incumbent_cost);
    println!("incumbent_path={:?}", report.observation.incumbent_path);
    println!("rounds={}", replay.rounds.len());
}
