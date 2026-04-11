#![allow(clippy::expect_used)]
//! Jacquard-style selector import example for `telltale-search`.

use std::collections::{BTreeMap, BTreeSet};

use telltale_search::{
    run_with_executor, EpsilonMilli, SearchDomain, SearchExecutionPolicy, SearchFairnessAssumption,
    SearchMachine, SearchQuery, SearchRunConfig, SearchSchedulerProfile,
    SearchSelectedResultSemanticsClass, SerialProposalExecutor,
};

#[derive(Clone, Debug, Default)]
struct JacquardSelectorDomain {
    edges: BTreeMap<&'static str, Vec<(&'static str, &'static str, u64)>>,
}

impl SearchDomain for JacquardSelectorDomain {
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
        _node: &Self::Node,
        _goal: &Self::Node,
    ) -> Self::Cost {
        0
    }

    fn selected_result_semantics_class(
        &self,
        _query: &SearchQuery<Self::Node>,
    ) -> SearchSelectedResultSemanticsClass {
        SearchSelectedResultSemanticsClass::DomainDefinedFromDiscoveredState
    }

    fn selected_result_candidates(
        &self,
        query: &SearchQuery<Self::Node>,
        g_score: &BTreeMap<Self::Node, Self::Cost>,
    ) -> Vec<Self::Node> {
        // Only candidates whose discovered score is at least 2 are eligible
        // for publication in this selector policy.
        let mut eligible = g_score
            .iter()
            .filter_map(|(node, cost)| {
                if query.accepts(node) && *cost >= 2 {
                    Some(*node)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        eligible.sort();
        eligible.dedup();
        eligible
    }

    fn snapshot_id(&self, _epoch: &Self::GraphEpoch) -> Self::SnapshotId {
        "jacquard-selector"
    }
}

fn main() {
    let mut domain = JacquardSelectorDomain::default();
    domain.edges.insert(
        "seed",
        vec![
            ("fast-lane", "seed-fast", 1),
            ("stable-lane", "seed-stable", 1),
        ],
    );
    domain
        .edges
        .insert("fast-lane", vec![("candidate-a", "fast-a", 0)]);
    domain
        .edges
        .insert("stable-lane", vec![("candidate-b", "stable-b", 1)]);

    let query = SearchQuery::try_candidate_set("seed", vec!["candidate-a", "candidate-b"], None)
        .expect("non-empty selector query");

    let mut machine = SearchMachine::new_with_query(domain, 1, query, EpsilonMilli::one());
    let (report, replay) = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        SearchRunConfig::new(
            SearchExecutionPolicy::new(SearchSchedulerProfile::CanonicalSerial, 1),
            BTreeSet::from([SearchFairnessAssumption::DeterministicSchedulerConfluence]),
        ),
    )
    .expect("selector run");

    println!(
        "selected_result_cost={:?}",
        report.observation.selected_result_cost
    );
    println!(
        "selected_result_witness={:?}",
        report.observation.selected_result_witness
    );
    println!(
        "selected_result_semantics_class={:?}",
        replay.selected_result_semantics_class
    );
    println!("path_problem_helper={:?}", report.route_bounds.path_problem);
}
