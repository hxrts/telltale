//! Optional viewer projection layer for `telltale-search` artifacts.

use serde::{Deserialize, Serialize};
use telltale_search::{ReplayRoundRecord, SearchObservationArtifact, SearchReplayArtifact};

/// Viewer-facing projection of one search run.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchViewerArtifact<N, G, S, C>
where
    N: Ord,
    G: Ord,
    S: Ord,
{
    /// Current incumbent path, if any.
    pub incumbent_path: Option<Vec<N>>,
    /// Current incumbent cost, if any.
    pub incumbent_cost: Option<C>,
    /// Normalized commit trace length for quick graph/timeline summaries.
    pub commit_count: usize,
    /// Graph epoch trace for time-travel and branch inspection.
    pub graph_epoch_trace: Vec<G>,
    /// Canonical replay rounds for stepwise inspection.
    pub rounds: Vec<ReplayRoundRecord<N, G, S, C>>,
}

/// Project a pure search observation plus replay into a viewer artifact.
#[must_use]
pub fn project_search_artifacts<N, G, S, C>(
    observation: &SearchObservationArtifact<N, G, C>,
    replay: &SearchReplayArtifact<N, G, S, C>,
) -> SearchViewerArtifact<N, G, S, C>
where
    N: Clone + Ord,
    G: Clone + Ord,
    S: Clone + Ord,
    C: Clone + Eq,
{
    SearchViewerArtifact {
        incumbent_path: observation.selected_result_witness.clone(),
        incumbent_cost: observation.selected_result_cost.clone(),
        commit_count: observation.normalized_commit_trace.len(),
        graph_epoch_trace: observation.graph_epoch_trace.clone(),
        rounds: replay.rounds.clone(),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::{BTreeMap, BTreeSet};

    use telltale_search::{
        run_with_executor, EpsilonMilli, SearchDomain, SearchExecutionPolicy,
        SearchFairnessAssumption, SearchMachine, SearchRunConfig, SearchSchedulerProfile,
        SerialProposalExecutor,
    };

    use super::*;

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
    fn projects_search_artifacts_for_viewer_consumption() {
        let mut domain = TestDomain::default();
        domain.edges.insert(0, vec![(1, "0-1", 1)]);
        domain.edges.insert(1, vec![(2, "1-2", 1)]);
        let mut machine = SearchMachine::new(domain, 1, 0, 2, EpsilonMilli::one());
        let (report, replay) = run_with_executor(
            &mut machine,
            &SerialProposalExecutor,
            SearchRunConfig::new(
                SearchExecutionPolicy::new(SearchSchedulerProfile::CanonicalSerial, 1),
                BTreeSet::from([SearchFairnessAssumption::DeterministicSchedulerConfluence]),
            ),
        )
        .expect("search run");

        let artifact = project_search_artifacts(&report.observation, &replay);
        assert_eq!(artifact.incumbent_cost, Some(2));
        assert_eq!(
            artifact.commit_count,
            report.observation.normalized_commit_trace.len()
        );
        assert_eq!(artifact.rounds.len(), replay.rounds.len());
    }
}
