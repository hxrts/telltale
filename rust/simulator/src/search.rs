//! Optional adapter layer for projecting `telltale-search` artifacts into
//! simulator-facing artifacts.

use serde::{Deserialize, Serialize};
use telltale_search::{
    ReplayRoundRecord, SchedulerArtifact, SearchExecutionReport, SearchReplayArtifact,
};

/// Simulator-facing projection of one search run.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchSimulationArtifact<N, G, S, C>
where
    N: Ord,
    G: Ord,
    S: Ord,
{
    /// Final observation exported through the simulator layer.
    pub observation: telltale_search::SearchObservationArtifact<N, G, C>,
    /// Scheduler and fairness metadata.
    pub scheduler: SchedulerArtifact,
    /// Canonical replay rounds for deterministic inspection.
    pub rounds: Vec<ReplayRoundRecord<N, G, S, C>>,
}

/// Project one `telltale-search` execution + replay pair into a simulator
/// artifact.
#[must_use]
pub fn project_search_run<N, G, S, C>(
    execution: &SearchExecutionReport<N, G, C>,
    replay: &SearchReplayArtifact<N, G, S, C>,
) -> SearchSimulationArtifact<N, G, S, C>
where
    N: Clone + Ord,
    G: Clone + Ord,
    S: Clone + Ord,
    C: Clone + Eq,
{
    SearchSimulationArtifact {
        observation: execution.observation.clone(),
        scheduler: execution.scheduler.clone(),
        rounds: replay.rounds.clone(),
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use telltale_search::{
        run_with_executor, EpsilonMilli, SearchDomain, SearchFairnessAssumption, SearchMachine,
        SearchSchedulerProfile, SerialProposalExecutor,
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
    fn projects_search_run_for_simulator_consumption() {
        let mut domain = TestDomain::default();
        domain.edges.insert(0, vec![(1, "0-1", 1)]);
        domain.edges.insert(1, vec![(2, "1-2", 1)]);
        let mut machine = SearchMachine::new(domain, 1, 0, 2, EpsilonMilli::one());
        let (report, replay) = run_with_executor(
            &mut machine,
            &SerialProposalExecutor,
            SearchSchedulerProfile::CanonicalSerial,
            1,
            vec![SearchFairnessAssumption::DeterministicSchedulerConfluence],
        )
        .expect("search run");

        let artifact = project_search_run(&report, &replay);
        assert_eq!(artifact.observation.incumbent_cost, Some(2));
        assert_eq!(
            artifact.scheduler.scheduler_profile,
            SearchSchedulerProfile::CanonicalSerial
        );
        assert_eq!(artifact.rounds.len(), replay.rounds.len());
    }
}
