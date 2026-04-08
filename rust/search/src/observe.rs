//! Observation, replay-artifact, and comparison boundary for `telltale-search`.

use serde::{Deserialize, Serialize};

use crate::admission::{
    SearchDeterminismMode, SearchFairnessAssumption, SearchObservableClass, SearchSchedulerProfile,
};
use crate::cost::SearchCost;

/// One normalized canonical commit record.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct NormalizedCommitRecord<N, C> {
    /// Target node updated by the commit.
    pub node: N,
    /// Canonical resulting `g` score.
    pub g_score: C,
}

/// One observed search artifact derived from a canonical machine run.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchObservationArtifact<N, G, C> {
    /// Current incumbent cost.
    pub incumbent_cost: Option<C>,
    /// Current incumbent path.
    pub incumbent_path: Option<Vec<N>>,
    /// Canonical normalized commit trace.
    pub normalized_commit_trace: Vec<NormalizedCommitRecord<N, C>>,
    /// Replay checkpoint markers.
    pub replay_checkpoints: Vec<String>,
    /// Graph epoch trace.
    pub graph_epoch_trace: Vec<G>,
    /// Declared scheduler profile.
    pub scheduler_profile: SearchSchedulerProfile,
    /// Declared fairness assumptions.
    pub fairness_assumptions: Vec<SearchFairnessAssumption>,
    /// Exact productive-step count.
    pub productive_steps: u64,
    /// Total scheduler-step count.
    pub total_scheduler_steps: u64,
}

/// Comparison relation between two observed artifacts.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum ObservationRelation {
    /// Exact equality under the requested mode.
    Exact,
    /// Equality only after commutative normalization.
    EquivalentModuloCommutativity,
    /// Observable mismatch.
    Mismatch,
}

/// Result of comparing two observed artifacts.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ObservationComparison {
    /// Overall relation under the requested mode.
    pub relation: ObservationRelation,
    /// Observable classes that mismatched.
    pub mismatches: Vec<SearchObservableClass>,
}

/// Compare two observed artifacts under one determinism mode and observable set.
#[must_use]
pub fn compare_observations<N, G, C>(
    left: &SearchObservationArtifact<N, G, C>,
    right: &SearchObservationArtifact<N, G, C>,
    mode: SearchDeterminismMode,
    required: &[SearchObservableClass],
) -> ObservationComparison
where
    N: Clone + Ord,
    G: Clone + Ord,
    C: SearchCost,
{
    let mut mismatches = Vec::new();
    for observable in required {
        match observable {
            SearchObservableClass::IncumbentCost => {
                if left.incumbent_cost != right.incumbent_cost {
                    mismatches.push(*observable);
                }
            }
            SearchObservableClass::CanonicalPathIdentity => {
                if left.incumbent_path != right.incumbent_path {
                    mismatches.push(*observable);
                }
            }
            SearchObservableClass::NormalizedCommitTrace => {
                let equal = match mode {
                    SearchDeterminismMode::ModuloCommutativity => {
                        normalized_commit_multiset(&left.normalized_commit_trace)
                            == normalized_commit_multiset(&right.normalized_commit_trace)
                    }
                    _ => left.normalized_commit_trace == right.normalized_commit_trace,
                };
                if !equal {
                    mismatches.push(*observable);
                }
            }
            SearchObservableClass::GraphEpochTrace => {
                if left.graph_epoch_trace != right.graph_epoch_trace {
                    mismatches.push(*observable);
                }
            }
            SearchObservableClass::SchedulerProfileTrace => {
                if left.scheduler_profile != right.scheduler_profile {
                    mismatches.push(*observable);
                }
            }
            SearchObservableClass::ProgressAccounting => {
                if left.productive_steps != right.productive_steps
                    || left.total_scheduler_steps != right.total_scheduler_steps
                {
                    mismatches.push(*observable);
                }
            }
            SearchObservableClass::ReplayCheckpointTrace => {
                if left.replay_checkpoints != right.replay_checkpoints {
                    mismatches.push(*observable);
                }
            }
            SearchObservableClass::CanonicalParentIdentity
            | SearchObservableClass::IncumbentPublicationTrace => {}
        }
    }

    let relation = if mismatches.is_empty() {
        match mode {
            SearchDeterminismMode::ModuloCommutativity
                if left.normalized_commit_trace != right.normalized_commit_trace =>
            {
                ObservationRelation::EquivalentModuloCommutativity
            }
            _ => ObservationRelation::Exact,
        }
    } else {
        ObservationRelation::Mismatch
    };

    ObservationComparison {
        relation,
        mismatches,
    }
}

fn normalized_commit_multiset<N, C>(records: &[NormalizedCommitRecord<N, C>]) -> Vec<(N, u128)>
where
    N: Clone + Ord,
    C: SearchCost,
{
    let mut normalized = records
        .iter()
        .map(|record| (record.node.clone(), record.g_score.order_key()))
        .collect::<Vec<_>>();
    normalized.sort();
    normalized
}

#[cfg(test)]
mod tests {
    use super::*;

    fn artifact(
        trace: Vec<(u8, u64)>,
        scheduler_profile: SearchSchedulerProfile,
    ) -> SearchObservationArtifact<u8, u64, u64> {
        SearchObservationArtifact {
            incumbent_cost: Some(3),
            incumbent_path: Some(vec![0, 1, 3]),
            normalized_commit_trace: trace
                .into_iter()
                .map(|(node, g_score)| NormalizedCommitRecord { node, g_score })
                .collect(),
            replay_checkpoints: vec!["cp0".to_string()],
            graph_epoch_trace: vec![1],
            scheduler_profile,
            fairness_assumptions: vec![SearchFairnessAssumption::DeterministicSchedulerConfluence],
            productive_steps: 2,
            total_scheduler_steps: 3,
        }
    }

    #[test]
    fn modulo_commutativity_accepts_reordered_commit_trace() {
        let left = artifact(
            vec![(1, 1), (2, 1)],
            SearchSchedulerProfile::CanonicalSerial,
        );
        let right = artifact(
            vec![(2, 1), (1, 1)],
            SearchSchedulerProfile::CanonicalSerial,
        );
        let comparison = compare_observations(
            &left,
            &right,
            SearchDeterminismMode::ModuloCommutativity,
            &[SearchObservableClass::NormalizedCommitTrace],
        );
        assert_eq!(
            comparison.relation,
            ObservationRelation::EquivalentModuloCommutativity
        );
    }

    #[test]
    fn full_mode_rejects_scheduler_profile_mismatch() {
        let left = artifact(vec![(1, 1)], SearchSchedulerProfile::CanonicalSerial);
        let right = artifact(vec![(1, 1)], SearchSchedulerProfile::BatchedParallelExact);
        let comparison = compare_observations(
            &left,
            &right,
            SearchDeterminismMode::Full,
            &[SearchObservableClass::SchedulerProfileTrace],
        );
        assert_eq!(comparison.relation, ObservationRelation::Mismatch);
        assert_eq!(
            comparison.mismatches,
            vec![SearchObservableClass::SchedulerProfileTrace]
        );
    }
}
