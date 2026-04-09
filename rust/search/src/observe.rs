//! Observation, replay-artifact, and comparison boundary for `telltale-search`.

use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use crate::admission::{
    SearchDeterminismMode, SearchFairnessAssumption, SearchObservableClass, SearchSchedulerProfile,
};
use crate::cost::SearchCost;

/// Accumulated replay- and observation-visible records collected during one run.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SearchObservationAccumulator<N, G, C> {
    /// Canonical normalized commit trace.
    pub(crate) normalized_commit_trace: Vec<NormalizedCommitRecord<N, C>>,
    /// Replay checkpoint markers.
    pub(crate) replay_checkpoints: Vec<String>,
    /// Graph epoch trace.
    pub(crate) graph_epoch_trace: Vec<G>,
    /// Incumbent publication trace.
    pub(crate) incumbent_publication_trace: Vec<IncumbentPublicationRecord<N, C>>,
}

/// One normalized canonical commit record.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct NormalizedCommitRecord<N, C> {
    /// Target node updated by the commit.
    pub node: N,
    /// Canonical parent chosen for the committed node.
    pub parent: Option<N>,
    /// Canonical resulting `g` score.
    pub g_score: C,
}

/// One incumbent publication derived from canonical commit state.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct IncumbentPublicationRecord<N, C> {
    /// Published incumbent cost.
    pub cost: C,
    /// Published incumbent path.
    pub path: Vec<N>,
}

/// One observed search artifact derived from a canonical machine run.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchObservationArtifact<N, G, C> {
    /// Current incumbent cost.
    pub incumbent_cost: Option<C>,
    /// Current incumbent path.
    pub incumbent_path: Option<Vec<N>>,
    /// Canonical parent identities derived from the authoritative machine state.
    pub canonical_parent_map: Vec<(N, N)>,
    /// Incumbent publication trace.
    pub incumbent_publication_trace: Vec<IncumbentPublicationRecord<N, C>>,
    /// Canonical normalized commit trace.
    pub normalized_commit_trace: Vec<NormalizedCommitRecord<N, C>>,
    /// Replay checkpoint markers.
    pub replay_checkpoints: Vec<String>,
    /// Graph epoch trace.
    pub graph_epoch_trace: Vec<G>,
    /// Declared scheduler profile.
    pub scheduler_profile: SearchSchedulerProfile,
    /// Declared fairness assumptions.
    pub fairness_assumptions: BTreeSet<SearchFairnessAssumption>,
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
            SearchObservableClass::CanonicalParentIdentity => {
                if left.canonical_parent_map != right.canonical_parent_map {
                    mismatches.push(*observable);
                }
            }
            SearchObservableClass::IncumbentPublicationTrace => {
                if left.incumbent_publication_trace != right.incumbent_publication_trace {
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
            SearchObservableClass::FairnessPremiseTrace => {
                if left.fairness_assumptions != right.fairness_assumptions {
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

fn normalized_commit_multiset<N, C>(
    records: &[NormalizedCommitRecord<N, C>],
) -> Vec<(N, Option<N>, u128)>
where
    N: Clone + Ord,
    C: SearchCost,
{
    let mut normalized = records
        .iter()
        .map(|record| {
            (
                record.node.clone(),
                record.parent.clone(),
                record.g_score.order_key(),
            )
        })
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
            canonical_parent_map: vec![(1, 0), (3, 1)],
            incumbent_publication_trace: vec![IncumbentPublicationRecord {
                cost: 3,
                path: vec![0, 1, 3],
            }],
            normalized_commit_trace: trace
                .into_iter()
                .map(|(node, g_score)| NormalizedCommitRecord {
                    node,
                    parent: Some(0),
                    g_score,
                })
                .collect(),
            replay_checkpoints: vec!["cp0".to_string()],
            graph_epoch_trace: vec![1],
            scheduler_profile,
            fairness_assumptions: [SearchFairnessAssumption::DeterministicSchedulerConfluence]
                .into_iter()
                .collect(),
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

    #[test]
    fn fairness_premise_trace_mismatch_is_observable() {
        let left = artifact(vec![(1, 1)], SearchSchedulerProfile::CanonicalSerial);
        let mut right = artifact(vec![(1, 1)], SearchSchedulerProfile::CanonicalSerial);
        right.fairness_assumptions = [SearchFairnessAssumption::EventualLiveBatchService]
            .into_iter()
            .collect();
        let comparison = compare_observations(
            &left,
            &right,
            SearchDeterminismMode::Full,
            &[SearchObservableClass::FairnessPremiseTrace],
        );
        assert_eq!(comparison.relation, ObservationRelation::Mismatch);
        assert_eq!(
            comparison.mismatches,
            vec![SearchObservableClass::FairnessPremiseTrace]
        );
    }

    #[test]
    fn canonical_parent_identity_and_incumbent_publication_are_observable() {
        let left = artifact(vec![(1, 1)], SearchSchedulerProfile::CanonicalSerial);
        let mut right = artifact(vec![(1, 1)], SearchSchedulerProfile::CanonicalSerial);
        right.canonical_parent_map = vec![(1, 0), (3, 2)];
        right.incumbent_publication_trace = vec![IncumbentPublicationRecord {
            cost: 4,
            path: vec![0, 2, 3],
        }];
        let comparison = compare_observations(
            &left,
            &right,
            SearchDeterminismMode::Full,
            &[
                SearchObservableClass::CanonicalParentIdentity,
                SearchObservableClass::IncumbentPublicationTrace,
            ],
        );
        assert_eq!(comparison.relation, ObservationRelation::Mismatch);
        assert_eq!(
            comparison.mismatches,
            vec![
                SearchObservableClass::CanonicalParentIdentity,
                SearchObservableClass::IncumbentPublicationTrace,
            ]
        );
    }
}
