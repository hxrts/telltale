use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::admission::{SearchFairnessAssumption, SearchSchedulerProfile};
use crate::cost::SearchCost;
use crate::domain::SearchDomain;
use crate::machine::{FrontierEntry, SearchError, SearchMachine, SearchState};
use crate::observe::{
    IncumbentPublicationRecord, NormalizedCommitRecord, SearchObservationArtifact,
};

use super::executor::{ProposalExecutor, ProposalExecutorKind};

type RuntimeExecutionResult<D> = Result<
    (
        SearchExecutionReport<
            <D as SearchDomain>::Node,
            <D as SearchDomain>::GraphEpoch,
            <D as SearchDomain>::Cost,
        >,
        SearchReplayArtifact<
            <D as SearchDomain>::Node,
            <D as SearchDomain>::GraphEpoch,
            <D as SearchDomain>::SnapshotId,
            <D as SearchDomain>::Cost,
        >,
    ),
    SearchRunError<<D as SearchDomain>::Error>,
>;

type RuntimeState<D> = SearchState<
    <D as SearchDomain>::Node,
    <D as SearchDomain>::EdgeMeta,
    <D as SearchDomain>::GraphEpoch,
    <D as SearchDomain>::SnapshotId,
    <D as SearchDomain>::Cost,
>;

/// Exactness class for total-step reporting.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum TotalStepMode {
    /// Total-step accounting is exact.
    Exact,
    /// Total-step accounting is scheduler-lifted under declared fairness
    /// assumptions.
    FairnessBounded,
}

/// Search progress summary.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ProgressSummary {
    /// Productive-step count.
    pub productive_steps: u64,
    /// Total scheduler-step count.
    pub total_scheduler_steps: u64,
    /// Exactness class of the total-step count.
    pub total_step_mode: TotalStepMode,
    /// Fairness assumptions used by the summary.
    pub fairness_assumptions: BTreeSet<SearchFairnessAssumption>,
}

/// Scheduler artifact for one run.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SchedulerArtifact {
    /// Declared scheduler class.
    pub scheduler_profile: SearchSchedulerProfile,
    /// Whether the scheduler artifact is exact, normalized, or only diagnostic.
    pub authority_class: SchedulerArtifactClass,
    /// Configured batch width.
    pub batch_width: u64,
    /// Declared fairness assumptions.
    pub fairness_assumptions: BTreeSet<SearchFairnessAssumption>,
}

/// Typed runtime configuration for one search run.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SearchRunConfig {
    /// Declared scheduler profile.
    pub scheduler_profile: SearchSchedulerProfile,
    /// Configured batch width.
    pub batch_width: u64,
    /// Declared fairness assumptions.
    pub fairness_assumptions: BTreeSet<SearchFairnessAssumption>,
}

/// Fail-closed runtime-config rejection.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum SearchRunConfigError {
    /// Batch width must be non-zero.
    ZeroBatchWidth,
    /// The selected scheduler profile requires the serial executor.
    RequiresSerialExecutor(SearchSchedulerProfile),
    /// The selected scheduler profile requires the native parallel executor.
    RequiresNativeParallelExecutor(SearchSchedulerProfile),
    /// The selected scheduler profile requires batch width one.
    RequiresBatchWidthOne(SearchSchedulerProfile),
    /// The selected scheduler profile requires a batch width greater than one.
    RequiresBatchWidthGreaterThanOne(SearchSchedulerProfile),
    /// The selected scheduler profile requires one fairness assumption.
    MissingFairnessAssumption {
        /// Profile being validated.
        profile: SearchSchedulerProfile,
        /// Missing assumption.
        assumption: SearchFairnessAssumption,
    },
}

/// Runtime execution error surface.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SearchRunError<E> {
    /// Invalid runtime configuration.
    InvalidConfig(SearchRunConfigError),
    /// Search-machine or domain error.
    Search(SearchError<E>),
}

/// Authority classification for emitted scheduler artifacts.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SchedulerArtifactClass {
    /// Scheduler artifact is authoritative and exact.
    Exact,
    /// Scheduler artifact is authoritative only after profile normalization.
    Normalized,
    /// Scheduler artifact is diagnostic and may not participate in exact claims.
    Diagnostic,
}

/// Execution report for one run.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchExecutionReport<N, G, C>
where
    N: Ord,
    G: Ord,
{
    /// Final observed artifact.
    pub observation: SearchObservationArtifact<N, G, C>,
    /// Scheduler artifact.
    pub scheduler: SchedulerArtifact,
    /// Progress summary.
    pub progress: ProgressSummary,
}

/// Replay record for one committed round.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct ReplayRoundRecord<N, G, S, C>
where
    N: Ord,
    G: Ord,
    S: Ord,
{
    /// Frozen graph epoch for the round.
    pub epoch: G,
    /// Frozen snapshot identity for the round.
    pub snapshot_id: S,
    /// Search phase identifier.
    pub phase: u64,
    /// Nodes in the extracted batch.
    pub batch_nodes: Vec<N>,
    /// Canonical normalized commit records produced by the round.
    pub commits: Vec<NormalizedCommitRecord<N, C>>,
}

/// Canonical replay artifact for one run.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchReplayArtifact<N, G, S, C>
where
    N: Ord,
    G: Ord,
    S: Ord,
{
    /// Canonical start node for the run.
    pub start: N,
    /// Canonical goal node for the run.
    pub goal: N,
    /// Declared scheduler profile.
    pub scheduler_profile: SearchSchedulerProfile,
    /// Declared fairness assumptions.
    pub fairness_assumptions: BTreeSet<SearchFairnessAssumption>,
    /// Graph epoch trace for the run.
    pub epoch_trace: Vec<G>,
    /// Canonical replay rounds.
    pub rounds: Vec<ReplayRoundRecord<N, G, S, C>>,
    /// Final observed artifact.
    pub final_observation: SearchObservationArtifact<N, G, C>,
}

/// Replay-time contract expected by the caller.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReplayExpectation<N, G, S> {
    /// Expected graph epoch trace.
    pub expected_epochs: Vec<G>,
    /// Expected per-round snapshot schedule.
    pub expected_snapshots: Vec<S>,
    /// Expected per-round phase sequence.
    pub expected_phases: Vec<u64>,
    /// Expected per-round batch nodes.
    pub expected_batch_nodes: Vec<Vec<N>>,
    /// Required fairness assumptions for theorem-style comparisons.
    pub required_fairness: BTreeSet<SearchFairnessAssumption>,
}

/// Requested epoch update to be committed at the next barrier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EpochReconfigurationRequest<G> {
    /// Next graph epoch.
    pub next_epoch: G,
}

/// Replay error surface.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ReplayError {
    /// The replay artifact epoch schedule does not match the requested schedule.
    EpochSchedule,
    /// The replay artifact snapshot schedule does not match the requested
    /// schedule.
    SnapshotSchedule,
    /// The replay artifact phase schedule does not match the requested schedule.
    PhaseSchedule,
    /// The replay artifact batch-node schedule does not match the requested
    /// schedule.
    BatchSchedule,
    /// The replay artifact fairness bundle does not satisfy the requested
    /// theorem-style premise bundle.
    FairnessBundle,
    /// The stored final observation does not match the derived replay result.
    ObservationArtifact,
}

fn require_fairness(
    config: &SearchRunConfig,
    profile: SearchSchedulerProfile,
    assumption: SearchFairnessAssumption,
) -> Result<(), SearchRunConfigError> {
    if config.fairness_assumptions.contains(&assumption) {
        Ok(())
    } else {
        Err(SearchRunConfigError::MissingFairnessAssumption {
            profile,
            assumption,
        })
    }
}

/// Validate one runtime configuration against one executor kind.
pub fn validate_run_config<D, X>(
    executor: &X,
    config: &SearchRunConfig,
) -> Result<(), SearchRunConfigError>
where
    D: SearchDomain,
    X: ProposalExecutor<D>,
{
    if config.batch_width == 0 {
        return Err(SearchRunConfigError::ZeroBatchWidth);
    }

    match config.scheduler_profile {
        SearchSchedulerProfile::CanonicalSerial => {
            if executor.kind() != ProposalExecutorKind::Serial {
                return Err(SearchRunConfigError::RequiresSerialExecutor(
                    config.scheduler_profile,
                ));
            }
            if config.batch_width != 1 {
                return Err(SearchRunConfigError::RequiresBatchWidthOne(
                    config.scheduler_profile,
                ));
            }
            require_fairness(
                config,
                config.scheduler_profile,
                SearchFairnessAssumption::DeterministicSchedulerConfluence,
            )?;
        }
        SearchSchedulerProfile::ThreadedExactSingleLane => {
            if executor.kind() != ProposalExecutorKind::NativeParallel {
                return Err(SearchRunConfigError::RequiresNativeParallelExecutor(
                    config.scheduler_profile,
                ));
            }
            if config.batch_width != 1 {
                return Err(SearchRunConfigError::RequiresBatchWidthOne(
                    config.scheduler_profile,
                ));
            }
            require_fairness(
                config,
                config.scheduler_profile,
                SearchFairnessAssumption::DeterministicSchedulerConfluence,
            )?;
        }
        SearchSchedulerProfile::BatchedParallelExact => {
            if executor.kind() != ProposalExecutorKind::NativeParallel {
                return Err(SearchRunConfigError::RequiresNativeParallelExecutor(
                    config.scheduler_profile,
                ));
            }
            if config.batch_width <= 1 {
                return Err(SearchRunConfigError::RequiresBatchWidthGreaterThanOne(
                    config.scheduler_profile,
                ));
            }
            require_fairness(
                config,
                config.scheduler_profile,
                SearchFairnessAssumption::DeterministicSchedulerConfluence,
            )?;
        }
        SearchSchedulerProfile::BatchedParallelEnvelopeBounded => {
            if executor.kind() != ProposalExecutorKind::NativeParallel {
                return Err(SearchRunConfigError::RequiresNativeParallelExecutor(
                    config.scheduler_profile,
                ));
            }
            if config.batch_width <= 1 {
                return Err(SearchRunConfigError::RequiresBatchWidthGreaterThanOne(
                    config.scheduler_profile,
                ));
            }
            require_fairness(
                config,
                config.scheduler_profile,
                SearchFairnessAssumption::EventualLiveBatchService,
            )?;
            require_fairness(
                config,
                config.scheduler_profile,
                SearchFairnessAssumption::NoStarvationWithinLegalWindow,
            )?;
        }
    }

    Ok(())
}

/// Execute one machine to completion through one proposal executor.
///
/// # Errors
///
/// Returns an error if successor enumeration fails in the domain or if the
/// authoritative machine detects an invariant violation during commit.
///
/// # Panics
///
/// Panics if one extracted batch entry count does not fit in `u64`.
pub fn run_with_executor<D, X>(
    machine: &mut SearchMachine<D>,
    executor: &X,
    config: SearchRunConfig,
) -> RuntimeExecutionResult<D>
where
    D: SearchDomain,
    X: ProposalExecutor<D>,
{
    validate_run_config::<D, X>(executor, &config).map_err(SearchRunError::InvalidConfig)?;
    let mut rounds = Vec::new();
    while let Some(batch) = machine.next_batch() {
        let mut proposals = executor
            .generate(machine.domain(), &batch, machine.goal())
            .map_err(SearchError::Domain)
            .map_err(SearchRunError::Search)?;
        machine.state_mut().trace_state.total_scheduler_steps += 1;
        let pre_commit_len = machine.observation().normalized_commit_trace.len();
        machine.activate_batch(&batch);
        machine.normalize_proposals(&mut proposals);
        let changed = machine.commit_proposals(&proposals);
        machine.state_mut().budget_state.expansions +=
            u64::try_from(batch.entries.len()).expect("batch entry count must fit in u64");
        machine.state_mut().budget_state.batches += 1;
        if changed {
            machine.state_mut().trace_state.productive_steps += 1;
        }
        machine
            .check_invariants()
            .map_err(SearchError::InvariantViolation)
            .map_err(SearchRunError::Search)?;

        let round_commits =
            machine.observation().normalized_commit_trace[pre_commit_len..].to_vec();
        rounds.push(ReplayRoundRecord {
            epoch: batch.epoch.clone(),
            snapshot_id: batch.snapshot_id.clone(),
            phase: batch.phase,
            batch_nodes: batch
                .entries
                .iter()
                .map(|entry| entry.node.clone())
                .collect(),
            commits: round_commits,
        });
    }

    let observation = machine.observation_artifact(
        config.scheduler_profile,
        config.fairness_assumptions.clone(),
    );
    let total_step_mode = match config.scheduler_profile {
        SearchSchedulerProfile::CanonicalSerial
        | SearchSchedulerProfile::ThreadedExactSingleLane
        | SearchSchedulerProfile::BatchedParallelExact => TotalStepMode::Exact,
        SearchSchedulerProfile::BatchedParallelEnvelopeBounded => TotalStepMode::FairnessBounded,
    };
    let progress = ProgressSummary {
        productive_steps: observation.productive_steps,
        total_scheduler_steps: observation.total_scheduler_steps,
        total_step_mode,
        fairness_assumptions: config.fairness_assumptions.clone(),
    };
    let scheduler = SchedulerArtifact {
        scheduler_profile: config.scheduler_profile,
        authority_class: classify_scheduler_artifact(config.scheduler_profile),
        batch_width: config.batch_width,
        fairness_assumptions: config.fairness_assumptions.clone(),
    };
    let replay = SearchReplayArtifact {
        start: machine.start.clone(),
        goal: machine.goal.clone(),
        scheduler_profile: config.scheduler_profile,
        fairness_assumptions: config.fairness_assumptions,
        epoch_trace: observation.graph_epoch_trace.clone(),
        rounds,
        final_observation: observation.clone(),
    };
    Ok((
        SearchExecutionReport {
            observation,
            scheduler,
            progress,
        },
        replay,
    ))
}

/// Commit one pending epoch update at a machine barrier.
pub fn commit_epoch_reconfiguration<D: SearchDomain>(
    machine: &mut SearchMachine<D>,
    request: EpochReconfigurationRequest<D::GraphEpoch>,
) {
    let next_snapshot = machine.domain().snapshot_id(&request.next_epoch);
    let start = machine.start.clone();
    machine.state_mut().phase += 1;
    machine.state_mut().graph_epoch = request.next_epoch.clone();
    machine.state_mut().graph_snapshot_id = next_snapshot;
    machine
        .observation_mut()
        .graph_epoch_trace
        .push(request.next_epoch);
    machine.state_mut().closed.clear();
    machine.state_mut().incons.clear();
    machine.last_batch = None;
    machine.state_mut().open.clear();
    machine.state_mut().g_score.clear();
    machine.state_mut().parent.clear();
    machine.state_mut().incumbent = None;

    let entry = machine.rebuild_frontier_entry(&start, D::Cost::zero());
    machine
        .state_mut()
        .g_score
        .insert(start.clone(), D::Cost::zero());
    machine.state_mut().open.insert(start, entry);
}

/// Replay one canonical observation artifact under an expected epoch schedule.
///
/// # Errors
///
/// Returns an error if the replay artifact does not match the requested epoch
/// schedule, phase schedule, or fairness bundle.
pub fn replay_observation<N, G, S, C>(
    replay: &SearchReplayArtifact<N, G, S, C>,
    expectation: &ReplayExpectation<N, G, S>,
) -> Result<SearchObservationArtifact<N, G, C>, ReplayError>
where
    N: Clone + Ord,
    G: Clone + Ord,
    S: Clone + Ord,
    C: SearchCost,
{
    if replay.epoch_trace != expectation.expected_epochs {
        return Err(ReplayError::EpochSchedule);
    }
    let replay_snapshots = replay
        .rounds
        .iter()
        .map(|round| round.snapshot_id.clone())
        .collect::<Vec<_>>();
    if replay_snapshots != expectation.expected_snapshots {
        return Err(ReplayError::SnapshotSchedule);
    }
    let replay_phases = replay
        .rounds
        .iter()
        .map(|round| round.phase)
        .collect::<Vec<_>>();
    if replay_phases != expectation.expected_phases {
        return Err(ReplayError::PhaseSchedule);
    }
    let replay_batches = replay
        .rounds
        .iter()
        .map(|round| round.batch_nodes.clone())
        .collect::<Vec<_>>();
    if replay_batches != expectation.expected_batch_nodes {
        return Err(ReplayError::BatchSchedule);
    }
    if !expectation
        .required_fairness
        .is_subset(&replay.fairness_assumptions)
    {
        return Err(ReplayError::FairnessBundle);
    }

    let normalized_commit_trace = replay
        .rounds
        .iter()
        .flat_map(|round| round.commits.iter().cloned())
        .collect::<Vec<_>>();
    let productive_steps = u64::try_from(
        replay
            .rounds
            .iter()
            .filter(|round| !round.commits.is_empty())
            .count(),
    )
    .map_err(|_| ReplayError::ObservationArtifact)?;
    let total_scheduler_steps =
        u64::try_from(replay.rounds.len()).map_err(|_| ReplayError::ObservationArtifact)?;
    let (incumbent_cost, incumbent_path) =
        reconstruct_incumbent_from_commits(&replay.start, &replay.goal, &normalized_commit_trace);
    let canonical_parent_map = derive_parent_map_from_commits(&normalized_commit_trace);
    let incumbent_publication_trace =
        derive_incumbent_publication_trace(&replay.start, &replay.goal, &normalized_commit_trace);

    let derived = SearchObservationArtifact {
        incumbent_cost,
        incumbent_path,
        canonical_parent_map,
        incumbent_publication_trace,
        normalized_commit_trace,
        replay_checkpoints: replay.final_observation.replay_checkpoints.clone(),
        graph_epoch_trace: replay.epoch_trace.clone(),
        scheduler_profile: replay.scheduler_profile,
        fairness_assumptions: replay.fairness_assumptions.clone(),
        productive_steps,
        total_scheduler_steps,
    };

    if derived != replay.final_observation {
        return Err(ReplayError::ObservationArtifact);
    }
    Ok(derived)
}

/// Classify one scheduler artifact according to the declared scheduler profile.
#[must_use]
pub fn classify_scheduler_artifact(
    scheduler_profile: SearchSchedulerProfile,
) -> SchedulerArtifactClass {
    match scheduler_profile {
        SearchSchedulerProfile::CanonicalSerial
        | SearchSchedulerProfile::ThreadedExactSingleLane
        | SearchSchedulerProfile::BatchedParallelExact => SchedulerArtifactClass::Exact,
        SearchSchedulerProfile::BatchedParallelEnvelopeBounded => {
            SchedulerArtifactClass::Normalized
        }
    }
}

fn derive_parent_map_from_commits<N, C>(commits: &[NormalizedCommitRecord<N, C>]) -> Vec<(N, N)>
where
    N: Clone + Ord,
{
    let mut parent = BTreeMap::new();
    for commit in commits {
        if let Some(parent_node) = &commit.parent {
            parent.insert(commit.node.clone(), parent_node.clone());
        }
    }
    parent.into_iter().collect()
}

fn derive_incumbent_publication_trace<N, C>(
    start: &N,
    goal: &N,
    commits: &[NormalizedCommitRecord<N, C>],
) -> Vec<IncumbentPublicationRecord<N, C>>
where
    N: Clone + Ord,
    C: SearchCost,
{
    let mut g_score = BTreeMap::new();
    let mut parent = BTreeMap::new();
    let mut publications = Vec::new();
    g_score.insert(start.clone(), C::zero());

    for commit in commits {
        g_score.insert(commit.node.clone(), commit.g_score);
        if let Some(parent_node) = &commit.parent {
            parent.insert(commit.node.clone(), parent_node.clone());
        }
        if &commit.node == goal {
            let Some(path) = reconstruct_path(start, goal, &parent) else {
                continue;
            };
            publications.push(IncumbentPublicationRecord {
                cost: commit.g_score,
                path,
            });
        }
    }

    publications
}

fn reconstruct_incumbent_from_commits<N, C>(
    start: &N,
    goal: &N,
    commits: &[NormalizedCommitRecord<N, C>],
) -> (Option<C>, Option<Vec<N>>)
where
    N: Clone + Ord,
    C: SearchCost,
{
    let mut g_score = BTreeMap::new();
    let mut parent = BTreeMap::new();
    g_score.insert(start.clone(), C::zero());

    for commit in commits {
        g_score.insert(commit.node.clone(), commit.g_score);
        if let Some(parent_node) = &commit.parent {
            parent.insert(commit.node.clone(), parent_node.clone());
        }
    }

    let incumbent_cost = g_score.get(goal).copied();
    let incumbent_path = incumbent_cost.and_then(|_| reconstruct_path(start, goal, &parent));
    (incumbent_cost, incumbent_path)
}

fn reconstruct_path<N>(start: &N, goal: &N, parent: &BTreeMap<N, N>) -> Option<Vec<N>>
where
    N: Clone + Ord,
{
    let mut path = vec![goal.clone()];
    let mut cursor = goal.clone();
    while cursor != *start {
        let next = parent.get(&cursor)?.clone();
        if path.contains(&next) {
            return None;
        }
        cursor = next;
        path.push(cursor.clone());
    }
    path.reverse();
    Some(path)
}

impl<D: SearchDomain> SearchMachine<D> {
    /// Internal mutable state access for runtime orchestration.
    pub(crate) fn state_mut(&mut self) -> &mut RuntimeState<D> {
        &mut self.state
    }

    /// Borrow the domain adapter.
    pub(crate) fn domain(&self) -> &D {
        &self.domain
    }

    /// Borrow the current goal.
    pub(crate) fn goal(&self) -> &D::Node {
        &self.goal
    }

    /// Rebuild one frontier entry under the current epoch and epsilon.
    pub(crate) fn rebuild_frontier_entry(
        &self,
        node: &D::Node,
        g_score: D::Cost,
    ) -> FrontierEntry<D::Node, D::Cost> {
        Self::frontier_entry_for(
            &self.domain,
            &self.state.graph_epoch,
            &self.goal,
            self.state.epsilon,
            node,
            g_score,
        )
    }
}

/// Placeholder runtime marker retained for smoke tests.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SearchRuntimeMarker;
