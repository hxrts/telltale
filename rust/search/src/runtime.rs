//! Runtime, scheduler, replay, and reconfiguration boundary for
//! `telltale-search`.

use std::collections::BTreeSet;

#[cfg(feature = "multi-thread")]
use rayon::prelude::*;
use serde::{Deserialize, Serialize};

use crate::admission::{SearchFairnessAssumption, SearchSchedulerProfile};
use crate::cost::SearchCost;
use crate::domain::SearchDomain;
use crate::machine::{
    CanonicalBatch, FrontierEntry, Proposal, ProposalKind, SearchError, SearchMachine, SearchState,
};
use crate::observe::{NormalizedCommitRecord, SearchObservationArtifact};

/// Machine authority surface touched by speculative proposals.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum AuthoritySurface {
    /// Incumbent publication state.
    Incumbent,
    /// Replay-visible batch descriptor.
    BatchWindow,
    /// Replay-visible phase state.
    Phase,
    /// Replay-visible graph epoch state.
    GraphEpoch,
    /// Normalized commit trace.
    CommitTrace,
}

/// Read summary for one proposal.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct AuthorityReadSet<N>
where
    N: Ord,
{
    /// Target nodes read by the proposal.
    pub target_nodes: BTreeSet<N>,
    /// Non-node authority surfaces read by the proposal.
    pub surfaces: BTreeSet<AuthoritySurface>,
}

/// Write summary for one proposal.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct AuthorityWriteSet<N>
where
    N: Ord,
{
    /// Target nodes written by the proposal.
    pub target_nodes: BTreeSet<N>,
    /// Non-node authority surfaces written by the proposal.
    pub surfaces: BTreeSet<AuthoritySurface>,
}

impl<N> Default for AuthorityReadSet<N>
where
    N: Ord,
{
    fn default() -> Self {
        Self {
            target_nodes: BTreeSet::new(),
            surfaces: BTreeSet::new(),
        }
    }
}

impl<N> Default for AuthorityWriteSet<N>
where
    N: Ord,
{
    fn default() -> Self {
        Self {
            target_nodes: BTreeSet::new(),
            surfaces: BTreeSet::new(),
        }
    }
}

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
    pub fairness_assumptions: Vec<SearchFairnessAssumption>,
}

/// Scheduler artifact for one run.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SchedulerArtifact {
    /// Declared scheduler class.
    pub scheduler_profile: SearchSchedulerProfile,
    /// Whether the scheduler artifact is exact, normalized, or only diagnostic.
    pub authority_class: SchedulerArtifactClass,
    /// Configured batch width.
    pub batch_width: usize,
    /// Declared fairness assumptions.
    pub fairness_assumptions: Vec<SearchFairnessAssumption>,
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
    /// Declared scheduler profile.
    pub scheduler_profile: SearchSchedulerProfile,
    /// Declared fairness assumptions.
    pub fairness_assumptions: Vec<SearchFairnessAssumption>,
    /// Graph epoch trace for the run.
    pub epoch_trace: Vec<G>,
    /// Canonical replay rounds.
    pub rounds: Vec<ReplayRoundRecord<N, G, S, C>>,
    /// Final observed artifact.
    pub final_observation: SearchObservationArtifact<N, G, C>,
}

/// Replay-time contract expected by the caller.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReplayExpectation<G> {
    /// Expected graph epoch trace.
    pub expected_epochs: Vec<G>,
    /// Expected per-round phase sequence.
    pub expected_phases: Vec<u64>,
    /// Required fairness assumptions for theorem-style comparisons.
    pub required_fairness: Vec<SearchFairnessAssumption>,
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
    EpochMismatch,
    /// The replay artifact phase schedule does not match the requested schedule.
    PhaseMismatch,
    /// The replay artifact fairness bundle does not satisfy the requested
    /// theorem-style premise bundle.
    FairnessMismatch,
}

/// Runtime executor for speculative proposal generation.
pub trait ProposalExecutor<D: SearchDomain> {
    /// Generate speculative proposals for one frozen batch.
    ///
    /// # Errors
    ///
    /// Returns an error if the domain fails during successor enumeration.
    fn generate(
        &self,
        domain: &D,
        batch: &CanonicalBatch<D::Node, D::GraphEpoch, D::SnapshotId, D::Cost>,
        goal: &D::Node,
    ) -> Result<Vec<Proposal<D::Node, D::EdgeMeta, D::Cost>>, D::Error>;
}

/// Serial executor over a canonical batch.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SerialProposalExecutor;

impl<D: SearchDomain> ProposalExecutor<D> for SerialProposalExecutor {
    fn generate(
        &self,
        domain: &D,
        batch: &CanonicalBatch<D::Node, D::GraphEpoch, D::SnapshotId, D::Cost>,
        goal: &D::Node,
    ) -> Result<Vec<Proposal<D::Node, D::EdgeMeta, D::Cost>>, D::Error> {
        let mut proposals = Vec::new();
        for (batch_index, entry) in batch.entries.iter().enumerate() {
            let mut successors = Vec::new();
            domain.successors(&batch.epoch, &entry.node, &mut successors)?;
            successors.sort_by(|left, right| left.0.cmp(&right.0));
            for (to, edge, edge_cost) in successors {
                proposals.push(Proposal {
                    batch_index,
                    from: entry.node.clone(),
                    to: to.clone(),
                    edge,
                    edge_cost,
                    tentative_g: entry.g_score.saturating_add(edge_cost),
                    kind: ProposalKind::Relax,
                    read_set: proposal_read_set(&entry.node, &to),
                    write_set: proposal_write_set(&to, goal),
                });
            }
        }
        let _ = goal;
        Ok(proposals)
    }
}

/// Native parallel executor over a canonical batch.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NativeParallelExecutor {
    /// Maximum batch width to execute.
    pub batch_width: usize,
}

#[cfg(feature = "multi-thread")]
impl<D> ProposalExecutor<D> for NativeParallelExecutor
where
    D: SearchDomain + Sync,
    D::Node: Sync,
    D::EdgeMeta: Send,
    D::GraphEpoch: Sync,
    D::Error: Send,
{
    fn generate(
        &self,
        domain: &D,
        batch: &CanonicalBatch<D::Node, D::GraphEpoch, D::SnapshotId, D::Cost>,
        goal: &D::Node,
    ) -> Result<Vec<Proposal<D::Node, D::EdgeMeta, D::Cost>>, D::Error> {
        let _ = goal;
        let mut per_entry = batch
            .entries
            .iter()
            .take(self.batch_width.max(1))
            .cloned()
            .enumerate()
            .collect::<Vec<_>>();
        per_entry.sort_by(|left, right| left.1.node.cmp(&right.1.node));
        let mut results = per_entry
            .into_par_iter()
            .map(|(batch_index, entry)| {
                let mut successors = Vec::new();
                domain.successors(&batch.epoch, &entry.node, &mut successors)?;
                successors.sort_by(|left, right| left.0.cmp(&right.0));
                let proposals = successors
                    .into_iter()
                    .map(|(to, edge, edge_cost)| Proposal {
                        batch_index,
                        from: entry.node.clone(),
                        to: to.clone(),
                        edge,
                        edge_cost,
                        tentative_g: entry.g_score.saturating_add(edge_cost),
                        kind: ProposalKind::Relax,
                        read_set: proposal_read_set(&entry.node, &to),
                        write_set: proposal_write_set(&to, goal),
                    })
                    .collect::<Vec<_>>();
                Ok::<_, D::Error>(proposals)
            })
            .collect::<Vec<_>>();

        let mut proposals = Vec::new();
        for result in results.drain(..) {
            proposals.extend(result?);
        }
        Ok(proposals)
    }
}

#[cfg(not(feature = "multi-thread"))]
impl<D: SearchDomain> ProposalExecutor<D> for NativeParallelExecutor {
    fn generate(
        &self,
        domain: &D,
        batch: &CanonicalBatch<D::Node, D::GraphEpoch, D::SnapshotId, D::Cost>,
        goal: &D::Node,
    ) -> Result<Vec<Proposal<D::Node, D::EdgeMeta, D::Cost>>, D::Error> {
        let serial = SerialProposalExecutor;
        let _ = self.batch_width;
        serial.generate(domain, batch, goal)
    }
}

/// Execute one machine to completion through one proposal executor.
pub fn run_with_executor<D, X>(
    machine: &mut SearchMachine<D>,
    executor: &X,
    scheduler_profile: SearchSchedulerProfile,
    batch_width: usize,
    fairness_assumptions: Vec<SearchFairnessAssumption>,
) -> Result<
    (
        SearchExecutionReport<D::Node, D::GraphEpoch, D::Cost>,
        SearchReplayArtifact<D::Node, D::GraphEpoch, D::SnapshotId, D::Cost>,
    ),
    SearchError<D::Error>,
>
where
    D: SearchDomain,
    X: ProposalExecutor<D>,
{
    let mut rounds = Vec::new();
    while let Some(batch) = machine.next_batch() {
        machine.state_mut().trace_state.total_scheduler_steps += 1;
        let pre_commit_len = machine.state().normalized_commit_trace.len();
        let mut proposals = executor
            .generate(machine.domain(), &batch, machine.goal())
            .map_err(SearchError::Domain)?;
        machine.normalize_proposals(&mut proposals);
        let changed = machine.commit_proposals(&proposals);
        machine.state_mut().budget_state.expansions += batch.entries.len() as u64;
        machine.state_mut().budget_state.batches += 1;
        if changed {
            machine.state_mut().trace_state.productive_steps += 1;
        }
        machine
            .check_invariants()
            .map_err(SearchError::InvariantViolation)?;

        let round_commits = machine.state().normalized_commit_trace[pre_commit_len..].to_vec();
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

    let observation = machine.observation_artifact(scheduler_profile, fairness_assumptions.clone());
    let total_step_mode = match scheduler_profile {
        SearchSchedulerProfile::CanonicalSerial
        | SearchSchedulerProfile::ThreadedExactSingleLane
        | SearchSchedulerProfile::BatchedParallelExact => TotalStepMode::Exact,
        SearchSchedulerProfile::BatchedParallelEnvelopeBounded => TotalStepMode::FairnessBounded,
    };
    let progress = ProgressSummary {
        productive_steps: observation.productive_steps,
        total_scheduler_steps: observation.total_scheduler_steps,
        total_step_mode,
        fairness_assumptions: fairness_assumptions.clone(),
    };
    let scheduler = SchedulerArtifact {
        scheduler_profile,
        authority_class: classify_scheduler_artifact(scheduler_profile),
        batch_width,
        fairness_assumptions: fairness_assumptions.clone(),
    };
    let replay = SearchReplayArtifact {
        scheduler_profile,
        fairness_assumptions,
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

/// Determine whether two proposals are independent on the machine authority
/// surface.
#[must_use]
pub fn proposals_independent<N>(
    left: &Proposal<N, impl Clone, impl SearchCost>,
    right: &Proposal<N, impl Clone, impl SearchCost>,
) -> bool
where
    N: Clone + Ord,
{
    left.write_set
        .target_nodes
        .is_disjoint(&right.write_set.target_nodes)
        && left
            .write_set
            .target_nodes
            .is_disjoint(&right.read_set.target_nodes)
        && right
            .write_set
            .target_nodes
            .is_disjoint(&left.read_set.target_nodes)
        && left
            .write_set
            .surfaces
            .is_disjoint(&right.write_set.surfaces)
        && left
            .write_set
            .surfaces
            .is_disjoint(&right.read_set.surfaces)
        && right
            .write_set
            .surfaces
            .is_disjoint(&left.read_set.surfaces)
}

/// Commit one pending epoch update at a machine barrier.
pub fn commit_epoch_reconfiguration<D: SearchDomain>(
    machine: &mut SearchMachine<D>,
    request: EpochReconfigurationRequest<D::GraphEpoch>,
) {
    let next_snapshot = machine.domain().snapshot_id(&request.next_epoch);
    machine.state_mut().phase += 1;
    machine.state_mut().graph_epoch = request.next_epoch.clone();
    machine.state_mut().graph_snapshot_id = next_snapshot;
    machine
        .state_mut()
        .graph_epoch_trace
        .push(request.next_epoch);
    machine.state_mut().closed.clear();
    machine.state_mut().incons.clear();
    machine.state_mut().last_batch = None;

    let all_nodes = machine
        .state()
        .g_score
        .iter()
        .map(|(node, cost)| (node.clone(), *cost))
        .collect::<Vec<_>>();
    machine.state_mut().open.clear();
    for (node, g_score) in all_nodes {
        let entry = machine.rebuild_frontier_entry(&node, g_score);
        machine.state_mut().open.insert(node, entry);
    }
}

/// Replay one canonical observation artifact under an expected epoch schedule.
pub fn replay_observation<N, G, S, C>(
    replay: &SearchReplayArtifact<N, G, S, C>,
    expectation: &ReplayExpectation<G>,
) -> Result<SearchObservationArtifact<N, G, C>, ReplayError>
where
    N: Clone + Ord,
    G: Clone + Ord,
    S: Clone + Ord,
    C: SearchCost,
{
    if replay.epoch_trace != expectation.expected_epochs {
        return Err(ReplayError::EpochMismatch);
    }
    let replay_phases = replay
        .rounds
        .iter()
        .map(|round| round.phase)
        .collect::<Vec<_>>();
    if replay_phases != expectation.expected_phases {
        return Err(ReplayError::PhaseMismatch);
    }
    if !expectation
        .required_fairness
        .iter()
        .all(|assumption| replay.fairness_assumptions.contains(assumption))
    {
        return Err(ReplayError::FairnessMismatch);
    }
    Ok(replay.final_observation.clone())
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

fn proposal_read_set<N>(from: &N, to: &N) -> AuthorityReadSet<N>
where
    N: Clone + Ord,
{
    let mut target_nodes = BTreeSet::new();
    target_nodes.insert(from.clone());
    target_nodes.insert(to.clone());
    let mut surfaces = BTreeSet::new();
    surfaces.insert(AuthoritySurface::BatchWindow);
    surfaces.insert(AuthoritySurface::GraphEpoch);
    surfaces.insert(AuthoritySurface::Phase);
    AuthorityReadSet {
        target_nodes,
        surfaces,
    }
}

fn proposal_write_set<N>(to: &N, goal: &N) -> AuthorityWriteSet<N>
where
    N: Clone + Ord,
{
    let mut target_nodes = BTreeSet::new();
    target_nodes.insert(to.clone());
    let mut surfaces = BTreeSet::new();
    if to == goal {
        surfaces.insert(AuthoritySurface::Incumbent);
    }
    AuthorityWriteSet {
        target_nodes,
        surfaces,
    }
}

impl<D: SearchDomain> SearchMachine<D> {
    /// Internal mutable state access for runtime orchestration.
    pub(crate) fn state_mut(
        &mut self,
    ) -> &mut SearchState<D::Node, D::EdgeMeta, D::GraphEpoch, D::SnapshotId, D::Cost> {
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

#[cfg(test)]
mod tests {
    use std::collections::BTreeMap;

    use crate::admission::{
        SearchDeterminismMode, SearchFairnessAssumption, SearchObservableClass,
        SearchSchedulerProfile,
    };
    use crate::cost::EpsilonMilli;
    use crate::domain::SearchDomain;
    use crate::machine::SearchMachine;
    use crate::observe::{compare_observations, ObservationRelation};

    use super::*;

    #[derive(Clone, Debug, Default)]
    struct TestDomain {
        edges: BTreeMap<u8, Vec<(u8, &'static str, u64)>>,
        heuristics: BTreeMap<(u64, u8), u64>,
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
            epoch: &Self::GraphEpoch,
            node: &Self::Node,
            _goal: &Self::Node,
        ) -> Self::Cost {
            *self.heuristics.get(&(*epoch, *node)).unwrap_or(&0)
        }

        fn snapshot_id(&self, epoch: &Self::GraphEpoch) -> Self::SnapshotId {
            if *epoch == 1 {
                "epoch-1"
            } else {
                "epoch-2"
            }
        }
    }

    fn make_domain() -> TestDomain {
        let mut domain = TestDomain::default();
        domain.edges.insert(0, vec![(1, "0-1", 1), (2, "0-2", 1)]);
        domain.edges.insert(1, vec![(3, "1-3", 1)]);
        domain.edges.insert(2, vec![(3, "2-3", 1)]);
        domain.heuristics.insert((1, 1), 0);
        domain.heuristics.insert((1, 2), 0);
        domain.heuristics.insert((2, 1), 1);
        domain.heuristics.insert((2, 2), 0);
        domain
    }

    #[test]
    fn serial_and_parallel_batch_width_one_are_exactly_equal() {
        let domain = make_domain();
        let mut left = SearchMachine::new(domain.clone(), 1, 0, 3, EpsilonMilli::one());
        let mut right = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
        let (left_report, _) = run_with_executor(
            &mut left,
            &SerialProposalExecutor,
            SearchSchedulerProfile::CanonicalSerial,
            1,
            vec![SearchFairnessAssumption::DeterministicSchedulerConfluence],
        )
        .expect("serial run");
        let (right_report, _) = run_with_executor(
            &mut right,
            &NativeParallelExecutor { batch_width: 1 },
            SearchSchedulerProfile::ThreadedExactSingleLane,
            1,
            vec![SearchFairnessAssumption::DeterministicSchedulerConfluence],
        )
        .expect("parallel run");
        assert_eq!(
            left_report.observation.incumbent_cost,
            right_report.observation.incumbent_cost
        );
        assert_eq!(
            left_report.observation.incumbent_path,
            right_report.observation.incumbent_path
        );
        assert_eq!(
            left_report.observation.normalized_commit_trace,
            right_report.observation.normalized_commit_trace
        );
        assert_eq!(right_report.progress.total_step_mode, TotalStepMode::Exact);
        assert_eq!(
            classify_scheduler_artifact(SearchSchedulerProfile::ThreadedExactSingleLane),
            SchedulerArtifactClass::Exact
        );
    }

    #[test]
    fn parallel_envelope_run_is_admitted_modulo_commutativity() {
        let domain = make_domain();
        let mut serial = SearchMachine::new(domain.clone(), 1, 0, 3, EpsilonMilli::one());
        let mut parallel = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
        let (serial_report, _) = run_with_executor(
            &mut serial,
            &SerialProposalExecutor,
            SearchSchedulerProfile::CanonicalSerial,
            1,
            vec![SearchFairnessAssumption::DeterministicSchedulerConfluence],
        )
        .expect("serial run");
        let (parallel_report, _) = run_with_executor(
            &mut parallel,
            &NativeParallelExecutor { batch_width: 2 },
            SearchSchedulerProfile::BatchedParallelEnvelopeBounded,
            2,
            vec![
                SearchFairnessAssumption::DeterministicSchedulerConfluence,
                SearchFairnessAssumption::NoStarvationWithinLegalWindow,
            ],
        )
        .expect("parallel run");
        let comparison = compare_observations(
            &serial_report.observation,
            &parallel_report.observation,
            SearchDeterminismMode::ModuloCommutativity,
            &[
                SearchObservableClass::IncumbentCost,
                SearchObservableClass::CanonicalPathIdentity,
                SearchObservableClass::NormalizedCommitTrace,
            ],
        );
        assert!(matches!(
            comparison.relation,
            ObservationRelation::Exact | ObservationRelation::EquivalentModuloCommutativity
        ));
        assert_eq!(
            parallel_report.progress.total_step_mode,
            TotalStepMode::FairnessBounded
        );
        assert_eq!(
            parallel_report.scheduler.authority_class,
            SchedulerArtifactClass::Normalized
        );
    }

    #[test]
    fn fairness_free_exact_claims_are_distinct_from_fairness_bounded_claims() {
        let domain = make_domain();
        let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
        let (report, _) = run_with_executor(
            &mut machine,
            &NativeParallelExecutor { batch_width: 2 },
            SearchSchedulerProfile::BatchedParallelEnvelopeBounded,
            2,
            vec![SearchFairnessAssumption::EventualLiveBatchService],
        )
        .expect("parallel run");
        assert_eq!(
            report.progress.total_step_mode,
            TotalStepMode::FairnessBounded
        );
        assert_eq!(
            report.progress.productive_steps,
            report.observation.productive_steps
        );
        assert_ne!(
            report.progress.fairness_assumptions,
            vec![SearchFairnessAssumption::DeterministicSchedulerConfluence]
        );
    }

    #[test]
    fn reconfiguration_commits_new_epoch_at_barrier() {
        let domain = make_domain();
        let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
        machine.step_once().expect("first step");
        commit_epoch_reconfiguration(&mut machine, EpochReconfigurationRequest { next_epoch: 2 });
        assert_eq!(machine.state().phase, 1);
        assert_eq!(machine.state().graph_epoch, 2);
        assert_eq!(machine.state().graph_epoch_trace, vec![1, 2]);
    }

    #[test]
    fn replay_rejects_mismatched_epoch_schedule() {
        let domain = make_domain();
        let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
        let (_, replay) = run_with_executor(
            &mut machine,
            &SerialProposalExecutor,
            SearchSchedulerProfile::CanonicalSerial,
            1,
            vec![SearchFairnessAssumption::DeterministicSchedulerConfluence],
        )
        .expect("serial run");
        let err = replay_observation(
            &replay,
            &ReplayExpectation {
                expected_epochs: vec![1, 2],
                expected_phases: replay.rounds.iter().map(|round| round.phase).collect(),
                required_fairness: vec![SearchFairnessAssumption::DeterministicSchedulerConfluence],
            },
        )
        .expect_err("mismatched epochs");
        assert_eq!(err, ReplayError::EpochMismatch);
    }

    #[test]
    fn replay_rejects_mismatched_phase_or_fairness_premises() {
        let domain = make_domain();
        let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
        let (_, replay) = run_with_executor(
            &mut machine,
            &NativeParallelExecutor { batch_width: 2 },
            SearchSchedulerProfile::BatchedParallelEnvelopeBounded,
            2,
            vec![SearchFairnessAssumption::EventualLiveBatchService],
        )
        .expect("parallel run");

        let phase_err = replay_observation(
            &replay,
            &ReplayExpectation {
                expected_epochs: replay.epoch_trace.clone(),
                expected_phases: vec![999],
                required_fairness: vec![SearchFairnessAssumption::EventualLiveBatchService],
            },
        )
        .expect_err("mismatched phases");
        assert_eq!(phase_err, ReplayError::PhaseMismatch);

        let fairness_err = replay_observation(
            &replay,
            &ReplayExpectation {
                expected_epochs: replay.epoch_trace.clone(),
                expected_phases: replay.rounds.iter().map(|round| round.phase).collect(),
                required_fairness: vec![SearchFairnessAssumption::DeterministicSchedulerConfluence],
            },
        )
        .expect_err("mismatched fairness bundle");
        assert_eq!(fairness_err, ReplayError::FairnessMismatch);
    }
}
