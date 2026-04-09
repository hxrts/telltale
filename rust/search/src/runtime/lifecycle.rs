use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::admission::{
    SearchDeterminismMode, SearchFairnessAssumption, SearchObservableClass, SearchSchedulerProfile,
};
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

/// Public fairness-claim class for one search scheduler profile.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchFairnessClaimClass {
    /// Exact one-step fairness for the current legal min-key batch.
    ExactOneStep,
    /// Exact one-step fairness inherited through proved one-step refinement to
    /// canonical serial search.
    ExactOneStepViaThreadedRefinement,
    /// Premise-scoped bounded-window fairness only.
    PremisedWindowBounded,
    /// Premise-only; no unconditional fairness theorem is claimed.
    PremiseOnly,
}

/// Public discovery-bound class for one selected route.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchRouteDiscoveryBoundClass {
    /// The bound is an exact observed value derived from the committed replay
    /// rounds of this run.
    ObservedRunBound,
    /// The observed bound is accompanied by the current theorem-backed
    /// goal-window service certificate.
    ObservedRunBoundWithGoalWindowCertificate,
    /// No candidate route was published during the run.
    NoCandidate,
}

/// Theorem-backed discovery certificate class for one selected route.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchRouteDiscoveryCertificateClass {
    /// The goal was in the legal service window and canonical serial search
    /// serviced it within the proved one-step bound.
    GoalWindowOneStepExact,
    /// The goal-window service bound is inherited through exact threaded
    /// refinement to canonical serial search.
    GoalWindowOneStepViaThreadedRefinement,
    /// The goal-window service bound is certified only under the exact batched
    /// premises.
    CertifiedGoalWindowService,
}

/// Theorem-backed discovery certificate for one selected route.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchRouteDiscoveryCertificate {
    /// Discovery theorem class.
    pub class: SearchRouteDiscoveryCertificateClass,
    /// Certified service bound in scheduler steps once the goal is in the
    /// current legal service window.
    pub service_bound_steps: u64,
    /// Observed scheduler-step index at which the goal first appears in the
    /// certified legal service window for this run.
    pub observed_goal_window_step: u64,
    /// Premises required by this certificate.
    pub required_premises: BTreeSet<SearchFairnessAssumption>,
    /// Search-visible observables justified by this certificate.
    pub certified_observables: BTreeSet<SearchObservableClass>,
}

/// Public route-quality class for one selected route.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchRouteQualityClass {
    /// Exact profiles produced an optimal route.
    ExactOptimal,
    /// The route quality is only justified under the certified exact-window
    /// premises.
    PremisedWindowBounded,
    /// The route quality remains premise-only.
    PremiseOnly,
    /// No candidate route was published during the run.
    NoCandidate,
}

/// Public route discovery and quality artifact for one run.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchRouteBoundArtifact<C> {
    /// Class of the candidate discovery bound.
    pub discovery_class: SearchRouteDiscoveryBoundClass,
    /// Observed scheduler-step bound until the first route candidate is
    /// published.
    pub candidate_discovery_bound_steps: Option<u64>,
    /// Theorem-backed bound, when available, once the goal is in the legal
    /// service window for the current profile.
    pub goal_service_bound_steps: Option<u64>,
    /// Observed scheduler-step bound until the goal first appears in the legal
    /// service window for the selected route.
    pub goal_window_entry_bound_steps: Option<u64>,
    /// Structured theorem-backed discovery certificate for the current profile
    /// when the public proof surface can justify one.
    pub discovery_certificate: Option<SearchRouteDiscoveryCertificate>,
    /// Observed scheduler-step bound from the latest epoch transition to the
    /// first route candidate published in that epoch.
    pub recovery_bound_steps_after_latest_epoch: Option<u64>,
    /// Class of the selected route quality claim.
    pub quality_class: SearchRouteQualityClass,
    /// Selected route cost if a candidate exists.
    pub selected_route_cost: Option<C>,
    /// Optimality gap when the current claim surface can justify one.
    pub optimality_gap: Option<C>,
    /// Approximation ratio in milli units when the current claim surface can
    /// justify one.
    pub approximation_ratio_milli: Option<u64>,
    /// Admissible upper bound on the selected route cost.
    pub admissible_upper_bound: Option<C>,
    /// Compact selected-route summary for downstream reporting.
    pub selected_route_summary: Option<SearchRouteSummary<C>>,
    /// Premises required by the selected route claim.
    pub required_premises: BTreeSet<SearchFairnessAssumption>,
}

/// Compact selected-route summary exported alongside route bounds.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchRouteSummary<C> {
    /// Selected route cost.
    pub cost: C,
    /// Number of hops in the selected route.
    pub hop_count: u64,
    /// Number of incumbent publications observed during the run.
    pub publication_count: u64,
    /// Number of canonical normalized commits observed during the run.
    pub normalized_commit_count: u64,
    /// Number of distinct epochs traversed by this run.
    pub traversed_epoch_count: u64,
    /// Generic route metrics exported in stable canonical order for downstream
    /// reporting and comparison.
    pub metrics: Vec<SearchRouteMetric>,
}

/// Stable metric name for generic route summaries.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchRouteMetricName {
    /// Total nodes on the selected route.
    PathNodeCount,
    /// Total edges on the selected route.
    HopCount,
    /// Stable scalar ordering key for the selected route cost.
    ScalarCostOrderKey,
    /// Number of incumbent publications observed during the run.
    PublicationCount,
    /// Number of canonical normalized commits observed during the run.
    NormalizedCommitCount,
    /// Number of epochs traversed during the run.
    TraversedEpochCount,
}

/// One generic route metric exported with the selected-route summary.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchRouteMetric {
    /// Stable metric identity.
    pub name: SearchRouteMetricName,
    /// Metric value in canonical integer form.
    pub value: u128,
}

/// Public fairness artifact for one run.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchFairnessArtifact<N, G, C>
where
    N: Ord,
    G: Ord,
{
    /// Declared scheduler profile.
    pub scheduler_profile: SearchSchedulerProfile,
    /// Public fairness claim class for that profile.
    pub claim_class: SearchFairnessClaimClass,
    /// Mirrored theorem-evidence certificate for this profile.
    pub certificate: SearchFairnessCertificate<N, G, C>,
    /// Whether the reduced normalized commit trace is theorem-claimed to match
    /// canonical serial search exactly.
    pub exact_commit_trace_refines_canonical: bool,
    /// Whether the reduced authoritative state slice is theorem-claimed to
    /// match canonical serial search exactly.
    pub exact_state_slice_refines_canonical: bool,
    /// Whether the reduced observable slice is theorem-claimed to match
    /// canonical serial search exactly.
    pub exact_observation_equivalent_to_canonical: bool,
}

/// Theorem-evidence certificate class for one search fairness artifact.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchFairnessCertificateClass {
    /// Exact current min-key batch service.
    CurrentMinKeyBatch,
    /// Exact current min-key batch service via exact threaded refinement to
    /// canonical serial search.
    CurrentMinKeyBatchViaThreadedRefinement,
    /// Certified current min-key window service under explicit premises.
    CertifiedCurrentMinKeyWindow,
    /// No unconditional or certified fairness certificate is attached.
    None,
}

/// First-class fairness certificate mirrored from the Lean theorem surface.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchFairnessCertificate<N, G, C>
where
    N: Ord,
    G: Ord,
{
    /// The theorem-evidence class.
    pub class: SearchFairnessCertificateClass,
    /// Exact service bound when the theorem surface provides one.
    pub service_bound_steps: Option<u64>,
    /// The theorem-side fairness premises required by this certificate.
    pub required_fairness: BTreeSet<SearchFairnessAssumption>,
    /// Search-visible observation classes justified by the theorem surface for
    /// this certificate.
    pub certified_observables: BTreeSet<SearchObservableClass>,
    /// Determinism/normalization mode under which the certified observables are
    /// theorem-backed.
    pub normalization_mode: SearchDeterminismMode,
    /// Certified graph epoch for the representative window, when one concrete
    /// window is attached to the runtime artifact.
    pub certified_epoch: Option<G>,
    /// Certified search phase for the representative window, when one concrete
    /// window is attached to the runtime artifact.
    pub certified_phase: Option<u64>,
    /// Representative certified batch nodes emitted by the run for the
    /// theorem-visible window surface.
    pub certified_batch_nodes: Vec<N>,
    /// Representative certified normalized commits emitted by the run for the
    /// theorem-visible window surface.
    pub certified_normalized_commits: Vec<NormalizedCommitRecord<N, C>>,
}

/// One machine-readable theorem-inventory row exported through the search
/// theorem-pack artifact.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchTheoremInventoryEntry {
    /// Stable theorem inventory key.
    pub name: String,
    /// Whether the theorem is part of the currently proved surface.
    pub present: bool,
}

/// Release-facing search theorem-pack artifact mirrored from the Lean theorem
/// pack and exposed through the Rust runtime surface.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchTheoremPackArtifact {
    /// Machine-readable theorem inventory.
    pub inventory: Vec<SearchTheoremInventoryEntry>,
    /// Exact canonical service bound for the current theorem-pack surface.
    pub canonical_service_bound_steps: u64,
    /// Exact canonical route-discovery suffix bound once the goal is in the
    /// legal service window.
    pub canonical_goal_window_discovery_suffix_bound_steps: u64,
    /// Canonical local gate that validates the theorem-pack surface.
    pub gate: String,
}

/// Certified-window trace validation failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SearchFairnessTraceValidationError {
    /// A certificate trace and replay rounds differ in length.
    TraceLengthMismatch,
    /// A certificate step bound differs from the certified one-window contract.
    InvalidServiceBound,
    /// A certificate phase disagrees with the replay round.
    PhaseMismatch,
    /// A certificate epoch disagrees with the replay round.
    EpochMismatch,
    /// Certified batch nodes disagree with the replay round.
    BatchMismatch,
    /// Certified normalized commits disagree with the replay round.
    CommitMismatch,
}

/// Stable exported state artifact for one authoritative search-machine state.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchStateArtifact<N, G, C>
where
    N: Ord,
    G: Ord,
{
    /// Canonical open frontier nodes with their current `g` scores.
    pub open_nodes: Vec<(N, C)>,
    /// Canonical closed-set nodes.
    pub closed_nodes: Vec<N>,
    /// Canonical `g` scores.
    pub g_scores: Vec<(N, C)>,
    /// Canonical parent identities.
    pub parent_map: Vec<(N, N)>,
    /// Current incumbent cost.
    pub incumbent_cost: Option<C>,
    /// Current incumbent path.
    pub incumbent_path: Option<Vec<N>>,
    /// Frozen graph epoch.
    pub epoch: G,
    /// Current search phase.
    pub phase: u64,
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
    /// Fairness artifact.
    pub fairness: SearchFairnessArtifact<N, G, C>,
    /// Per-round fairness certificate trace.
    pub fairness_certificate_trace: Vec<SearchFairnessCertificate<N, G, C>>,
    /// Final authoritative state artifact.
    pub final_state: SearchStateArtifact<N, G, C>,
    /// Release-facing theorem-pack artifact for this run surface.
    pub theorem_pack: SearchTheoremPackArtifact,
    /// Route discovery and quality artifact for the selected route.
    pub route_bounds: SearchRouteBoundArtifact<C>,
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
    /// Authoritative state artifact after the round commits.
    pub state_after_round: SearchStateArtifact<N, G, C>,
    /// Theorem-facing fairness certificate for this round.
    pub fairness_certificate: SearchFairnessCertificate<N, G, C>,
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
    /// Public fairness artifact.
    pub fairness: SearchFairnessArtifact<N, G, C>,
    /// Per-round fairness certificate trace.
    pub fairness_certificate_trace: Vec<SearchFairnessCertificate<N, G, C>>,
    /// Graph epoch trace for the run.
    pub epoch_trace: Vec<G>,
    /// Canonical replay rounds.
    pub rounds: Vec<ReplayRoundRecord<N, G, S, C>>,
    /// Final authoritative state artifact.
    pub final_state: SearchStateArtifact<N, G, C>,
    /// Release-facing theorem-pack artifact for this run surface.
    pub theorem_pack: SearchTheoremPackArtifact,
    /// Route discovery and quality artifact for the selected route.
    pub route_bounds: SearchRouteBoundArtifact<C>,
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

/// Classify the public fairness claim for one scheduler profile.
#[must_use]
pub fn classify_fairness_claim(profile: SearchSchedulerProfile) -> SearchFairnessClaimClass {
    match profile {
        SearchSchedulerProfile::CanonicalSerial => SearchFairnessClaimClass::ExactOneStep,
        SearchSchedulerProfile::ThreadedExactSingleLane => {
            SearchFairnessClaimClass::ExactOneStepViaThreadedRefinement
        }
        SearchSchedulerProfile::BatchedParallelExact => {
            SearchFairnessClaimClass::PremisedWindowBounded
        }
        SearchSchedulerProfile::BatchedParallelEnvelopeBounded => {
            SearchFairnessClaimClass::PremiseOnly
        }
    }
}

/// Public observation classes justified by the current theorem surface for one
/// scheduler profile.
#[must_use]
pub fn theorem_backed_observables(
    profile: SearchSchedulerProfile,
) -> BTreeSet<SearchObservableClass> {
    match profile {
        SearchSchedulerProfile::CanonicalSerial
        | SearchSchedulerProfile::ThreadedExactSingleLane => [
            SearchObservableClass::IncumbentCost,
            SearchObservableClass::CanonicalParentIdentity,
            SearchObservableClass::CanonicalPathIdentity,
            SearchObservableClass::NormalizedCommitTrace,
            SearchObservableClass::ProgressAccounting,
        ]
        .into_iter()
        .collect(),
        SearchSchedulerProfile::BatchedParallelExact => {
            [SearchObservableClass::NormalizedCommitTrace]
                .into_iter()
                .collect()
        }
        SearchSchedulerProfile::BatchedParallelEnvelopeBounded => BTreeSet::new(),
    }
}

/// Release-facing theorem-pack artifact for the current search fairness proof
/// surface.
#[must_use]
pub fn search_theorem_pack_artifact() -> SearchTheoremPackArtifact {
    SearchTheoremPackArtifact {
        inventory: [
            ("search_canonical_serial_exact_one_step_fairness", true),
            (
                "search_canonical_serial_dynamic_liveness_under_stability",
                true,
            ),
            (
                "search_threaded_exact_single_lane_refines_canonical_one_step",
                true,
            ),
            (
                "search_threaded_exact_single_lane_commit_trace_refines_canonical",
                true,
            ),
            (
                "search_threaded_exact_single_lane_state_slice_refines_canonical",
                true,
            ),
            (
                "search_threaded_exact_single_lane_observation_slice_refines_canonical",
                true,
            ),
            (
                "search_threaded_exact_single_lane_observation_equivalent_to_canonical",
                true,
            ),
            (
                "search_threaded_exact_single_lane_multi_step_state_trace_refines_canonical",
                true,
            ),
            (
                "search_threaded_exact_single_lane_multi_step_observation_trace_refines_canonical",
                true,
            ),
            (
                "search_threaded_exact_single_lane_state_artifact_refines_canonical",
                true,
            ),
            (
                "search_threaded_exact_single_lane_multi_step_state_artifact_trace_refines_canonical",
                true,
            ),
            (
                "search_threaded_exact_single_lane_exact_one_step_fairness",
                true,
            ),
            (
                "search_batched_parallel_exact_certified_window_fairness",
                true,
            ),
            (
                "search_batched_parallel_exact_bounded_dynamic_starvation_freedom",
                true,
            ),
            (
                "search_batched_parallel_exact_certified_window_trace_valid",
                true,
            ),
            (
                "search_batched_parallel_envelope_unconditional_fairness",
                false,
            ),
            (
                "search_canonical_serial_goal_window_service_has_exact_suffix_bound",
                true,
            ),
            (
                "search_threaded_exact_single_lane_goal_window_service_has_exact_suffix_bound",
                true,
            ),
        ]
        .into_iter()
        .map(|(name, present)| SearchTheoremInventoryEntry {
            name: name.to_string(),
            present,
        })
        .collect(),
        canonical_service_bound_steps: 1,
        canonical_goal_window_discovery_suffix_bound_steps: 1,
        gate: "just check-search-fairness".to_string(),
    }
}

fn state_artifact_for_machine<D>(
    machine: &SearchMachine<D>,
) -> SearchStateArtifact<D::Node, D::GraphEpoch, D::Cost>
where
    D: SearchDomain,
{
    SearchStateArtifact {
        open_nodes: machine
            .state()
            .open
            .iter()
            .map(|(node, entry)| (node.clone(), entry.g_score))
            .collect(),
        closed_nodes: machine.state().closed.iter().cloned().collect(),
        g_scores: machine
            .state()
            .g_score
            .iter()
            .map(|(node, score)| (node.clone(), *score))
            .collect(),
        parent_map: machine
            .state()
            .parent
            .iter()
            .map(|(node, parent)| (node.clone(), parent.from.clone()))
            .collect(),
        incumbent_cost: machine
            .state()
            .incumbent
            .as_ref()
            .map(|incumbent| incumbent.cost),
        incumbent_path: machine
            .state()
            .incumbent
            .as_ref()
            .map(|incumbent| incumbent.path.clone()),
        epoch: machine.state().graph_epoch.clone(),
        phase: machine.state().phase,
    }
}

fn route_bound_artifact_for_replay<N, G, S, C>(
    profile: SearchSchedulerProfile,
    replay: &SearchReplayArtifact<N, G, S, C>,
) -> SearchRouteBoundArtifact<C>
where
    C: SearchCost,
    N: Ord,
    G: Clone + Ord,
    S: Ord,
{
    let selected_route_cost = replay.final_observation.incumbent_cost;
    let publication_count =
        u64::try_from(replay.final_observation.incumbent_publication_trace.len())
            .expect("publication count fits in u64");
    let normalized_commit_count =
        u64::try_from(replay.final_observation.normalized_commit_trace.len())
            .expect("normalized commit count fits in u64");
    let traversed_epoch_count =
        u64::try_from(replay.epoch_trace.len()).expect("epoch trace length fits in u64");
    let selected_route_summary = replay
        .final_observation
        .incumbent_path
        .as_ref()
        .zip(selected_route_cost)
        .map(|(path, cost)| {
            let path_node_count = u64::try_from(path.len()).expect("path node count fits in u64");
            let hop_count =
                u64::try_from(path.len().saturating_sub(1)).expect("hop count fits in u64");
            SearchRouteSummary {
                cost,
                hop_count,
                publication_count,
                normalized_commit_count,
                traversed_epoch_count,
                metrics: vec![
                    SearchRouteMetric {
                        name: SearchRouteMetricName::PathNodeCount,
                        value: u128::from(path_node_count),
                    },
                    SearchRouteMetric {
                        name: SearchRouteMetricName::HopCount,
                        value: u128::from(hop_count),
                    },
                    SearchRouteMetric {
                        name: SearchRouteMetricName::ScalarCostOrderKey,
                        value: cost.order_key(),
                    },
                    SearchRouteMetric {
                        name: SearchRouteMetricName::PublicationCount,
                        value: u128::from(publication_count),
                    },
                    SearchRouteMetric {
                        name: SearchRouteMetricName::NormalizedCommitCount,
                        value: u128::from(normalized_commit_count),
                    },
                    SearchRouteMetric {
                        name: SearchRouteMetricName::TraversedEpochCount,
                        value: u128::from(traversed_epoch_count),
                    },
                ],
            }
        });
    let candidate_discovery_bound_steps = replay
        .rounds
        .iter()
        .position(|round| round.state_after_round.incumbent_cost.is_some())
        .map(|index| u64::try_from(index + 1).expect("round index fits in u64"));
    let goal_window_entry_bound_steps = replay
        .rounds
        .iter()
        .position(|round| round.batch_nodes.contains(&replay.goal))
        .map(|index| u64::try_from(index + 1).expect("round index fits in u64"));
    let latest_epoch = replay.epoch_trace.last().cloned();
    let recovery_bound_steps_after_latest_epoch = latest_epoch.and_then(|latest_epoch| {
        replay
            .rounds
            .iter()
            .filter(|round| round.epoch == latest_epoch)
            .position(|round| round.state_after_round.incumbent_cost.is_some())
            .map(|index| u64::try_from(index + 1).expect("round index fits in u64"))
    });
    let required_premises = replay.fairness.certificate.required_fairness.clone();
    let goal_service_bound_steps = replay.fairness.certificate.service_bound_steps;
    let discovery_certificate =
        goal_window_entry_bound_steps.zip(goal_service_bound_steps).and_then(
            |(observed_goal_window_step, service_bound_steps)| {
                let class = match profile {
                    SearchSchedulerProfile::CanonicalSerial => {
                        SearchRouteDiscoveryCertificateClass::GoalWindowOneStepExact
                    }
                    SearchSchedulerProfile::ThreadedExactSingleLane => {
                        SearchRouteDiscoveryCertificateClass::GoalWindowOneStepViaThreadedRefinement
                    }
                    SearchSchedulerProfile::BatchedParallelExact => {
                        SearchRouteDiscoveryCertificateClass::CertifiedGoalWindowService
                    }
                    SearchSchedulerProfile::BatchedParallelEnvelopeBounded => {
                        unreachable!(
                            "envelope-bounded profiles do not carry a theorem-backed discovery certificate"
                        )
                    }
                };
                Some(SearchRouteDiscoveryCertificate {
                    class,
                    service_bound_steps,
                    observed_goal_window_step,
                    required_premises: replay.fairness.certificate.required_fairness.clone(),
                    certified_observables: replay.fairness.certificate.certified_observables.clone(),
                })
            },
        );

    match (selected_route_cost, profile) {
        (None, _) => SearchRouteBoundArtifact {
            discovery_class: SearchRouteDiscoveryBoundClass::NoCandidate,
            candidate_discovery_bound_steps: None,
            goal_service_bound_steps,
            goal_window_entry_bound_steps,
            discovery_certificate: None,
            recovery_bound_steps_after_latest_epoch: None,
            quality_class: SearchRouteQualityClass::NoCandidate,
            selected_route_cost: None,
            optimality_gap: None,
            approximation_ratio_milli: None,
            admissible_upper_bound: None,
            selected_route_summary: None,
            required_premises,
        },
        (Some(cost), SearchSchedulerProfile::CanonicalSerial)
        | (Some(cost), SearchSchedulerProfile::ThreadedExactSingleLane) => {
            SearchRouteBoundArtifact {
                discovery_class:
                    SearchRouteDiscoveryBoundClass::ObservedRunBoundWithGoalWindowCertificate,
                candidate_discovery_bound_steps,
                goal_service_bound_steps,
                goal_window_entry_bound_steps,
                discovery_certificate,
                recovery_bound_steps_after_latest_epoch,
                quality_class: SearchRouteQualityClass::ExactOptimal,
                selected_route_cost: Some(cost),
                optimality_gap: Some(C::zero()),
                approximation_ratio_milli: Some(1_000),
                admissible_upper_bound: Some(cost),
                selected_route_summary,
                required_premises,
            }
        }
        (Some(cost), SearchSchedulerProfile::BatchedParallelExact) => SearchRouteBoundArtifact {
            discovery_class:
                SearchRouteDiscoveryBoundClass::ObservedRunBoundWithGoalWindowCertificate,
            candidate_discovery_bound_steps,
            goal_service_bound_steps,
            goal_window_entry_bound_steps,
            discovery_certificate,
            recovery_bound_steps_after_latest_epoch,
            quality_class: SearchRouteQualityClass::PremisedWindowBounded,
            selected_route_cost: Some(cost),
            optimality_gap: None,
            approximation_ratio_milli: None,
            admissible_upper_bound: Some(cost),
            selected_route_summary,
            required_premises,
        },
        (Some(cost), SearchSchedulerProfile::BatchedParallelEnvelopeBounded) => {
            SearchRouteBoundArtifact {
                discovery_class: SearchRouteDiscoveryBoundClass::ObservedRunBound,
                candidate_discovery_bound_steps,
                goal_service_bound_steps,
                goal_window_entry_bound_steps,
                discovery_certificate: None,
                recovery_bound_steps_after_latest_epoch,
                quality_class: SearchRouteQualityClass::PremiseOnly,
                selected_route_cost: Some(cost),
                optimality_gap: None,
                approximation_ratio_milli: None,
                admissible_upper_bound: Some(cost),
                selected_route_summary,
                required_premises,
            }
        }
    }
}

/// Build the public fairness artifact for one scheduler profile.
#[must_use]
pub fn fairness_artifact_for_profile<N, C>(
    profile: SearchSchedulerProfile,
) -> SearchFairnessArtifact<N, (), C>
where
    N: Ord,
{
    fairness_artifact_for_window(profile, None, None, Vec::new(), Vec::new())
}

/// Build the public fairness artifact for one scheduler profile and one
/// representative theorem-visible certified window.
#[must_use]
fn fairness_artifact_for_window<N, G, C>(
    profile: SearchSchedulerProfile,
    certified_epoch: Option<G>,
    certified_phase: Option<u64>,
    certified_batch_nodes: Vec<N>,
    certified_normalized_commits: Vec<NormalizedCommitRecord<N, C>>,
) -> SearchFairnessArtifact<N, G, C>
where
    N: Ord,
    G: Ord,
{
    let required_fairness = match profile {
        SearchSchedulerProfile::CanonicalSerial => {
            [SearchFairnessAssumption::DeterministicSchedulerConfluence]
                .into_iter()
                .collect()
        }
        SearchSchedulerProfile::ThreadedExactSingleLane => {
            [SearchFairnessAssumption::DeterministicSchedulerConfluence]
                .into_iter()
                .collect()
        }
        SearchSchedulerProfile::BatchedParallelExact => [
            SearchFairnessAssumption::DeterministicSchedulerConfluence,
            SearchFairnessAssumption::EventualLiveBatchService,
            SearchFairnessAssumption::NoStarvationWithinLegalWindow,
        ]
        .into_iter()
        .collect(),
        SearchSchedulerProfile::BatchedParallelEnvelopeBounded => [
            SearchFairnessAssumption::EventualLiveBatchService,
            SearchFairnessAssumption::NoStarvationWithinLegalWindow,
        ]
        .into_iter()
        .collect(),
    };
    let claim_class = classify_fairness_claim(profile);
    let exposes_window_certificate = !matches!(claim_class, SearchFairnessClaimClass::PremiseOnly);
    let certificate = SearchFairnessCertificate {
        class: match claim_class {
            SearchFairnessClaimClass::ExactOneStep => {
                SearchFairnessCertificateClass::CurrentMinKeyBatch
            }
            SearchFairnessClaimClass::ExactOneStepViaThreadedRefinement => {
                SearchFairnessCertificateClass::CurrentMinKeyBatchViaThreadedRefinement
            }
            SearchFairnessClaimClass::PremisedWindowBounded => {
                SearchFairnessCertificateClass::CertifiedCurrentMinKeyWindow
            }
            SearchFairnessClaimClass::PremiseOnly => SearchFairnessCertificateClass::None,
        },
        service_bound_steps: match claim_class {
            SearchFairnessClaimClass::ExactOneStep
            | SearchFairnessClaimClass::ExactOneStepViaThreadedRefinement
            | SearchFairnessClaimClass::PremisedWindowBounded => Some(1),
            SearchFairnessClaimClass::PremiseOnly => None,
        },
        required_fairness,
        certified_observables: theorem_backed_observables(profile),
        normalization_mode: match claim_class {
            SearchFairnessClaimClass::ExactOneStep
            | SearchFairnessClaimClass::ExactOneStepViaThreadedRefinement => {
                SearchDeterminismMode::Full
            }
            SearchFairnessClaimClass::PremisedWindowBounded => {
                SearchDeterminismMode::ModuloCommutativity
            }
            SearchFairnessClaimClass::PremiseOnly => SearchDeterminismMode::Replay,
        },
        certified_epoch: if exposes_window_certificate {
            certified_epoch
        } else {
            None
        },
        certified_phase: if exposes_window_certificate {
            certified_phase
        } else {
            None
        },
        certified_batch_nodes: if exposes_window_certificate {
            certified_batch_nodes
        } else {
            Vec::new()
        },
        certified_normalized_commits: if exposes_window_certificate {
            certified_normalized_commits
        } else {
            Vec::new()
        },
    };
    SearchFairnessArtifact {
        scheduler_profile: profile,
        claim_class,
        certificate,
        exact_commit_trace_refines_canonical: matches!(
            claim_class,
            SearchFairnessClaimClass::ExactOneStep
                | SearchFairnessClaimClass::ExactOneStepViaThreadedRefinement
        ),
        exact_state_slice_refines_canonical: matches!(
            claim_class,
            SearchFairnessClaimClass::ExactOneStep
                | SearchFairnessClaimClass::ExactOneStepViaThreadedRefinement
        ),
        exact_observation_equivalent_to_canonical: matches!(
            claim_class,
            SearchFairnessClaimClass::ExactOneStep
                | SearchFairnessClaimClass::ExactOneStepViaThreadedRefinement
        ),
    }
}

fn fairness_certificate_for_round<N, G, C>(
    profile: SearchSchedulerProfile,
    epoch: G,
    phase: u64,
    batch_nodes: Vec<N>,
    commits: Vec<NormalizedCommitRecord<N, C>>,
) -> SearchFairnessCertificate<N, G, C>
where
    N: Ord,
    G: Ord,
{
    fairness_artifact_for_window(profile, Some(epoch), Some(phase), batch_nodes, commits)
        .certificate
}

/// Validate one exported fairness certificate trace against replay rounds.
pub fn validate_fairness_certificate_trace<N, G, S, C>(
    replay: &SearchReplayArtifact<N, G, S, C>,
) -> Result<(), SearchFairnessTraceValidationError>
where
    N: Clone + Ord,
    G: Clone + Ord,
    S: Ord,
    C: SearchCost,
{
    if replay.fairness_certificate_trace.len() != replay.rounds.len() {
        return Err(SearchFairnessTraceValidationError::TraceLengthMismatch);
    }
    for (certificate, round) in replay
        .fairness_certificate_trace
        .iter()
        .zip(replay.rounds.iter())
    {
        if certificate.service_bound_steps != Some(1) {
            return Err(SearchFairnessTraceValidationError::InvalidServiceBound);
        }
        if certificate.certified_epoch.as_ref() != Some(&round.epoch) {
            return Err(SearchFairnessTraceValidationError::EpochMismatch);
        }
        if certificate.certified_phase != Some(round.phase) {
            return Err(SearchFairnessTraceValidationError::PhaseMismatch);
        }
        if certificate.certified_batch_nodes != round.batch_nodes {
            return Err(SearchFairnessTraceValidationError::BatchMismatch);
        }
        if certificate.certified_normalized_commits != round.commits {
            return Err(SearchFairnessTraceValidationError::CommitMismatch);
        }
    }
    Ok(())
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
    let mut fairness_certificate_trace = Vec::new();
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
        let state_after_round = state_artifact_for_machine(machine);
        let fairness_certificate = fairness_certificate_for_round(
            config.scheduler_profile,
            batch.epoch.clone(),
            batch.phase,
            batch
                .entries
                .iter()
                .map(|entry| entry.node.clone())
                .collect(),
            round_commits.clone(),
        );
        fairness_certificate_trace.push(fairness_certificate.clone());
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
            state_after_round,
            fairness_certificate,
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
    let final_state = state_artifact_for_machine(machine);
    let theorem_pack = search_theorem_pack_artifact();
    let representative_window = rounds
        .first()
        .map(|round| (round.batch_nodes.clone(), round.commits.clone()))
        .unwrap_or_else(|| (Vec::new(), Vec::new()));
    let fairness = fairness_artifact_for_window(
        config.scheduler_profile,
        rounds.first().map(|round| round.epoch.clone()),
        rounds.first().map(|round| round.phase),
        representative_window.0,
        representative_window.1,
    );
    let replay = SearchReplayArtifact {
        start: machine.start.clone(),
        goal: machine.goal.clone(),
        scheduler_profile: config.scheduler_profile,
        fairness_assumptions: config.fairness_assumptions,
        fairness: fairness.clone(),
        fairness_certificate_trace: fairness_certificate_trace.clone(),
        epoch_trace: observation.graph_epoch_trace.clone(),
        rounds,
        final_state: final_state.clone(),
        theorem_pack: theorem_pack.clone(),
        route_bounds: SearchRouteBoundArtifact {
            discovery_class: SearchRouteDiscoveryBoundClass::NoCandidate,
            candidate_discovery_bound_steps: None,
            goal_service_bound_steps: fairness.certificate.service_bound_steps,
            goal_window_entry_bound_steps: None,
            discovery_certificate: None,
            recovery_bound_steps_after_latest_epoch: None,
            quality_class: SearchRouteQualityClass::NoCandidate,
            selected_route_cost: None,
            optimality_gap: None,
            approximation_ratio_milli: None,
            admissible_upper_bound: None,
            selected_route_summary: None,
            required_premises: fairness.certificate.required_fairness.clone(),
        },
        final_observation: observation.clone(),
    };
    let route_bounds = route_bound_artifact_for_replay(config.scheduler_profile, &replay);
    let replay = SearchReplayArtifact {
        route_bounds: route_bounds.clone(),
        ..replay
    };
    Ok((
        SearchExecutionReport {
            observation,
            scheduler,
            fairness,
            fairness_certificate_trace,
            final_state,
            theorem_pack,
            route_bounds,
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
