use std::{
    collections::{BTreeMap, BTreeSet},
    env,
};

use serde::{Deserialize, Serialize};

use crate::admission::{
    SearchDeterminismMode, SearchFairnessAssumption, SearchObservableClass, SearchSchedulerProfile,
};
use crate::cost::SearchCost;
use crate::domain::{
    SearchDomain, SearchQuery, SearchReseedingPolicy, SearchSelectedResultSemanticsClass,
};
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

/// How one run terminated under its declared effort profile.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum SearchRunTermination {
    /// The live frontier emptied and the run reached its natural barrier.
    Completed,
    /// The declared scheduler-step budget was exhausted before the frontier
    /// emptied.
    SchedulerStepBudgetExhausted,
}

/// Scheduler artifact for one run.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SchedulerArtifact {
    /// Declared execution policy. This is execution-side configuration only
    /// and does not define downstream search-problem semantics.
    pub execution_policy: SearchExecutionPolicy,
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

/// Public discovery-bound class for one selected result.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchResultDiscoveryBoundClass {
    /// The bound is an exact observed value derived from the committed replay
    /// rounds of this run.
    ObservedRunBound,
    /// No candidate route was published during the run.
    NoCandidate,
}

/// Historical route-discovery vocabulary retained for compatibility.
pub type SearchRouteDiscoveryBoundClass = SearchResultDiscoveryBoundClass;

/// Theorem-backed discovery certificate class for one selected result.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchResultDiscoveryCertificateClass {
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

/// Historical route-discovery-certificate vocabulary retained for
/// compatibility.
pub type SearchRouteDiscoveryCertificateClass = SearchResultDiscoveryCertificateClass;

/// Theorem-backed discovery certificate for one selected result.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchResultDiscoveryCertificate {
    /// Discovery theorem class.
    pub class: SearchResultDiscoveryCertificateClass,
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

/// Historical route discovery certificate vocabulary retained for
/// compatibility.
pub type SearchRouteDiscoveryCertificate = SearchResultDiscoveryCertificate;

/// Optional path-problem-specific discovery helper layered over generic
/// selected-result bounds.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchPathProblemDiscoveryArtifact {
    /// Theorem-backed bound, when available, once the path goal enters the
    /// certified legal service window for the current profile.
    pub goal_service_bound_steps: Option<u64>,
    /// Observed scheduler-step bound until the path goal first appears in the
    /// legal service window.
    pub goal_window_entry_bound_steps: Option<u64>,
    /// Structured theorem-backed discovery certificate for the path-goal
    /// specialization, when available.
    pub discovery_certificate: Option<SearchResultDiscoveryCertificate>,
}

/// Historical route-problem discovery helper vocabulary retained for
/// compatibility.
pub type SearchRouteProblemDiscoveryArtifact = SearchPathProblemDiscoveryArtifact;

/// Public quality class for one selected result.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchResultQualityClass {
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

/// Historical route-quality vocabulary retained for compatibility.
pub type SearchRouteQualityClass = SearchResultQualityClass;

/// Generic approximation/exactness contract for one run surface.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchApproximationContractClass {
    /// Exact end-to-end search contract.
    Exact,
    /// Exactness only once a certified service window premise is attached.
    CertifiedWindowExact,
    /// Budgeted anytime search contract.
    BudgetedAnytime,
    /// Envelope-bounded search contract.
    EnvelopeBounded,
    /// No selected result is available.
    NoResult,
}

/// Public selected-result discovery and quality artifact for one run.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchResultBoundArtifact<C> {
    /// Class of the candidate discovery bound.
    pub discovery_class: SearchResultDiscoveryBoundClass,
    /// Observed scheduler-step bound until the first route candidate is
    /// published.
    pub candidate_discovery_bound_steps: Option<u64>,
    /// Optional path-problem-specific discovery helper. Generic selected-result
    /// bounds do not rely on a distinguished goal anchor.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub path_problem: Option<SearchPathProblemDiscoveryArtifact>,
    /// Observed scheduler-step bound from the latest epoch transition to the
    /// first route candidate published in that epoch.
    pub recovery_bound_steps_after_latest_epoch: Option<u64>,
    /// Class of the selected route quality claim.
    pub quality_class: SearchResultQualityClass,
    /// Selected-result cost if a candidate exists.
    #[serde(alias = "selected_route_cost")]
    pub selected_result_cost: Option<C>,
    /// Optimality gap when the current claim surface can justify one.
    pub optimality_gap: Option<C>,
    /// Approximation ratio in milli units when the current claim surface can
    /// justify one.
    pub approximation_ratio_milli: Option<u64>,
    /// Admissible upper bound on the selected route cost.
    pub admissible_upper_bound: Option<C>,
    /// Compact selected-result summary for downstream reporting.
    #[serde(alias = "selected_route_summary")]
    pub selected_result_summary: Option<SearchResultSummary<C>>,
    /// Premises required by the selected route claim.
    pub required_premises: BTreeSet<SearchFairnessAssumption>,
}

/// Historical route-bound vocabulary retained for compatibility.
pub type SearchRouteBoundArtifact<C> = SearchResultBoundArtifact<C>;

/// Generic selected-result bound vocabulary retained alongside the
/// route-oriented helper during migration.
pub type SearchSelectedResultBoundArtifact<C> = SearchResultBoundArtifact<C>;

impl<C> SearchResultBoundArtifact<C> {
    /// Borrow the optional path-problem-specific discovery helper.
    #[must_use]
    pub fn path_problem(&self) -> Option<&SearchPathProblemDiscoveryArtifact> {
        self.path_problem.as_ref()
    }
}

/// Compact selected-result summary exported alongside result bounds.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(bound(deserialize = "C: Deserialize<'de>"))]
pub struct SearchResultSummary<C> {
    /// Selected route cost.
    pub cost: C,
    /// Length of the selected-result witness when one structured witness is
    /// exported by the domain.
    pub selected_result_witness_len: Option<u64>,
    /// Number of incumbent publications observed during the run.
    pub publication_count: u64,
    /// Number of canonical normalized commits observed during the run.
    pub normalized_commit_count: u64,
    /// Number of distinct epochs traversed by this run.
    pub traversed_epoch_count: u64,
    /// Optional path-search-specific summary helper.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub path_summary: Option<SearchPathResultSummary<C>>,
    /// Generic route metrics exported in stable canonical order for downstream
    /// reporting and comparison.
    pub metrics: Vec<SearchResultMetric>,
}

/// Optional path-search-specific summary helper.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(bound(deserialize = "C: Deserialize<'de>"))]
pub struct SearchPathResultSummary<C> {
    /// Selected path cost.
    pub cost: C,
    /// Number of nodes in the selected path witness.
    pub path_node_count: u64,
    /// Number of hops in the selected path witness.
    pub hop_count: u64,
}

/// Historical route-summary vocabulary retained for compatibility.
pub type SearchRouteSummary<C> = SearchPathResultSummary<C>;

/// Generic selected-result summary vocabulary retained alongside the
/// route-oriented helper during migration.
pub type SearchSelectedResultSummary<C> = SearchResultSummary<C>;

/// Stable metric name for generic selected-result summaries.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchResultMetricName {
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

/// Historical route-metric-name vocabulary retained for compatibility.
pub type SearchRouteMetricName = SearchResultMetricName;

/// One generic metric exported with the selected-result summary.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchResultMetric {
    /// Stable metric identity.
    pub name: SearchRouteMetricName,
    /// Metric value in canonical integer form.
    pub value: u128,
}

/// Historical route-metric vocabulary retained for compatibility.
pub type SearchRouteMetric = SearchResultMetric;

/// Generic selected-result metric vocabulary retained alongside the
/// route-oriented helper during migration.
pub type SearchSelectedResultMetric = SearchResultMetric;

/// Generic selected-result metric-name vocabulary retained alongside the
/// route-oriented helper during migration.
pub type SearchSelectedResultMetricName = SearchResultMetricName;

/// Generic approximation/exactness artifact vocabulary retained alongside the
/// route-oriented helper during migration.
pub type SearchApproximationArtifact<C> = SearchResultBoundArtifact<C>;

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

/// Support classification for one theorem in the search theorem pack.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchTheoremSupportClass {
    /// Direct theorem over executable reduced semantics.
    ExecutableSemantics,
    /// Corollary obtained by refinement from a stronger semantics theorem.
    RefinementCorollary,
    /// Theorem remains premise-scoped rather than unconditional.
    PremiseScoped,
}

/// Problem-class classification for one theorem in the search theorem pack.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum SearchTheoremProblemClass {
    /// Generic machine/refinement/fairness theorem.
    GenericMachine,
    /// Generic selected-result/result-bound theorem.
    GenericSelectedResult,
    /// Path-problem-specific discovery or completeness theorem.
    PathProblemSpecific,
}

/// One theorem-inventory support-class row.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchTheoremInventorySupportClassEntry {
    /// Stable theorem inventory key.
    pub name: String,
    /// Support classification for that theorem.
    pub support_class: SearchTheoremSupportClass,
}

/// One theorem-inventory problem-class row.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchTheoremInventoryProblemClassEntry {
    /// Stable theorem inventory key.
    pub name: String,
    /// Problem-class classification for that theorem.
    pub problem_class: SearchTheoremProblemClass,
}

/// Release-facing search theorem-pack artifact mirrored from the Lean theorem
/// pack and exposed through the Rust runtime surface.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchTheoremPackArtifact {
    /// Machine-readable theorem inventory.
    pub inventory: Vec<SearchTheoremInventoryEntry>,
    /// Support classification for each theorem inventory row.
    pub inventory_support_classes: Vec<SearchTheoremInventorySupportClassEntry>,
    /// Problem-class classification for each theorem inventory row.
    pub inventory_problem_classes: Vec<SearchTheoremInventoryProblemClassEntry>,
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
    /// Current selected-result cost.
    #[serde(alias = "incumbent_cost")]
    pub selected_result_cost: Option<C>,
    /// Current selected-result witness.
    #[serde(alias = "incumbent_path")]
    pub selected_result_witness: Option<Vec<N>>,
    /// Latest applied reseeding policy when this state follows an epoch
    /// transition.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub latest_reseed_policy: Option<SearchReseedingPolicy>,
    /// Frozen graph epoch.
    pub epoch: G,
    /// Current search phase.
    pub phase: u64,
}

/// Richer exported full-machine artifact used for the strengthened
/// refinement-facing search proof boundary.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchFullStateArtifact<N, G, S, C>
where
    N: Ord,
    G: Ord,
    S: Ord,
{
    /// Canonical open frontier nodes with their current `g` scores.
    pub open_nodes: Vec<(N, C)>,
    /// Canonical closed-set nodes.
    pub closed_nodes: Vec<N>,
    /// Canonical inconsistent-set nodes.
    pub incons_nodes: Vec<N>,
    /// Canonical `g` scores.
    pub g_scores: Vec<(N, C)>,
    /// Canonical parent identities.
    pub parent_map: Vec<(N, N)>,
    /// Current selected-result cost.
    #[serde(alias = "incumbent_cost")]
    pub selected_result_cost: Option<C>,
    /// Current selected-result witness.
    #[serde(alias = "incumbent_path")]
    pub selected_result_witness: Option<Vec<N>>,
    /// Current epsilon.
    pub epsilon_milli: u64,
    /// Current search phase.
    pub phase: u64,
    /// Frozen graph epoch.
    pub epoch: G,
    /// Frozen graph snapshot.
    pub snapshot_id: S,
    /// Last extracted batch nodes when available.
    pub last_batch_nodes: Option<Vec<N>>,
    /// Full normalized commit trace.
    pub normalized_commit_trace: Vec<NormalizedCommitRecord<N, C>>,
    /// Full selected-result publication trace.
    #[serde(alias = "incumbent_publication_trace")]
    pub selected_result_publication_trace: Vec<IncumbentPublicationRecord<N, C>>,
    /// Latest applied reseeding policy when this state follows an epoch
    /// transition.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub latest_reseed_policy: Option<SearchReseedingPolicy>,
}

/// Typed runtime configuration for one search run.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum SearchCachingProfile {
    /// Recompute all transient scheduling data from the authoritative machine
    /// state each step.
    EphemeralPerStep,
    #[doc(hidden)]
    /// Reuse cached scheduling state across steps. This remains unsupported by
    /// the current stable runtime surface and is rejected fail-closed.
    IncrementalReuse,
}

/// Typed effort/budget profile for one search run.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum SearchEffortProfile {
    /// Run the machine to completion.
    RunToCompletion,
    /// Stop after the given number of scheduler steps. One budget unit is one
    /// full canonical batch/service step, and runs stop only at batch
    /// barriers.
    SchedulerStepBudget(u64),
}

/// Typed execution policy for one search run.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchExecutionPolicy {
    /// Declared execution-side scheduler profile.
    pub scheduler_profile: SearchSchedulerProfile,
    /// Configured batch width.
    pub batch_width: u64,
    /// Selected caching profile.
    pub caching_profile: SearchCachingProfile,
    /// Selected effort profile.
    pub effort_profile: SearchEffortProfile,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum BatchWidthRequirement {
    ExactlyOne,
    GreaterThanOne,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct SearchExecutionPolicyCompatibility {
    required_executor: ProposalExecutorKind,
    batch_width: BatchWidthRequirement,
    required_fairness: &'static [SearchFairnessAssumption],
}

const SERIAL_EXACT_FAIRNESS: &[SearchFairnessAssumption] =
    &[SearchFairnessAssumption::DeterministicSchedulerConfluence];

const ENVELOPE_FAIRNESS: &[SearchFairnessAssumption] = &[
    SearchFairnessAssumption::EventualLiveBatchService,
    SearchFairnessAssumption::NoStarvationWithinLegalWindow,
];

const fn execution_policy_compatibility(
    scheduler_profile: SearchSchedulerProfile,
) -> SearchExecutionPolicyCompatibility {
    match scheduler_profile {
        SearchSchedulerProfile::CanonicalSerial => SearchExecutionPolicyCompatibility {
            required_executor: ProposalExecutorKind::Serial,
            batch_width: BatchWidthRequirement::ExactlyOne,
            required_fairness: SERIAL_EXACT_FAIRNESS,
        },
        SearchSchedulerProfile::ThreadedExactSingleLane => SearchExecutionPolicyCompatibility {
            required_executor: ProposalExecutorKind::NativeParallel,
            batch_width: BatchWidthRequirement::ExactlyOne,
            required_fairness: SERIAL_EXACT_FAIRNESS,
        },
        SearchSchedulerProfile::BatchedParallelExact => SearchExecutionPolicyCompatibility {
            required_executor: ProposalExecutorKind::NativeParallel,
            batch_width: BatchWidthRequirement::GreaterThanOne,
            required_fairness: SERIAL_EXACT_FAIRNESS,
        },
        SearchSchedulerProfile::BatchedParallelEnvelopeBounded => {
            SearchExecutionPolicyCompatibility {
                required_executor: ProposalExecutorKind::NativeParallel,
                batch_width: BatchWidthRequirement::GreaterThanOne,
                required_fairness: ENVELOPE_FAIRNESS,
            }
        }
    }
}

impl SearchExecutionPolicy {
    /// Construct one execution policy with the current default
    /// cache/effort settings.
    #[must_use]
    pub const fn new(scheduler_profile: SearchSchedulerProfile, batch_width: u64) -> Self {
        Self {
            scheduler_profile,
            batch_width,
            caching_profile: SearchCachingProfile::EphemeralPerStep,
            effort_profile: SearchEffortProfile::RunToCompletion,
        }
    }

    /// Return one copy with an explicit caching profile.
    #[must_use]
    pub const fn with_caching_profile(self, caching_profile: SearchCachingProfile) -> Self {
        Self {
            caching_profile,
            ..self
        }
    }

    /// Return one copy with an explicit effort profile.
    #[must_use]
    pub const fn with_effort_profile(self, effort_profile: SearchEffortProfile) -> Self {
        Self {
            effort_profile,
            ..self
        }
    }
}

/// Classify the generic approximation/exactness contract induced by one
/// execution policy.
#[must_use]
pub fn classify_approximation_contract(
    policy: SearchExecutionPolicy,
) -> SearchApproximationContractClass {
    match policy.effort_profile {
        SearchEffortProfile::SchedulerStepBudget(_) => {
            SearchApproximationContractClass::BudgetedAnytime
        }
        SearchEffortProfile::RunToCompletion => match policy.scheduler_profile {
            SearchSchedulerProfile::CanonicalSerial
            | SearchSchedulerProfile::ThreadedExactSingleLane => {
                SearchApproximationContractClass::Exact
            }
            SearchSchedulerProfile::BatchedParallelExact => {
                SearchApproximationContractClass::CertifiedWindowExact
            }
            SearchSchedulerProfile::BatchedParallelEnvelopeBounded => {
                SearchApproximationContractClass::EnvelopeBounded
            }
        },
    }
}

/// Typed runtime configuration for one search run.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SearchRunConfig {
    /// Declared execution policy. This is execution-side configuration only
    /// and does not define downstream search-problem semantics.
    pub execution_policy: SearchExecutionPolicy,
    /// Declared fairness assumptions.
    pub fairness_assumptions: BTreeSet<SearchFairnessAssumption>,
}

impl SearchRunConfig {
    /// Construct one runtime config from an execution policy and declared
    /// fairness assumptions.
    #[must_use]
    pub fn new(
        execution_policy: SearchExecutionPolicy,
        fairness_assumptions: BTreeSet<SearchFairnessAssumption>,
    ) -> Self {
        Self {
            execution_policy,
            fairness_assumptions,
        }
    }
}

/// Fail-closed runtime-config rejection.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum SearchRunConfigError {
    /// Batch width must be non-zero.
    ZeroBatchWidth,
    /// The selected caching profile is not yet supported by the current
    /// runtime.
    UnsupportedCachingProfile(SearchCachingProfile),
    /// The selected effort profile is not yet supported by the current
    /// runtime.
    UnsupportedEffortProfile(SearchEffortProfile),
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
    /// Selected-result discovery and quality artifact for the run.
    ///
    /// The field name retains the historical route-bound spelling for
    /// compatibility while the type itself is generic over selected results.
    pub route_bounds: SearchResultBoundArtifact<C>,
    /// How the run terminated under its declared effort profile.
    pub termination: SearchRunTermination,
    /// Progress summary.
    pub progress: ProgressSummary,
}

impl<N, G, C> SearchExecutionReport<N, G, C>
where
    N: Ord,
    G: Ord,
{
    /// Borrow the generic selected-result bound artifact for this run.
    #[must_use]
    pub fn selected_result_bounds(&self) -> &SearchResultBoundArtifact<C> {
        &self.route_bounds
    }
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

/// Optional path-problem-specific replay metadata.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct SearchPathProblemReplayArtifact<N> {
    /// Canonical path-goal anchor when the query is the built-in single-goal
    /// path adapter.
    pub goal_anchor: N,
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
    /// Generalized query for the run.
    pub query: SearchQuery<N>,
    /// Selected-result semantics class used by this run.
    pub selected_result_semantics_class: SearchSelectedResultSemanticsClass,
    /// Optional path-problem-specific replay metadata.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub path_problem: Option<SearchPathProblemReplayArtifact<N>>,
    /// Declared execution policy for the run.
    pub execution_policy: SearchExecutionPolicy,
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
    /// How the run terminated under its declared effort profile.
    pub termination: SearchRunTermination,
    /// Release-facing theorem-pack artifact for this run surface.
    pub theorem_pack: SearchTheoremPackArtifact,
    /// Selected-result discovery and quality artifact for the run.
    ///
    /// The field name retains the historical route-bound spelling for
    /// compatibility while the type itself is generic over selected results.
    pub route_bounds: SearchResultBoundArtifact<C>,
    /// Final observed artifact.
    pub final_observation: SearchObservationArtifact<N, G, C>,
}

impl<N, G, S, C> SearchReplayArtifact<N, G, S, C>
where
    N: Ord,
    G: Ord,
    S: Ord,
{
    /// Borrow the generic selected-result bound artifact for this replay.
    #[must_use]
    pub fn selected_result_bounds(&self) -> &SearchResultBoundArtifact<C> {
        &self.route_bounds
    }
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
    /// Reseeding policy used for the new epoch.
    pub reseeding_policy: SearchReseedingPolicy,
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
    /// The replay artifact requires domain-defined selected-result semantics
    /// that cannot be re-derived from the generic replay payload alone.
    UnsupportedSelectedResultSemantics,
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
            SearchObservableClass::SelectedResultCost,
            SearchObservableClass::CanonicalParentIdentity,
            SearchObservableClass::SelectedResultWitnessIdentity,
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
#[allow(clippy::too_many_lines)]
pub fn search_theorem_pack_artifact() -> SearchTheoremPackArtifact {
    SearchTheoremPackArtifact {
        inventory: [
            ("search_canonical_serial_exact_one_step_fairness", true),
            (
                "search_full_state_artifact_of_full_state_is_runtime_projection",
                true,
            ),
            (
                "search_reduced_state_of_full_state_preserves_machine_invariants",
                true,
            ),
            ("search_full_activate_batch_preserves_invariants", true),
            ("search_full_apply_proposal_preserves_invariants", true),
            ("search_full_commit_proposals_preserves_invariants", true),
            (
                "search_full_decrease_epsilon_and_rebuild_preserves_invariants",
                true,
            ),
            (
                "search_full_commit_epoch_reconfiguration_preserves_invariants",
                true,
            ),
            ("search_full_step_once_preserves_invariants", true),
            (
                "search_full_activate_batch_refines_reduced_service_window",
                true,
            ),
            (
                "search_full_step_once_refines_reduced_executable_step",
                true,
            ),
            (
                "search_canonical_serial_dynamic_liveness_under_stability",
                true,
            ),
            (
                "search_executable_canonical_step_preserves_invariants",
                true,
            ),
            (
                "search_executable_trace_refines_canonical_machine_trace",
                true,
            ),
            (
                "search_executable_step_artifact_refines_canonical_step_artifact",
                true,
            ),
            ("search_canonical_machine_step_preserves_invariants", true),
            (
                "search_canonical_machine_trace_currently_min_priority_eventually_serviced",
                true,
            ),
            (
                "search_canonical_machine_step_artifact_refines_runtime_boundary",
                true,
            ),
            (
                "search_canonical_machine_state_artifact_is_runtime_projection",
                true,
            ),
            (
                "search_fixed_phase_canonical_serial_terminates_under_finite_reachable_bound",
                true,
            ),
            (
                "search_rebuild_aware_canonical_serial_terminates_under_phase_work_measure",
                true,
            ),
            (
                "search_bounded_strict_preemption_eventually_becomes_min",
                true,
            ),
            (
                "search_canonical_serial_nonmin_entry_eventually_serviced_under_bounded_strict_preemption",
                true,
            ),
            (
                "search_finite_better_entry_exhaustion_eventually_becomes_min",
                true,
            ),
            (
                "search_canonical_serial_nonmin_entry_eventually_serviced_under_finite_better_entry_exhaustion",
                true,
            ),
            (
                "search_canonical_serial_nonmin_entry_eventually_serviced_under_scheduler_fairness",
                true,
            ),
            (
                "search_canonical_serial_goal_reached_from_ready_witness_path",
                true,
            ),
            (
                "search_canonical_machine_goal_reached_from_ready_witness_path",
                true,
            ),
            (
                "search_canonical_machine_goal_reached_from_graph_reachability",
                true,
            ),
            (
                "search_canonical_machine_goal_reached_from_raw_successor_semantics",
                true,
            ),
            (
                "search_goal_reachability_connects_to_incumbent_publication",
                true,
            ),
            (
                "search_eventual_optimal_goal_publication_under_admissible_consistent_heuristic",
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
                "search_batched_parallel_envelope_claim_is_certified_window_bounded",
                true,
            ),
            (
                "search_batched_parallel_envelope_certified_window_fairness",
                true,
            ),
            (
                "search_batched_parallel_envelope_certified_window_trace_valid",
                true,
            ),
            (
                "search_canonical_serial_goal_window_service_has_exact_suffix_bound",
                true,
            ),
            (
                "search_threaded_exact_single_lane_goal_window_service_has_exact_suffix_bound",
                true,
            ),
            ("search_canonical_serial_has_exact_result_contract", true),
            (
                "search_threaded_exact_single_lane_has_exact_result_contract",
                true,
            ),
            (
                "search_batched_parallel_exact_has_certified_window_exact_contract",
                true,
            ),
            (
                "search_batched_parallel_envelope_has_envelope_bounded_contract",
                true,
            ),
            (
                "search_scheduler_step_budget_yields_budgeted_anytime_contract",
                true,
            ),
            (
                "search_selected_result_observation_slice_refines_legacy_fields",
                true,
            ),
        ]
        .into_iter()
        .map(|(name, present)| SearchTheoremInventoryEntry {
            name: name.to_string(),
            present,
        })
        .collect(),
        inventory_support_classes: [
            (
                "search_canonical_serial_exact_one_step_fairness",
                SearchTheoremSupportClass::ExecutableSemantics,
            ),
            (
                "search_full_state_artifact_of_full_state_is_runtime_projection",
                SearchTheoremSupportClass::ExecutableSemantics,
            ),
            (
                "search_reduced_state_of_full_state_preserves_machine_invariants",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
            (
                "search_full_activate_batch_preserves_invariants",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_full_apply_proposal_preserves_invariants",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_full_commit_proposals_preserves_invariants",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_full_decrease_epsilon_and_rebuild_preserves_invariants",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_full_commit_epoch_reconfiguration_preserves_invariants",
                SearchTheoremSupportClass::ExecutableSemantics,
            ),
            (
                "search_full_step_once_preserves_invariants",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_full_activate_batch_refines_reduced_service_window",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_full_step_once_refines_reduced_executable_step",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_canonical_serial_dynamic_liveness_under_stability",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_executable_canonical_step_preserves_invariants",
                SearchTheoremSupportClass::ExecutableSemantics,
            ),
            (
                "search_executable_trace_refines_canonical_machine_trace",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
            (
                "search_executable_step_artifact_refines_canonical_step_artifact",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
            (
                "search_canonical_machine_step_preserves_invariants",
                SearchTheoremSupportClass::ExecutableSemantics,
            ),
            (
                "search_canonical_machine_trace_currently_min_priority_eventually_serviced",
                SearchTheoremSupportClass::ExecutableSemantics,
            ),
            (
                "search_canonical_machine_step_artifact_refines_runtime_boundary",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
            (
                "search_canonical_machine_state_artifact_is_runtime_projection",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
            (
                "search_fixed_phase_canonical_serial_terminates_under_finite_reachable_bound",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_rebuild_aware_canonical_serial_terminates_under_phase_work_measure",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_bounded_strict_preemption_eventually_becomes_min",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_canonical_serial_nonmin_entry_eventually_serviced_under_bounded_strict_preemption",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_finite_better_entry_exhaustion_eventually_becomes_min",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_canonical_serial_nonmin_entry_eventually_serviced_under_finite_better_entry_exhaustion",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_canonical_serial_nonmin_entry_eventually_serviced_under_scheduler_fairness",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_canonical_serial_goal_reached_from_ready_witness_path",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_canonical_machine_goal_reached_from_ready_witness_path",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_canonical_machine_goal_reached_from_graph_reachability",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_canonical_machine_goal_reached_from_raw_successor_semantics",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_goal_reachability_connects_to_incumbent_publication",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_eventual_optimal_goal_publication_under_admissible_consistent_heuristic",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_threaded_exact_single_lane_refines_canonical_one_step",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
            (
                "search_threaded_exact_single_lane_commit_trace_refines_canonical",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
            (
                "search_threaded_exact_single_lane_state_slice_refines_canonical",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
            (
                "search_threaded_exact_single_lane_observation_slice_refines_canonical",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
            (
                "search_threaded_exact_single_lane_observation_equivalent_to_canonical",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
            (
                "search_threaded_exact_single_lane_multi_step_state_trace_refines_canonical",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
            (
                "search_threaded_exact_single_lane_multi_step_observation_trace_refines_canonical",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
            (
                "search_threaded_exact_single_lane_state_artifact_refines_canonical",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
            (
                "search_threaded_exact_single_lane_multi_step_state_artifact_trace_refines_canonical",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
            (
                "search_threaded_exact_single_lane_exact_one_step_fairness",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
            (
                "search_canonical_serial_goal_window_service_has_exact_suffix_bound",
                SearchTheoremSupportClass::ExecutableSemantics,
            ),
            (
                "search_threaded_exact_single_lane_goal_window_service_has_exact_suffix_bound",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
            (
                "search_batched_parallel_exact_certified_window_fairness",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_batched_parallel_exact_bounded_dynamic_starvation_freedom",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_batched_parallel_exact_certified_window_trace_valid",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_batched_parallel_envelope_claim_is_certified_window_bounded",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_batched_parallel_envelope_certified_window_fairness",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_batched_parallel_envelope_certified_window_trace_valid",
                SearchTheoremSupportClass::PremiseScoped,
            ),
            (
                "search_canonical_serial_has_exact_result_contract",
                SearchTheoremSupportClass::ExecutableSemantics,
            ),
            (
                "search_threaded_exact_single_lane_has_exact_result_contract",
                SearchTheoremSupportClass::ExecutableSemantics,
            ),
            (
                "search_batched_parallel_exact_has_certified_window_exact_contract",
                SearchTheoremSupportClass::ExecutableSemantics,
            ),
            (
                "search_batched_parallel_envelope_has_envelope_bounded_contract",
                SearchTheoremSupportClass::ExecutableSemantics,
            ),
            (
                "search_scheduler_step_budget_yields_budgeted_anytime_contract",
                SearchTheoremSupportClass::ExecutableSemantics,
            ),
            (
                "search_selected_result_observation_slice_refines_legacy_fields",
                SearchTheoremSupportClass::RefinementCorollary,
            ),
        ]
        .into_iter()
        .map(|(name, support_class)| SearchTheoremInventorySupportClassEntry {
            name: name.to_string(),
            support_class,
        })
        .collect(),
        inventory_problem_classes: theorem_inventory_problem_classes(),
        canonical_service_bound_steps: 1,
        canonical_goal_window_discovery_suffix_bound_steps: 1,
        gate: "just check-search-fairness".to_string(),
    }
}

/// Classify one theorem row as generic-machine or problem-specific.
#[must_use]
pub fn classify_theorem_problem_class(name: &str) -> SearchTheoremProblemClass {
    match name {
        "search_canonical_serial_has_exact_result_contract"
        | "search_threaded_exact_single_lane_has_exact_result_contract"
        | "search_batched_parallel_exact_has_certified_window_exact_contract"
        | "search_batched_parallel_envelope_has_envelope_bounded_contract"
        | "search_scheduler_step_budget_yields_budgeted_anytime_contract"
        | "search_selected_result_observation_slice_refines_legacy_fields" => {
            SearchTheoremProblemClass::GenericSelectedResult
        }
        "search_canonical_serial_goal_reached_from_ready_witness_path"
        | "search_canonical_machine_goal_reached_from_ready_witness_path"
        | "search_canonical_machine_goal_reached_from_graph_reachability"
        | "search_canonical_machine_goal_reached_from_raw_successor_semantics"
        | "search_goal_reachability_connects_to_incumbent_publication"
        | "search_eventual_optimal_goal_publication_under_admissible_consistent_heuristic"
        | "search_canonical_serial_goal_window_service_has_exact_suffix_bound"
        | "search_threaded_exact_single_lane_goal_window_service_has_exact_suffix_bound" => {
            SearchTheoremProblemClass::PathProblemSpecific
        }
        _ => SearchTheoremProblemClass::GenericMachine,
    }
}

/// Derived problem-class inventory for the current theorem-pack surface.
#[must_use]
pub fn theorem_inventory_problem_classes() -> Vec<SearchTheoremInventoryProblemClassEntry> {
    [
        "search_canonical_serial_exact_one_step_fairness",
        "search_full_state_artifact_of_full_state_is_runtime_projection",
        "search_reduced_state_of_full_state_preserves_machine_invariants",
        "search_full_activate_batch_preserves_invariants",
        "search_full_apply_proposal_preserves_invariants",
        "search_full_commit_proposals_preserves_invariants",
        "search_full_decrease_epsilon_and_rebuild_preserves_invariants",
        "search_full_commit_epoch_reconfiguration_preserves_invariants",
        "search_full_step_once_preserves_invariants",
        "search_full_activate_batch_refines_reduced_service_window",
        "search_full_step_once_refines_reduced_executable_step",
        "search_canonical_serial_dynamic_liveness_under_stability",
        "search_executable_canonical_step_preserves_invariants",
        "search_executable_trace_refines_canonical_machine_trace",
        "search_executable_step_artifact_refines_canonical_step_artifact",
        "search_canonical_machine_step_preserves_invariants",
        "search_canonical_machine_trace_currently_min_priority_eventually_serviced",
        "search_canonical_machine_step_artifact_refines_runtime_boundary",
        "search_canonical_machine_state_artifact_is_runtime_projection",
        "search_fixed_phase_canonical_serial_terminates_under_finite_reachable_bound",
        "search_rebuild_aware_canonical_serial_terminates_under_phase_work_measure",
        "search_bounded_strict_preemption_eventually_becomes_min",
        "search_canonical_serial_nonmin_entry_eventually_serviced_under_bounded_strict_preemption",
        "search_finite_better_entry_exhaustion_eventually_becomes_min",
        "search_canonical_serial_nonmin_entry_eventually_serviced_under_finite_better_entry_exhaustion",
        "search_canonical_serial_nonmin_entry_eventually_serviced_under_scheduler_fairness",
        "search_canonical_serial_goal_reached_from_ready_witness_path",
        "search_canonical_machine_goal_reached_from_ready_witness_path",
        "search_canonical_machine_goal_reached_from_graph_reachability",
        "search_canonical_machine_goal_reached_from_raw_successor_semantics",
        "search_goal_reachability_connects_to_incumbent_publication",
        "search_eventual_optimal_goal_publication_under_admissible_consistent_heuristic",
        "search_threaded_exact_single_lane_refines_canonical_one_step",
        "search_threaded_exact_single_lane_commit_trace_refines_canonical",
        "search_threaded_exact_single_lane_state_slice_refines_canonical",
        "search_threaded_exact_single_lane_observation_slice_refines_canonical",
        "search_threaded_exact_single_lane_observation_equivalent_to_canonical",
        "search_threaded_exact_single_lane_multi_step_state_trace_refines_canonical",
        "search_threaded_exact_single_lane_multi_step_observation_trace_refines_canonical",
        "search_threaded_exact_single_lane_state_artifact_refines_canonical",
        "search_threaded_exact_single_lane_multi_step_state_artifact_trace_refines_canonical",
        "search_threaded_exact_single_lane_exact_one_step_fairness",
        "search_canonical_serial_goal_window_service_has_exact_suffix_bound",
        "search_threaded_exact_single_lane_goal_window_service_has_exact_suffix_bound",
        "search_batched_parallel_exact_certified_window_fairness",
        "search_batched_parallel_exact_bounded_dynamic_starvation_freedom",
        "search_batched_parallel_exact_certified_window_trace_valid",
        "search_batched_parallel_envelope_claim_is_certified_window_bounded",
        "search_batched_parallel_envelope_certified_window_fairness",
        "search_batched_parallel_envelope_certified_window_trace_valid",
        "search_canonical_serial_has_exact_result_contract",
        "search_threaded_exact_single_lane_has_exact_result_contract",
        "search_batched_parallel_exact_has_certified_window_exact_contract",
        "search_batched_parallel_envelope_has_envelope_bounded_contract",
        "search_scheduler_step_budget_yields_budgeted_anytime_contract",
        "search_selected_result_observation_slice_refines_legacy_fields",
    ]
    .into_iter()
    .map(|name| SearchTheoremInventoryEntry {
        name: name.to_string(),
        present: true,
    })
    .map(|entry| SearchTheoremInventoryProblemClassEntry {
        problem_class: classify_theorem_problem_class(&entry.name),
        name: entry.name,
    })
    .collect()
}

impl<C> SearchResultBoundArtifact<C>
where
    C: SearchCost,
{
    /// Borrow the selected-result cost in generic terminology.
    #[must_use]
    pub fn selected_result_cost(&self) -> Option<&C> {
        self.selected_result_cost.as_ref()
    }

    /// Borrow the selected-result summary in generic terminology.
    #[must_use]
    pub fn selected_result_summary(&self) -> Option<&SearchResultSummary<C>> {
        self.selected_result_summary.as_ref()
    }

    /// Borrow the optional path-search-specific summary helper.
    #[must_use]
    pub fn selected_path_summary(&self) -> Option<&SearchPathResultSummary<C>> {
        self.selected_result_summary
            .as_ref()
            .and_then(|summary| summary.path_summary.as_ref())
    }

    /// Classify the generic approximation/exactness contract for this result
    /// under one execution policy.
    #[must_use]
    pub fn approximation_contract_class(
        &self,
        policy: SearchExecutionPolicy,
    ) -> SearchApproximationContractClass {
        if self.selected_result_cost.is_none() {
            SearchApproximationContractClass::NoResult
        } else {
            classify_approximation_contract(policy)
        }
    }
}

fn replay_path_problem_artifact<N>(
    goal_anchor: Option<N>,
    goal_service_bound_steps: Option<u64>,
) -> Option<SearchPathProblemDiscoveryArtifact> {
    goal_anchor.map(|_| SearchPathProblemDiscoveryArtifact {
        goal_service_bound_steps,
        goal_window_entry_bound_steps: None,
        discovery_certificate: None,
    })
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
        selected_result_cost: machine
            .state()
            .incumbent
            .as_ref()
            .map(|incumbent| incumbent.cost),
        selected_result_witness: machine.selected_result_witness_for_export(),
        latest_reseed_policy: machine.observation().reseed_policy_trace.last().copied(),
        epoch: machine.state().graph_epoch.clone(),
        phase: machine.state().phase,
    }
}

fn report_only_state_artifact_for_machine<D>(
    machine: &SearchMachine<D>,
) -> SearchStateArtifact<D::Node, D::GraphEpoch, D::Cost>
where
    D: SearchDomain,
{
    SearchStateArtifact {
        open_nodes: Vec::new(),
        closed_nodes: Vec::new(),
        g_scores: Vec::new(),
        parent_map: Vec::new(),
        selected_result_cost: machine
            .state()
            .incumbent
            .as_ref()
            .map(|incumbent| incumbent.cost),
        selected_result_witness: machine.selected_result_witness_for_export(),
        latest_reseed_policy: machine.observation().reseed_policy_trace.last().copied(),
        epoch: machine.state().graph_epoch.clone(),
        phase: machine.state().phase,
    }
}

/// Export the richer full-machine artifact boundary for one live Rust search
/// machine state.
#[must_use]
pub fn full_state_artifact_for_machine<D>(
    machine: &SearchMachine<D>,
) -> SearchFullStateArtifact<D::Node, D::GraphEpoch, D::SnapshotId, D::Cost>
where
    D: SearchDomain,
{
    SearchFullStateArtifact {
        open_nodes: machine
            .state()
            .open
            .iter()
            .map(|(node, entry)| (node.clone(), entry.g_score))
            .collect(),
        closed_nodes: machine.state().closed.iter().cloned().collect(),
        incons_nodes: machine.state().incons.iter().cloned().collect(),
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
        selected_result_cost: machine
            .state()
            .incumbent
            .as_ref()
            .map(|incumbent| incumbent.cost),
        selected_result_witness: machine.selected_result_witness_for_export(),
        epsilon_milli: u64::from(machine.state().epsilon.0),
        phase: machine.state().phase,
        epoch: machine.state().graph_epoch.clone(),
        snapshot_id: machine.state().graph_snapshot_id.clone(),
        last_batch_nodes: machine.last_batch.as_ref().map(|batch| {
            batch
                .entries
                .iter()
                .map(|entry| entry.node.clone())
                .collect()
        }),
        normalized_commit_trace: machine.observation.normalized_commit_trace.clone(),
        selected_result_publication_trace: machine
            .observation
            .selected_result_publication_trace
            .clone(),
        latest_reseed_policy: machine.observation().reseed_policy_trace.last().copied(),
    }
}

#[allow(clippy::too_many_lines)]
fn route_bound_artifact_for_replay<N, G, S, C>(
    policy: SearchExecutionPolicy,
    termination: SearchRunTermination,
    replay: &SearchReplayArtifact<N, G, S, C>,
) -> SearchResultBoundArtifact<C>
where
    C: SearchCost,
    N: Ord,
    G: Clone + Ord,
    S: Ord,
{
    let selected_result_cost = replay.final_observation.selected_result_cost;
    let publication_count = u64::try_from(
        replay
            .final_observation
            .selected_result_publication_trace
            .len(),
    )
    .expect("publication count fits in u64");
    let normalized_commit_count =
        u64::try_from(replay.final_observation.normalized_commit_trace.len())
            .expect("normalized commit count fits in u64");
    let traversed_epoch_count =
        u64::try_from(replay.epoch_trace.len()).expect("epoch trace length fits in u64");
    let selected_result_summary = replay
        .final_observation
        .selected_result_witness
        .as_ref()
        .zip(selected_result_cost)
        .map(|(path, cost)| {
            let path_node_count = u64::try_from(path.len()).expect("path node count fits in u64");
            let hop_count =
                u64::try_from(path.len().saturating_sub(1)).expect("hop count fits in u64");
            SearchResultSummary {
                cost,
                selected_result_witness_len: Some(path_node_count),
                publication_count,
                normalized_commit_count,
                traversed_epoch_count,
                path_summary: Some(SearchPathResultSummary {
                    cost,
                    path_node_count,
                    hop_count,
                }),
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
        .position(|round| round.state_after_round.selected_result_cost.is_some())
        .map(|index| u64::try_from(index + 1).expect("round index fits in u64"));
    let latest_epoch = replay.epoch_trace.last().cloned();
    let recovery_bound_steps_after_latest_epoch = latest_epoch.and_then(|latest_epoch| {
        replay
            .rounds
            .iter()
            .filter(|round| round.epoch == latest_epoch)
            .position(|round| round.state_after_round.selected_result_cost.is_some())
            .map(|index| u64::try_from(index + 1).expect("round index fits in u64"))
    });
    let required_premises = replay.fairness.certificate.required_fairness.clone();
    let path_problem = replay.path_problem.as_ref().map(|path_problem| {
        let goal_window_entry_bound_steps = replay
            .rounds
            .iter()
            .position(|round| round.batch_nodes.contains(&path_problem.goal_anchor))
            .map(|index| u64::try_from(index + 1).expect("round index fits in u64"));
        let goal_service_bound_steps = replay.fairness.certificate.service_bound_steps;
        let discovery_certificate = goal_window_entry_bound_steps
            .zip(goal_service_bound_steps)
            .map(|(observed_goal_window_step, service_bound_steps)| {
                let class = match policy.scheduler_profile {
                    SearchSchedulerProfile::CanonicalSerial => {
                        SearchRouteDiscoveryCertificateClass::GoalWindowOneStepExact
                    }
                    SearchSchedulerProfile::ThreadedExactSingleLane => {
                        SearchRouteDiscoveryCertificateClass::GoalWindowOneStepViaThreadedRefinement
                    }
                    SearchSchedulerProfile::BatchedParallelExact
                    | SearchSchedulerProfile::BatchedParallelEnvelopeBounded => {
                        SearchRouteDiscoveryCertificateClass::CertifiedGoalWindowService
                    }
                };
                SearchRouteDiscoveryCertificate {
                    class,
                    service_bound_steps,
                    observed_goal_window_step,
                    required_premises: replay.fairness.certificate.required_fairness.clone(),
                    certified_observables: replay
                        .fairness
                        .certificate
                        .certified_observables
                        .clone(),
                }
            });
        SearchPathProblemDiscoveryArtifact {
            goal_service_bound_steps,
            goal_window_entry_bound_steps,
            discovery_certificate,
        }
    });

    let budget_exhausted = matches!(
        (policy.effort_profile, termination),
        (
            SearchEffortProfile::SchedulerStepBudget(_),
            SearchRunTermination::SchedulerStepBudgetExhausted
        )
    );

    match (selected_result_cost, policy.scheduler_profile) {
        (None, _) => SearchResultBoundArtifact {
            discovery_class: SearchRouteDiscoveryBoundClass::NoCandidate,
            candidate_discovery_bound_steps: None,
            path_problem: path_problem.clone(),
            recovery_bound_steps_after_latest_epoch: None,
            quality_class: SearchRouteQualityClass::NoCandidate,
            selected_result_cost: None,
            optimality_gap: None,
            approximation_ratio_milli: None,
            admissible_upper_bound: None,
            selected_result_summary: None,
            required_premises,
        },
        (Some(cost), SearchSchedulerProfile::CanonicalSerial)
        | (Some(cost), SearchSchedulerProfile::ThreadedExactSingleLane) => {
            SearchResultBoundArtifact {
                discovery_class: SearchRouteDiscoveryBoundClass::ObservedRunBound,
                candidate_discovery_bound_steps,
                path_problem: path_problem.clone(),
                recovery_bound_steps_after_latest_epoch,
                quality_class: if budget_exhausted {
                    SearchRouteQualityClass::PremiseOnly
                } else {
                    SearchRouteQualityClass::ExactOptimal
                },
                selected_result_cost: Some(cost),
                optimality_gap: if budget_exhausted {
                    None
                } else {
                    Some(C::zero())
                },
                approximation_ratio_milli: if budget_exhausted { None } else { Some(1_000) },
                admissible_upper_bound: Some(cost),
                selected_result_summary,
                required_premises,
            }
        }
        (Some(cost), SearchSchedulerProfile::BatchedParallelExact) => SearchResultBoundArtifact {
            discovery_class: SearchRouteDiscoveryBoundClass::ObservedRunBound,
            candidate_discovery_bound_steps,
            path_problem: path_problem.clone(),
            recovery_bound_steps_after_latest_epoch,
            quality_class: if budget_exhausted {
                SearchRouteQualityClass::PremiseOnly
            } else {
                SearchRouteQualityClass::PremisedWindowBounded
            },
            selected_result_cost: Some(cost),
            optimality_gap: None,
            approximation_ratio_milli: None,
            admissible_upper_bound: Some(cost),
            selected_result_summary,
            required_premises,
        },
        (Some(cost), SearchSchedulerProfile::BatchedParallelEnvelopeBounded) => {
            SearchResultBoundArtifact {
                discovery_class: SearchRouteDiscoveryBoundClass::ObservedRunBound,
                candidate_discovery_bound_steps,
                path_problem,
                recovery_bound_steps_after_latest_epoch,
                quality_class: SearchRouteQualityClass::PremisedWindowBounded,
                selected_result_cost: Some(cost),
                optimality_gap: None,
                approximation_ratio_milli: None,
                admissible_upper_bound: Some(cost),
                selected_result_summary,
                required_premises,
            }
        }
    }
}

#[allow(clippy::too_many_lines)]
fn route_bound_artifact_for_report_only<N, G, C>(
    policy: SearchExecutionPolicy,
    termination: SearchRunTermination,
    observation: &SearchObservationArtifact<N, G, C>,
    path_goal_anchor: Option<N>,
    fairness: &SearchFairnessArtifact<N, G, C>,
) -> SearchResultBoundArtifact<C>
where
    C: SearchCost,
    N: Clone + Ord,
    G: Ord,
{
    let selected_result_cost = observation.selected_result_cost;
    let publication_count = u64::try_from(observation.selected_result_publication_trace.len())
        .expect("publication count fits in u64");
    let normalized_commit_count = u64::try_from(observation.normalized_commit_trace.len())
        .expect("normalized commit count fits in u64");
    let traversed_epoch_count =
        u64::try_from(observation.graph_epoch_trace.len()).expect("epoch trace length fits in u64");
    let selected_result_summary = observation
        .selected_result_witness
        .as_ref()
        .zip(selected_result_cost)
        .map(|(path, cost)| {
            let path_node_count = u64::try_from(path.len()).expect("path node count fits in u64");
            let hop_count =
                u64::try_from(path.len().saturating_sub(1)).expect("hop count fits in u64");
            SearchResultSummary {
                cost,
                selected_result_witness_len: Some(path_node_count),
                publication_count,
                normalized_commit_count,
                traversed_epoch_count,
                path_summary: Some(SearchPathResultSummary {
                    cost,
                    path_node_count,
                    hop_count,
                }),
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
    let required_premises = fairness.certificate.required_fairness.clone();
    let path_problem = path_goal_anchor.map(|_| SearchPathProblemDiscoveryArtifact {
        goal_service_bound_steps: fairness.certificate.service_bound_steps,
        goal_window_entry_bound_steps: None,
        discovery_certificate: None,
    });
    let budget_exhausted = matches!(
        (policy.effort_profile, termination),
        (
            SearchEffortProfile::SchedulerStepBudget(_),
            SearchRunTermination::SchedulerStepBudgetExhausted
        )
    );

    match (selected_result_cost, policy.scheduler_profile) {
        (None, _) => SearchResultBoundArtifact {
            discovery_class: SearchRouteDiscoveryBoundClass::NoCandidate,
            candidate_discovery_bound_steps: None,
            path_problem,
            recovery_bound_steps_after_latest_epoch: None,
            quality_class: SearchRouteQualityClass::NoCandidate,
            selected_result_cost: None,
            optimality_gap: None,
            approximation_ratio_milli: None,
            admissible_upper_bound: None,
            selected_result_summary: None,
            required_premises,
        },
        (Some(cost), SearchSchedulerProfile::CanonicalSerial)
        | (Some(cost), SearchSchedulerProfile::ThreadedExactSingleLane) => {
            SearchResultBoundArtifact {
                discovery_class: SearchRouteDiscoveryBoundClass::ObservedRunBound,
                candidate_discovery_bound_steps: None,
                path_problem,
                recovery_bound_steps_after_latest_epoch: None,
                quality_class: if budget_exhausted {
                    SearchRouteQualityClass::PremiseOnly
                } else {
                    SearchRouteQualityClass::ExactOptimal
                },
                selected_result_cost: Some(cost),
                optimality_gap: if budget_exhausted {
                    None
                } else {
                    Some(C::zero())
                },
                approximation_ratio_milli: if budget_exhausted { None } else { Some(1_000) },
                admissible_upper_bound: Some(cost),
                selected_result_summary,
                required_premises,
            }
        }
        (Some(cost), SearchSchedulerProfile::BatchedParallelExact) => SearchResultBoundArtifact {
            discovery_class: SearchRouteDiscoveryBoundClass::ObservedRunBound,
            candidate_discovery_bound_steps: None,
            path_problem,
            recovery_bound_steps_after_latest_epoch: None,
            quality_class: if budget_exhausted {
                SearchRouteQualityClass::PremiseOnly
            } else {
                SearchRouteQualityClass::PremisedWindowBounded
            },
            selected_result_cost: Some(cost),
            optimality_gap: None,
            approximation_ratio_milli: None,
            admissible_upper_bound: Some(cost),
            selected_result_summary,
            required_premises,
        },
        (Some(cost), SearchSchedulerProfile::BatchedParallelEnvelopeBounded) => {
            SearchResultBoundArtifact {
                discovery_class: SearchRouteDiscoveryBoundClass::ObservedRunBound,
                candidate_discovery_bound_steps: None,
                path_problem,
                recovery_bound_steps_after_latest_epoch: None,
                quality_class: SearchRouteQualityClass::PremisedWindowBounded,
                selected_result_cost: Some(cost),
                optimality_gap: None,
                approximation_ratio_milli: None,
                admissible_upper_bound: Some(cost),
                selected_result_summary,
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
///
/// # Errors
///
/// Returns `SearchFairnessTraceValidationError` if the certificate trace length
/// does not match the replay round count.
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
///
/// # Errors
///
/// Returns `SearchRunConfigError` if the configuration is inconsistent with the
/// executor kind, execution policy, fairness assumptions, or batch width.
pub fn validate_run_config<D, X>(
    executor: &X,
    config: &SearchRunConfig,
) -> Result<(), SearchRunConfigError>
where
    D: SearchDomain + super::authority::SearchAuthorityPolicy,
    X: ProposalExecutor<D>,
{
    let policy = config.execution_policy;
    let compatibility = execution_policy_compatibility(policy.scheduler_profile);

    if policy.batch_width == 0 {
        return Err(SearchRunConfigError::ZeroBatchWidth);
    }

    if policy.caching_profile != SearchCachingProfile::EphemeralPerStep {
        return Err(SearchRunConfigError::UnsupportedCachingProfile(
            policy.caching_profile,
        ));
    }

    if let SearchEffortProfile::SchedulerStepBudget(0) = policy.effort_profile {
        // Zero-budget runs are valid and simply emit the initial artifact state
        // without servicing any batch.
    }

    match compatibility.required_executor {
        ProposalExecutorKind::Serial if executor.kind() != ProposalExecutorKind::Serial => {
            return Err(SearchRunConfigError::RequiresSerialExecutor(
                policy.scheduler_profile,
            ));
        }
        ProposalExecutorKind::NativeParallel
            if executor.kind() != ProposalExecutorKind::NativeParallel =>
        {
            return Err(SearchRunConfigError::RequiresNativeParallelExecutor(
                policy.scheduler_profile,
            ));
        }
        _ => {}
    }

    match compatibility.batch_width {
        BatchWidthRequirement::ExactlyOne if policy.batch_width != 1 => {
            return Err(SearchRunConfigError::RequiresBatchWidthOne(
                policy.scheduler_profile,
            ));
        }
        BatchWidthRequirement::GreaterThanOne if policy.batch_width <= 1 => {
            return Err(SearchRunConfigError::RequiresBatchWidthGreaterThanOne(
                policy.scheduler_profile,
            ));
        }
        _ => {}
    }

    for assumption in compatibility.required_fairness {
        require_fairness(config, policy.scheduler_profile, *assumption)?;
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
#[allow(clippy::too_many_lines)]
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
    let policy = config.execution_policy;
    let step_budget = match policy.effort_profile {
        SearchEffortProfile::RunToCompletion => None,
        SearchEffortProfile::SchedulerStepBudget(budget) => Some(budget),
    };
    let mut rounds = Vec::new();
    let mut fairness_certificate_trace = Vec::new();
    while let Some(batch) = machine.next_batch() {
        if step_budget
            .is_some_and(|budget| machine.state().trace_state.total_scheduler_steps >= budget)
        {
            break;
        }
        let mut proposals = executor
            .generate(machine.domain(), &batch, machine.query())
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
            policy.scheduler_profile,
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

    let termination = match step_budget {
        Some(budget)
            if machine.next_batch().is_some()
                && machine.state().trace_state.total_scheduler_steps >= budget =>
        {
            SearchRunTermination::SchedulerStepBudgetExhausted
        }
        _ => SearchRunTermination::Completed,
    };

    let observation = machine.observation_artifact(
        policy.scheduler_profile,
        config.fairness_assumptions.clone(),
    );
    let total_step_mode = match policy.scheduler_profile {
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
        execution_policy: policy,
        scheduler_profile: policy.scheduler_profile,
        authority_class: classify_scheduler_artifact(policy.scheduler_profile),
        batch_width: policy.batch_width,
        fairness_assumptions: config.fairness_assumptions.clone(),
    };
    let final_state = report_only_state_artifact_for_machine(machine);
    let theorem_pack = search_theorem_pack_artifact();
    let representative_window = rounds
        .first()
        .map(|round| (round.batch_nodes.clone(), round.commits.clone()))
        .unwrap_or_else(|| (Vec::new(), Vec::new()));
    let fairness = fairness_artifact_for_window(
        policy.scheduler_profile,
        rounds.first().map(|round| round.epoch.clone()),
        rounds.first().map(|round| round.phase),
        representative_window.0,
        representative_window.1,
    );
    let replay = SearchReplayArtifact {
        start: machine.start.clone(),
        query: machine.query().clone(),
        selected_result_semantics_class: machine
            .domain()
            .selected_result_semantics_class(machine.query()),
        path_problem: machine
            .query()
            .path_goal_anchor()
            .cloned()
            .map(|goal_anchor| SearchPathProblemReplayArtifact { goal_anchor }),
        execution_policy: policy,
        scheduler_profile: policy.scheduler_profile,
        fairness_assumptions: config.fairness_assumptions,
        fairness: fairness.clone(),
        fairness_certificate_trace: fairness_certificate_trace.clone(),
        epoch_trace: observation.graph_epoch_trace.clone(),
        rounds,
        final_state: final_state.clone(),
        termination,
        theorem_pack: theorem_pack.clone(),
        route_bounds: SearchResultBoundArtifact {
            discovery_class: SearchRouteDiscoveryBoundClass::NoCandidate,
            candidate_discovery_bound_steps: None,
            path_problem: replay_path_problem_artifact(
                machine.query().path_goal_anchor().cloned(),
                fairness.certificate.service_bound_steps,
            ),
            recovery_bound_steps_after_latest_epoch: None,
            quality_class: SearchRouteQualityClass::NoCandidate,
            selected_result_cost: None,
            optimality_gap: None,
            approximation_ratio_milli: None,
            admissible_upper_bound: None,
            selected_result_summary: None,
            required_premises: fairness.certificate.required_fairness.clone(),
        },
        final_observation: observation.clone(),
    };
    let route_bounds = route_bound_artifact_for_replay(policy, termination, &replay);
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
            termination,
            progress,
        },
        replay,
    ))
}

type ReportOnlyExecutionResult<D> = Result<
    SearchExecutionReport<
        <D as SearchDomain>::Node,
        <D as SearchDomain>::GraphEpoch,
        <D as SearchDomain>::Cost,
    >,
    SearchRunError<<D as SearchDomain>::Error>,
>;

/// Execute one machine to completion without materializing replay rounds.
///
/// # Errors
///
/// Returns an error if the execution config is invalid, executor proposal
/// generation fails, or the machine violates its invariants while advancing.
///
/// # Panics
///
/// Panics if a batch size does not fit in `u64`.
#[allow(
    clippy::missing_errors_doc,
    clippy::missing_panics_doc,
    clippy::needless_pass_by_value,
    clippy::too_many_lines
)]
pub fn run_with_executor_report_only<D, X>(
    machine: &mut SearchMachine<D>,
    executor: &X,
    config: SearchRunConfig,
) -> ReportOnlyExecutionResult<D>
where
    D: SearchDomain,
    X: ProposalExecutor<D>,
{
    validate_run_config::<D, X>(executor, &config).map_err(SearchRunError::InvalidConfig)?;
    machine.set_observation_trace_recording(false);
    machine.set_selected_result_witness_deferral(true);
    let progress_logging_enabled = env::var("JACQUARD_TELLTALE_PROGRESS").as_deref() == Ok("1");
    let policy = config.execution_policy;
    let step_budget = match policy.effort_profile {
        SearchEffortProfile::RunToCompletion => None,
        SearchEffortProfile::SchedulerStepBudget(budget) => Some(budget),
    };
    let mut representative_epoch = None;
    let mut representative_phase = None;
    let mut representative_batch_nodes = Vec::new();
    let mut representative_commits = Vec::new();
    while let Some(batch) = machine.next_batch() {
        if step_budget
            .is_some_and(|budget| machine.state().trace_state.total_scheduler_steps >= budget)
        {
            break;
        }
        let mut proposals = executor
            .generate(machine.domain(), &batch, machine.query())
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
        if progress_logging_enabled
            && machine.state().trace_state.total_scheduler_steps % 50_000 == 0
        {
            eprintln!(
                "[telltale-progress] steps={} productive={} batches={} open={} closed={} accepted_nodes={}",
                machine.state().trace_state.total_scheduler_steps,
                machine.state().trace_state.productive_steps,
                machine.state().budget_state.batches,
                machine.state().open.len(),
                machine.state().closed.len(),
                machine.query().accepted_nodes().len(),
            );
        }
        machine
            .check_invariants()
            .map_err(SearchError::InvariantViolation)
            .map_err(SearchRunError::Search)?;

        if representative_epoch.is_none() {
            representative_epoch = Some(batch.epoch.clone());
            representative_phase = Some(batch.phase);
            representative_batch_nodes = batch
                .entries
                .iter()
                .map(|entry| entry.node.clone())
                .collect();
            representative_commits =
                machine.observation().normalized_commit_trace[pre_commit_len..].to_vec();
        }
    }

    let termination = match step_budget {
        Some(budget)
            if machine.next_batch().is_some()
                && machine.state().trace_state.total_scheduler_steps >= budget =>
        {
            SearchRunTermination::SchedulerStepBudgetExhausted
        }
        _ => SearchRunTermination::Completed,
    };

    let observation = machine.observation_artifact_without_replay(
        policy.scheduler_profile,
        config.fairness_assumptions.clone(),
    );
    let total_step_mode = match policy.scheduler_profile {
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
        execution_policy: policy,
        scheduler_profile: policy.scheduler_profile,
        authority_class: classify_scheduler_artifact(policy.scheduler_profile),
        batch_width: policy.batch_width,
        fairness_assumptions: config.fairness_assumptions.clone(),
    };
    let final_state = state_artifact_for_machine(machine);
    let theorem_pack = search_theorem_pack_artifact();
    let fairness = fairness_artifact_for_window(
        policy.scheduler_profile,
        representative_epoch,
        representative_phase,
        representative_batch_nodes,
        representative_commits,
    );
    let route_bounds = route_bound_artifact_for_report_only(
        policy,
        termination,
        &observation,
        machine.query().path_goal_anchor().cloned(),
        &fairness,
    );
    Ok(SearchExecutionReport {
        observation,
        scheduler,
        fairness,
        fairness_certificate_trace: Vec::new(),
        final_state,
        theorem_pack,
        route_bounds,
        termination,
        progress,
    })
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
    machine
        .observation_mut()
        .reseed_policy_trace
        .push(request.reseeding_policy);
    machine.state_mut().closed.clear();
    machine.last_batch = None;
    machine.state_mut().incumbent = None;
    machine.state_mut().selected_terminal = None;
    match request.reseeding_policy {
        SearchReseedingPolicy::StartOnly => {
            machine.state_mut().incons.clear();
            machine.state_mut().open.clear();
            machine.state_mut().g_score.clear();
            machine.state_mut().parent.clear();

            let entry = machine.rebuild_frontier_entry(&start, D::Cost::zero());
            machine
                .state_mut()
                .g_score
                .insert(start.clone(), D::Cost::zero());
            machine.state_mut().open.insert(start, entry);
            machine.sync_lookup_state_from_canonical();
        }
        SearchReseedingPolicy::PreserveOpenAndIncons => {
            let rebuild_nodes = machine
                .state()
                .open
                .keys()
                .cloned()
                .chain(machine.state().incons.iter().cloned())
                .chain(core::iter::once(start.clone()))
                .collect::<BTreeSet<_>>();

            let retained_nodes =
                retained_parent_closure(&start, &rebuild_nodes, &machine.state().parent);
            let retained_scores = machine
                .state()
                .g_score
                .iter()
                .filter(|(node, _)| retained_nodes.contains(*node))
                .map(|(node, score)| (node.clone(), *score))
                .collect::<BTreeMap<_, _>>();
            let retained_parent = machine
                .state()
                .parent
                .iter()
                .filter(|(node, parent)| {
                    retained_nodes.contains(*node) && retained_nodes.contains(&parent.from)
                })
                .map(|(node, parent)| (node.clone(), parent.clone()))
                .collect::<BTreeMap<_, _>>();

            machine.state_mut().open.clear();
            machine.state_mut().incons.clear();
            machine.state_mut().g_score = retained_scores;
            machine.state_mut().parent = retained_parent;

            for node in rebuild_nodes {
                let g_score = *machine
                    .state()
                    .g_score
                    .get(&node)
                    .unwrap_or(&D::Cost::zero());
                machine
                    .state_mut()
                    .g_score
                    .entry(node.clone())
                    .or_insert(g_score);
                let entry = machine.rebuild_frontier_entry(&node, g_score);
                machine.state_mut().open.insert(node, entry);
            }
            machine.sync_lookup_state_from_canonical();
        }
    }
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
    let (selected_result_cost, selected_result_witness, selected_result_publication_trace) =
        match replay.selected_result_semantics_class {
            SearchSelectedResultSemanticsClass::QueryDerived => {
                let (cost, witness) = reconstruct_selected_from_commits(
                    &replay.start,
                    &replay.query,
                    &normalized_commit_trace,
                );
                let publication_trace = derive_selected_result_publication_trace_from_rounds(
                    &replay.start,
                    &replay.query,
                    &replay.rounds,
                );
                (cost, witness, publication_trace)
            }
            SearchSelectedResultSemanticsClass::DomainDefinedFromDiscoveredState => {
                return Err(ReplayError::UnsupportedSelectedResultSemantics);
            }
        };
    let canonical_parent_map = derive_parent_map_from_commits(&normalized_commit_trace);

    let derived = SearchObservationArtifact {
        selected_result_cost,
        selected_result_witness,
        canonical_parent_map,
        selected_result_publication_trace,
        normalized_commit_trace,
        replay_checkpoints: replay.final_observation.replay_checkpoints.clone(),
        graph_epoch_trace: replay.epoch_trace.clone(),
        reseed_policy_trace: replay.final_observation.reseed_policy_trace.clone(),
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

fn derive_selected_result_publication_trace_from_rounds<N, G, S, C>(
    start: &N,
    query: &SearchQuery<N>,
    rounds: &[ReplayRoundRecord<N, G, S, C>],
) -> Vec<IncumbentPublicationRecord<N, C>>
where
    N: Clone + Ord,
    G: Ord,
    S: Ord,
    C: SearchCost,
{
    let mut g_score = BTreeMap::new();
    let mut parent = BTreeMap::new();
    let mut publications = Vec::new();
    let mut current_incumbent: Option<(C, Vec<N>)> = None;
    g_score.insert(start.clone(), C::zero());

    for round in rounds {
        for commit in &round.commits {
            g_score.insert(commit.node.clone(), commit.g_score);
            if let Some(parent_node) = &commit.parent {
                parent.insert(commit.node.clone(), parent_node.clone());
            }
            let Some(next) = best_selected_solution_from_maps(start, query, &g_score, &parent)
            else {
                continue;
            };
            let should_publish = match current_incumbent.as_ref() {
                None => true,
                Some(current) => next.0 < current.0 || (next.0 == current.0 && next.1 < current.1),
            };
            if should_publish {
                publications.push(IncumbentPublicationRecord {
                    cost: next.0,
                    witness: next.1.clone(),
                });
                current_incumbent = Some(next);
            }
        }
    }

    publications
}

fn reconstruct_selected_from_commits<N, C>(
    start: &N,
    query: &SearchQuery<N>,
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

    match best_selected_solution_from_maps(start, query, &g_score, &parent) {
        Some((cost, path)) => (Some(cost), Some(path)),
        None => (None, None),
    }
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

fn retained_parent_closure<N, E, C>(
    start: &N,
    seeds: &BTreeSet<N>,
    parent: &BTreeMap<N, crate::machine::ParentRecord<N, E, C>>,
) -> BTreeSet<N>
where
    N: Clone + Ord,
    E: Clone,
    C: Copy,
{
    let mut retained = BTreeSet::new();
    for seed in seeds {
        let mut cursor = seed.clone();
        retained.insert(cursor.clone());
        while cursor != *start {
            let Some(next_parent) = parent.get(&cursor) else {
                break;
            };
            cursor = next_parent.from.clone();
            if !retained.insert(cursor.clone()) {
                break;
            }
        }
    }
    retained
}

fn best_selected_solution_from_maps<N, C>(
    start: &N,
    query: &SearchQuery<N>,
    g_score: &BTreeMap<N, C>,
    parent: &BTreeMap<N, N>,
) -> Option<(C, Vec<N>)>
where
    N: Clone + Ord,
    C: SearchCost,
{
    query
        .accepted_nodes()
        .iter()
        .filter_map(|node| {
            let cost = g_score.get(node).copied()?;
            let path = reconstruct_path(start, node, parent)?;
            Some((cost, path))
        })
        .min_by(|left, right| left.0.cmp(&right.0).then(left.1.cmp(&right.1)))
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

    /// Rebuild one frontier entry under the current epoch and epsilon.
    pub(crate) fn rebuild_frontier_entry(
        &self,
        node: &D::Node,
        g_score: D::Cost,
    ) -> FrontierEntry<D::Node, D::Cost> {
        Self::frontier_entry_for(
            &self.domain,
            &self.state.graph_epoch,
            &self.query,
            self.state.epsilon,
            node,
            g_score,
        )
    }
}

/// Placeholder runtime marker retained for smoke tests.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SearchRuntimeMarker;
