//! Protocol-machine-backed simulation runner.
//!
//! Wraps `telltale-machine` to execute choreographies through the protocol machine,
//! producing simulator traces plus canonical semantic artifacts.

use std::collections::BTreeMap;
use telltale_types::FixedQ32;

use crate::analysis::{compare_observability, NormalizedObservability, ObservabilityRelation};
use crate::backend::SimulationMachine;
use crate::environment::{
    EnvironmentController, EnvironmentModels, EnvironmentTrace, TransmissionIntent,
};
use crate::fault::{
    AdversaryBudgetRecord, AdversarySummary, AssumptionDiagnostic, AssumptionFailureClass,
    ScheduledAdversary,
};
use crate::field::FieldModel;
use telltale_machine::model::effects::{EffectHandler, EffectTraceEntry};
use telltale_machine::model::output_condition::OutputConditionCheck;
use telltale_machine::model::scheduler_types::{PriorityPolicy, SchedPolicy};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::ObsEvent;
use telltale_machine::{
    ProtocolMachine, ProtocolMachineConfig, ProtocolMachineSemanticObjects, SemanticAuditRecord,
    StepResult,
};
use telltale_types::{GlobalType, LocalTypeR};

use crate::checkpoint::CheckpointStore;
use crate::execution::{execute_scenario_rounds, ScenarioMiddleware, ScenarioMiddlewareCheckpoint};
use crate::harness::derive_initial_states;
use crate::persistence::CheckpointArtifact;
use crate::property::{PropertyContext, PropertyMonitor, PropertyViolation};
use crate::reconfiguration::{ReconfigurationRecord, ReconfigurationSummary};
use crate::scenario::{
    ExecutionBackend, ExecutionRegime, ExecutionSpec, ResolvedExecutionBackend,
    ResolvedSchedulerPolicy, ResolvedTheoremProfile, Scenario,
};
use crate::trace::{StepRecord, Trace};
use crate::value_conv::{f64s_to_values, registers_to_f64s};
use telltale_machine::model::state::SessionState;

/// (coroutine_id, role_name) pair.
type CoroInfo = Vec<(usize, String)>;

// Simulator handlers implement the same external-handler boundary used by the guest runtime.

/// Record state for all roles in a coroutine set.
fn record_all_roles(
    machine: &SimulationMachine,
    coro_info: &CoroInfo,
    step: usize,
    trace: &mut Trace,
) {
    let step_u64 = u64::try_from(step).unwrap_or(u64::MAX);
    for (coro_id, role) in coro_info {
        if let Some(coro) = machine
            .coroutines()
            .into_iter()
            .find(|coro| coro.id == *coro_id)
        {
            trace.record(StepRecord {
                step: step_u64,
                role: role.clone(),
                state: registers_to_f64s(&coro.regs),
            });
        }
    }
}

fn current_role_state(
    machine: &SimulationMachine,
    coro_info: &CoroInfo,
) -> BTreeMap<String, Vec<FixedQ32>> {
    let mut states = BTreeMap::new();
    for (coro_id, role) in coro_info {
        if let Some(coro) = machine
            .coroutines()
            .into_iter()
            .find(|coro| coro.id == *coro_id)
        {
            states.insert(role.clone(), registers_to_f64s(&coro.regs));
        }
    }
    states
}

fn transmissions_at_tick(
    obs_trace: &[ObsEvent],
    tick: u64,
    logical_step: u64,
) -> Vec<TransmissionIntent> {
    obs_trace
        .iter()
        .filter_map(|event| match event {
            ObsEvent::Sent {
                tick: event_tick,
                session,
                from,
                to,
                label,
                ..
            } if *event_tick == tick => Some(TransmissionIntent {
                tick: *event_tick,
                logical_step,
                session: *session,
                from: from.clone(),
                to: to.clone(),
                label: label.clone(),
            }),
            _ => None,
        })
        .collect()
}

/// Initialize coroutine registers from FixedQ32 state vectors.
fn init_coro_regs(
    machine: &mut SimulationMachine,
    coro_info: &CoroInfo,
    initial_states: &BTreeMap<String, Vec<FixedQ32>>,
) -> Result<(), String> {
    for (coro_id, role) in coro_info {
        let init = initial_states
            .get(role)
            .ok_or_else(|| format!("missing initial state for role '{role}'"))?;
        let vals = f64s_to_values(init);
        machine.overwrite_coroutine_registers(*coro_id, 2, &vals)?;
    }
    Ok(())
}

fn productive_event_count(events: &[ObsEvent]) -> u64 {
    u64::try_from(
        events
            .iter()
            .filter(|event| {
                matches!(
                    event,
                    ObsEvent::Sent { .. }
                        | ObsEvent::Received { .. }
                        | ObsEvent::Offered { .. }
                        | ObsEvent::Chose { .. }
                )
            })
            .count(),
    )
    .unwrap_or(u64::MAX)
}

fn session_depth_budget(
    snapshots: &BTreeMap<telltale_machine::model::state::SessionId, SessionState>,
) -> u64 {
    snapshots
        .values()
        .flat_map(|session| session.local_types.values())
        .map(|entry| u64::try_from(type_depth(&entry.current)).unwrap_or(u64::MAX))
        .fold(0u64, u64::saturating_add)
}

fn session_weighted_measure(
    snapshots: &BTreeMap<telltale_machine::model::state::SessionId, SessionState>,
) -> u64 {
    let depth = session_depth_budget(snapshots);
    let buffers = snapshots
        .values()
        .flat_map(|session| session.buffers.values())
        .map(|buffer| u64::try_from(buffer.len()).unwrap_or(u64::MAX))
        .fold(0u64, u64::saturating_add);
    depth.saturating_mul(2).saturating_add(buffers)
}

fn contains_recursion(lt: &LocalTypeR) -> bool {
    match lt {
        LocalTypeR::Mu { body, .. } => contains_recursion(body),
        LocalTypeR::Var(_) => true,
        LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
            branches.iter().any(|(_, _, cont)| contains_recursion(cont))
        }
        LocalTypeR::End => false,
    }
}

fn type_depth(lt: &LocalTypeR) -> usize {
    match lt {
        LocalTypeR::End | LocalTypeR::Var(_) => 0,
        LocalTypeR::Mu { body, .. } => type_depth(body),
        LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
            let max_branch = branches
                .iter()
                .map(|(_, _, cont)| type_depth(cont))
                .max()
                .unwrap_or(0);
            1 + max_branch
        }
    }
}

/// A choreography specification for concurrent execution.
pub struct ChoreographySpec {
    /// Local types per role.
    pub local_types: BTreeMap<String, LocalTypeR>,
    /// Global type.
    pub global_type: GlobalType,
    /// Initial state vectors per role.
    pub initial_states: BTreeMap<String, Vec<FixedQ32>>,
}

/// Run multiple choreographies on the canonical protocol-machine lane.
///
/// Each choreography gets its own session namespace. Returns one trace per
/// choreography, indexed in the same order as the input specs.
///
/// # Errors
///
/// Returns an error string if loading or execution fails.
#[allow(clippy::cognitive_complexity)]
pub fn run_multi_session_canonical(
    specs: &[ChoreographySpec],
    steps: usize,
    handler: &dyn EffectHandler,
) -> Result<Vec<Trace>, String> {
    let mut machine =
        SimulationMachine::Canonical(ProtocolMachine::new(ProtocolMachineConfig::default()));

    let mut session_infos: Vec<(usize, CoroInfo)> = Vec::new();

    for (session_idx, spec) in specs.iter().enumerate() {
        let image = CodeImage::from_local_types(&spec.local_types, &spec.global_type);
        let owned = machine
            .load_choreography_owned(&image, format!("sim/concurrent/{session_idx}"))
            .map_err(|e| format!("load error: {e}"))?;
        let sid = owned.session_id();

        let coros = machine.session_coroutines(sid);
        let coro_info: CoroInfo = coros.iter().map(|c| (c.id, c.role.clone())).collect();
        init_coro_regs(&mut machine, &coro_info, &spec.initial_states)?;
        session_infos.push((sid, coro_info));
    }

    let max_rounds = steps.saturating_sub(1);
    let mut per_session_step: Vec<usize> = vec![0; specs.len()];
    let mut traces: Vec<Trace> = (0..specs.len()).map(|_| Trace::new()).collect();

    // Record initial state (step 0 = Mu step).
    for (si, (_sid, coro_info)) in session_infos.iter().enumerate() {
        if steps > 0 {
            record_all_roles(&machine, coro_info, 0, &mut traces[si]);
            per_session_step[si] = 1;
        }
    }

    for _ in 0..max_rounds {
        if per_session_step.iter().all(|&s| s >= steps) {
            break;
        }

        match machine.step_round(handler, 1) {
            Ok(StepResult::AllDone | StepResult::Stuck) => break,
            Ok(StepResult::Continue) => {}
            Err(e) => return Err(format!("protocol machine error: {e}")),
        }

        for (si, (_sid, coro_info)) in session_infos.iter().enumerate() {
            if per_session_step[si] < steps {
                record_all_roles(&machine, coro_info, per_session_step[si], &mut traces[si]);
                per_session_step[si] += 1;
            }
        }
    }

    // Fall back to final state if no intermediate records.
    for (i, (_sid, coro_info)) in session_infos.iter().enumerate() {
        if traces[i].records.is_empty() {
            record_all_roles(&machine, coro_info, steps.saturating_sub(1), &mut traces[i]);
        }
    }

    Ok(traces)
}

/// Run a choreography through the protocol machine and return a simulator-compatible trace.
///
/// Sampling is round-based. Step `0` records the initial state before any
/// scheduler rounds run, and each subsequent step records the state after one
/// completed protocol-machine round.
///
/// # Errors
///
/// Returns an error string if protocol-machine execution fails.
pub fn run(
    local_types: &BTreeMap<String, LocalTypeR>,
    global_type: &GlobalType,
    initial_states: &BTreeMap<String, Vec<FixedQ32>>,
    steps: usize,
    handler: &dyn EffectHandler,
) -> Result<Trace, String> {
    let image = CodeImage::from_local_types(local_types, global_type);

    let mut machine =
        SimulationMachine::Canonical(ProtocolMachine::new(ProtocolMachineConfig::default()));
    let sid = machine
        .load_choreography_owned(&image, "sim/run")
        .map_err(|e| format!("load error: {e}"))?;
    let sid = sid.session_id();

    let coros = machine.session_coroutines(sid);
    let coro_info: CoroInfo = coros.iter().map(|c| (c.id, c.role.clone())).collect();
    init_coro_regs(&mut machine, &coro_info, initial_states)?;

    let mut trace = Trace::new();

    let max_rounds = steps.saturating_sub(1);
    let mut step_idx: usize = 0;

    // Record initial state (step 0 = Mu step).
    if steps > 0 {
        record_all_roles(&machine, &coro_info, 0, &mut trace);
        step_idx = 1;
    }

    for _ in 0..max_rounds {
        if step_idx >= steps {
            break;
        }

        match machine.step_round(handler, 1) {
            Ok(StepResult::AllDone | StepResult::Stuck) => break,
            Ok(StepResult::Continue) => {}
            Err(e) => return Err(format!("protocol machine error: {e}")),
        }

        record_all_roles(&machine, &coro_info, step_idx, &mut trace);
        step_idx += 1;
    }

    if trace.records.is_empty() {
        record_all_roles(&machine, &coro_info, steps.saturating_sub(1), &mut trace);
    }

    Ok(trace)
}

/// Result of a scenario-backed run.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, PartialEq)]
pub struct ScenarioResult {
    /// Execution trace with step records.
    pub trace: Trace,
    /// Property violations detected during execution.
    pub violations: Vec<PropertyViolation>,
    /// Replay-ready protocol-machine artifact data captured for this run.
    pub replay: ScenarioReplayArtifact,
    /// Envelope-normalized analysis artifacts derived from replay-visible data.
    pub analysis: ScenarioAnalysisArtifact,
    /// Structured run statistics for observability.
    pub stats: ScenarioStats,
}

/// Analysis artifacts derived from a scenario run without weakening canonical replay.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, PartialEq, Eq)]
pub struct ScenarioAnalysisArtifact {
    /// Envelope-normalized observability class derived from raw replay traces.
    pub normalized_observability: NormalizedObservability,
}

/// Replay-ready artifact data captured from a scenario run.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, PartialEq)]
pub struct ScenarioReplayArtifact {
    /// Resolved theorem/profile information for this run.
    pub theorem_profile: ResolvedTheoremProfile,
    /// Resolved adversary program used by the transport/crash middleware.
    pub adversary_schedule: Vec<ScheduledAdversary>,
    /// Budget-consumption history recorded by the adversary middleware.
    pub adversary_budget_history: Vec<AdversaryBudgetRecord>,
    /// Assumption-bundle diagnostics derived from adversary budgets and theorem regime checks.
    pub assumption_diagnostics: Vec<AssumptionDiagnostic>,
    /// Raw observable protocol-machine trace.
    pub obs_trace: Vec<ObsEvent>,
    /// Effect trace entries for deterministic replay.
    pub effect_trace: Vec<EffectTraceEntry>,
    /// Canonical typed effect exchanges captured from the guest runtime.
    pub effect_exchanges: Vec<telltale_machine::EffectExchangeRecord>,
    /// Output-condition verification checks captured by the protocol machine.
    pub output_condition_trace: Vec<OutputConditionCheck>,
    /// Canonical semantic audit records derived from the protocol-machine run.
    pub semantic_audit_log: Vec<SemanticAuditRecord>,
    /// Canonical semantic object export captured from the protocol-machine run.
    pub semantic_objects: ProtocolMachineSemanticObjects,
    /// Canonical simulator reconfiguration trace captured from the shared execution core.
    pub reconfiguration_trace: Vec<ReconfigurationRecord>,
    /// Canonical environment trace captured from shared environment hooks.
    pub environment_trace: EnvironmentTrace,
    /// Serialized canonical checkpoints captured during the run.
    pub checkpoints: Vec<CheckpointArtifact>,
}

/// Structured statistics emitted by scenario execution.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, PartialEq, Eq)]
pub struct ScenarioStats {
    /// Scenario seed used for middleware RNG.
    pub seed: u64,
    /// Proof-side execution regime classification.
    pub execution_regime: ExecutionRegime,
    /// Resolved theorem/profile information for this run.
    pub theorem_profile: ResolvedTheoremProfile,
    /// Theorem-native progress summary derived from session snapshots and productive events.
    pub theorem_progress: TheoremProgressSummary,
    /// Scheduler-facing theorem/native execution profile summary for the run.
    pub scheduler_profile: SchedulerProfileSummary,
    /// Reconfiguration accounting summary kept separate from theorem progress descent.
    pub reconfiguration_summary: ReconfigurationSummary,
    /// Environment trace emitted by shared environment hooks.
    pub environment_trace: EnvironmentTrace,
    /// Adversary-budget summary for the run.
    pub adversary_summary: AdversarySummary,
    /// Assumption-bundle diagnostics derived from adversary budgets and theorem regime checks.
    pub assumption_diagnostics: Vec<AssumptionDiagnostic>,
    /// Resolved execution backend.
    pub backend: ResolvedExecutionBackend,
    /// Resolved scheduler concurrency value.
    pub scheduler_concurrency: u64,
    /// Resolved worker-thread count.
    pub worker_threads: u64,
    /// Number of protocol-machine rounds executed by the scenario loop.
    pub rounds_executed: u64,
    /// Final protocol-machine clock tick.
    pub final_tick: u64,
    /// Number of observable events in the final protocol-machine trace.
    pub total_obs_events: usize,
    /// Number of observed `Invoked` events.
    pub total_invoked_events: usize,
    /// Number of checkpoint writes attempted by interval policy.
    pub checkpoint_writes: usize,
    /// Last non-fatal checkpoint capture error observed during the run.
    pub checkpoint_error: Option<String>,
}

/// Theorem-native progress summary for one scenario run.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, PartialEq, Eq)]
pub struct TheoremProgressSummary {
    /// Initial weighted measure `W = 2 * depth + buffer`.
    pub initial_weighted_measure: u64,
    /// Initial exact productive-step budget for recursion-free protocols.
    pub initial_depth_budget: u64,
    /// Productive communication events observed during the run.
    pub productive_step_count: u64,
    /// Final weighted measure after execution.
    pub remaining_weighted_measure: u64,
    /// Weighted measure consumed over the run.
    pub weighted_measure_consumed: u64,
    /// Critical-capacity summary for supported scenarios.
    pub critical_capacity: CriticalCapacitySummary,
}

/// Scheduler-profile summary for theorem-native scheduling semantics.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, PartialEq, Eq)]
pub struct SchedulerProfileSummary {
    /// Resolved implementation scheduler policy.
    pub implementation_policy: ResolvedSchedulerPolicy,
    /// Resolved theorem-facing scheduler profile.
    pub theorem_profile: crate::scenario::TheoremSchedulerProfile,
    /// Whether productive-step accounting remains exact.
    pub productive_exactness: bool,
    /// Whether only productive exactness is available or a conservative total-step bound exists.
    pub total_step_mode: SchedulerBoundMode,
    /// Conservative total-step upper bound when the selected scheduler profile admits one.
    pub total_step_upper_bound: Option<u64>,
    /// Fairness premise required by the implementation policy.
    pub fairness_requirement: SchedulerFairnessRequirement,
    /// Envelope/adherence status under the theorem profile.
    pub envelope_status: SchedulerEnvelopeStatus,
}

/// Scheduler-bound availability class.
#[derive(Debug, Clone, Copy, serde::Serialize, serde::Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum SchedulerBoundMode {
    /// Only productive-step accounting is reported exactly.
    ProductiveExactOnly,
    /// A conservative total-step bound is available.
    ConservativeTotalStepBound,
}

/// Fairness premise required by the scheduler policy.
#[derive(Debug, Clone, Copy, serde::Serialize, serde::Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
#[allow(clippy::enum_variant_names)]
pub enum SchedulerFairnessRequirement {
    /// Fairness depends on roles yielding cooperatively.
    ExplicitYieldFairness,
    /// Fairness depends on round-robin queue rotation.
    RoundRobinQueueFairness,
    /// Fairness depends on aging priority promotion.
    AgingPriorityFairness,
    /// Fairness depends on token-weighted priority discipline.
    TokenWeightedFairness,
    /// Fairness depends on progress-token availability.
    ProgressTokenFairness,
}

/// Envelope/adherence status for the resolved scheduler profile.
#[derive(Debug, Clone, Copy, serde::Serialize, serde::Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum SchedulerEnvelopeStatus {
    /// The run is theorem-exact for this scheduler profile.
    Exact,
    /// The run is admitted under envelope adherence only.
    EnvelopeAdherent,
    /// The run is admitted under the broader envelope admission contract.
    EnvelopeAdmitted,
    /// The declared scheduler profile is not theorem-backed for this run.
    Ineligible,
}

/// Cross-run scheduler comparison anchored to normalized observability.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, PartialEq, Eq)]
pub struct SchedulerComparison {
    /// Baseline run scheduler profile.
    pub baseline: SchedulerProfileSummary,
    /// Candidate run scheduler profile.
    pub candidate: SchedulerProfileSummary,
    /// Raw-vs-normalized observability relation between the runs.
    pub observability_relation: ObservabilityRelation,
    /// Whether theorem-backed eligibility matches across the runs.
    pub theorem_eligibility_match: bool,
    /// Whether the difference is performance/classification-only rather than semantic.
    pub performance_only_difference: bool,
}

/// Critical-capacity classification summary.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize, PartialEq, Eq)]
pub struct CriticalCapacitySummary {
    /// Threshold used for classification when available.
    pub threshold: Option<u64>,
    /// Phase classification relative to the threshold.
    pub phase: CriticalCapacityPhase,
}

/// Critical-capacity phase classification.
#[derive(Debug, Clone, Copy, serde::Serialize, serde::Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum CriticalCapacityPhase {
    /// The scenario does not currently admit theorem-native phase classification.
    Unsupported,
    /// Observed productive load stayed below the threshold.
    BelowThreshold,
    /// Observed productive load saturated the threshold exactly.
    AtThreshold,
    /// Observed productive load exceeded the threshold.
    AboveThreshold,
}

fn scheduler_profile_summary(
    resolved_policy: ResolvedSchedulerPolicy,
    theorem_profile: &ResolvedTheoremProfile,
    initial_weighted_measure: u64,
    scheduler_concurrency: u64,
) -> SchedulerProfileSummary {
    let (total_step_mode, total_step_upper_bound) =
        if theorem_profile.eligibility == crate::scenario::TheoremEligibility::EnvelopeBounded {
            (
                SchedulerBoundMode::ConservativeTotalStepBound,
                Some(initial_weighted_measure.saturating_mul(scheduler_concurrency.max(1))),
            )
        } else {
            (SchedulerBoundMode::ProductiveExactOnly, None)
        };

    let fairness_requirement = match resolved_policy {
        ResolvedSchedulerPolicy::Cooperative => SchedulerFairnessRequirement::ExplicitYieldFairness,
        ResolvedSchedulerPolicy::RoundRobin => {
            SchedulerFairnessRequirement::RoundRobinQueueFairness
        }
        ResolvedSchedulerPolicy::PriorityAging => {
            SchedulerFairnessRequirement::AgingPriorityFairness
        }
        ResolvedSchedulerPolicy::PriorityTokenWeighted => {
            SchedulerFairnessRequirement::TokenWeightedFairness
        }
        ResolvedSchedulerPolicy::ProgressAware => {
            SchedulerFairnessRequirement::ProgressTokenFairness
        }
    };

    let envelope_status = if theorem_profile.eligibility
        == crate::scenario::TheoremEligibility::Ineligible
    {
        SchedulerEnvelopeStatus::Ineligible
    } else {
        match theorem_profile.envelope_profile {
            crate::scenario::TheoremEnvelopeProfile::Exact => SchedulerEnvelopeStatus::Exact,
            crate::scenario::TheoremEnvelopeProfile::ProtocolMachineEnvelopeAdherence => {
                SchedulerEnvelopeStatus::EnvelopeAdherent
            }
            crate::scenario::TheoremEnvelopeProfile::ProtocolMachineEnvelopeAdmission => {
                SchedulerEnvelopeStatus::EnvelopeAdmitted
            }
            crate::scenario::TheoremEnvelopeProfile::None
            | crate::scenario::TheoremEnvelopeProfile::Auto => SchedulerEnvelopeStatus::Ineligible,
        }
    };

    SchedulerProfileSummary {
        implementation_policy: resolved_policy,
        theorem_profile: theorem_profile.scheduler_profile,
        productive_exactness: true,
        total_step_mode,
        total_step_upper_bound,
        fairness_requirement,
        envelope_status,
    }
}

fn machine_scheduler_policy(policy: ResolvedSchedulerPolicy) -> SchedPolicy {
    match policy {
        ResolvedSchedulerPolicy::Cooperative => SchedPolicy::Cooperative,
        ResolvedSchedulerPolicy::RoundRobin => SchedPolicy::RoundRobin,
        ResolvedSchedulerPolicy::PriorityAging => SchedPolicy::Priority(PriorityPolicy::Aging),
        ResolvedSchedulerPolicy::PriorityTokenWeighted => {
            SchedPolicy::Priority(PriorityPolicy::TokenWeighted)
        }
        ResolvedSchedulerPolicy::ProgressAware => SchedPolicy::ProgressAware,
    }
}

/// Compare two scenario runs through their scheduler-profile summaries and normalized observability.
#[must_use]
pub fn compare_scheduler_runs(
    baseline: &ScenarioResult,
    candidate: &ScenarioResult,
) -> SchedulerComparison {
    let observability = compare_observability(
        &baseline.replay.obs_trace,
        &baseline.replay.reconfiguration_trace,
        &baseline.analysis.normalized_observability,
        &candidate.replay.obs_trace,
        &candidate.replay.reconfiguration_trace,
        &candidate.analysis.normalized_observability,
    );
    let theorem_eligibility_match =
        baseline.stats.theorem_profile.eligibility == candidate.stats.theorem_profile.eligibility;

    SchedulerComparison {
        baseline: baseline.stats.scheduler_profile.clone(),
        candidate: candidate.stats.scheduler_profile.clone(),
        observability_relation: observability.relation,
        theorem_eligibility_match,
        performance_only_difference: theorem_eligibility_match
            && observability.relation != ObservabilityRelation::SafetyVisibleDivergence,
    }
}

fn snapshot_contains_recursion(
    snapshots: &BTreeMap<telltale_machine::model::state::SessionId, SessionState>,
) -> bool {
    snapshots
        .values()
        .flat_map(|session| session.local_types.values())
        .any(|entry| contains_recursion(&entry.current))
}

fn critical_capacity_summary(
    initial_snapshots: &BTreeMap<telltale_machine::model::state::SessionId, SessionState>,
    productive_step_count: u64,
    initial_depth_budget: u64,
) -> CriticalCapacitySummary {
    if snapshot_contains_recursion(initial_snapshots) {
        return CriticalCapacitySummary {
            threshold: None,
            phase: CriticalCapacityPhase::Unsupported,
        };
    }

    let phase = match productive_step_count.cmp(&initial_depth_budget) {
        std::cmp::Ordering::Less => CriticalCapacityPhase::BelowThreshold,
        std::cmp::Ordering::Equal => CriticalCapacityPhase::AtThreshold,
        std::cmp::Ordering::Greater => CriticalCapacityPhase::AboveThreshold,
    };

    CriticalCapacitySummary {
        threshold: Some(initial_depth_budget),
        phase,
    }
}

fn theorem_progress_summary(
    initial_snapshots: &BTreeMap<telltale_machine::model::state::SessionId, SessionState>,
    final_snapshots: &BTreeMap<telltale_machine::model::state::SessionId, SessionState>,
    productive_step_count: u64,
) -> TheoremProgressSummary {
    let initial_depth_budget = session_depth_budget(initial_snapshots);
    let initial_weighted_measure = session_weighted_measure(initial_snapshots);
    let remaining_weighted_measure = session_weighted_measure(final_snapshots);

    TheoremProgressSummary {
        initial_weighted_measure,
        initial_depth_budget,
        productive_step_count,
        remaining_weighted_measure,
        weighted_measure_consumed: initial_weighted_measure
            .saturating_sub(remaining_weighted_measure),
        critical_capacity: critical_capacity_summary(
            initial_snapshots,
            productive_step_count,
            initial_depth_budget,
        ),
    }
}

fn assumption_diagnostics_with_regime(
    theorem_profile: &ResolvedTheoremProfile,
    mut diagnostics: Vec<AssumptionDiagnostic>,
) -> Vec<AssumptionDiagnostic> {
    if let Some(reason) = theorem_profile
        .eligibility_reason
        .as_ref()
        .filter(|_| theorem_profile.eligibility == crate::scenario::TheoremEligibility::Ineligible)
    {
        diagnostics.push(AssumptionDiagnostic {
            tick: 0,
            class: AssumptionFailureClass::UnsupportedRegime,
            adversary_id: None,
            detail: reason.clone(),
        });
    }
    diagnostics
}

fn validate_checkpoint_machine_matches_scenario(
    scenario: &Scenario,
    machine: &ProtocolMachine,
) -> Result<(), String> {
    let mut checkpoint_roles: Vec<_> = machine
        .coroutines()
        .iter()
        .map(|coro| coro.role.clone())
        .collect();
    checkpoint_roles.sort();
    checkpoint_roles.dedup();

    let mut scenario_roles = scenario.roles.clone();
    scenario_roles.sort();
    scenario_roles.dedup();

    if checkpoint_roles != scenario_roles {
        return Err(format!(
            "checkpoint roles {:?} do not match scenario roles {:?}",
            checkpoint_roles, scenario_roles
        ));
    }
    Ok(())
}

/// Run a choreography with scenario-defined middleware (adversaries/network/properties).
///
/// # Errors
///
/// Returns an error string if protocol-machine execution fails.
#[allow(clippy::too_many_lines)]
pub fn run_with_scenario(
    local_types: &BTreeMap<String, LocalTypeR>,
    global_type: &GlobalType,
    initial_states: &BTreeMap<String, Vec<FixedQ32>>,
    scenario: &Scenario,
    handler: &dyn EffectHandler,
) -> Result<ScenarioResult, String> {
    run_with_scenario_and_environment(
        local_types,
        global_type,
        initial_states,
        scenario,
        handler,
        None,
    )
}

/// Build the authoritative canonical replay variant of a scenario.
///
/// This disables checkpoint emission and forces the canonical serialized execution lane
/// used for replay, debugging, and exact artifact reproduction.
#[must_use]
pub fn canonical_replay_scenario(scenario: &Scenario) -> Scenario {
    let mut replay = scenario.clone();
    replay.execution = ExecutionSpec {
        backend: ExecutionBackend::Canonical,
        scheduler_policy: replay.execution.scheduler_policy,
        scheduler_concurrency: Some(1),
        worker_threads: Some(1),
    };
    replay.checkpoint_interval = None;
    replay
}

/// Re-run a scenario through the authoritative canonical replay lane.
///
/// This is the public replay surface for reproducing exact simulator artifacts under the
/// canonical backend, even when the original scenario was executed under a different exact lane.
///
/// # Errors
///
/// Returns an error if the canonical replay run fails.
pub fn run_canonical_replay(
    local_types: &BTreeMap<String, LocalTypeR>,
    global_type: &GlobalType,
    initial_states: &BTreeMap<String, Vec<FixedQ32>>,
    scenario: &Scenario,
    handler: &dyn EffectHandler,
) -> Result<ScenarioResult, String> {
    let replay = canonical_replay_scenario(scenario);
    run_with_scenario(local_types, global_type, initial_states, &replay, handler)
}

fn execute_loaded_scenario_machine(
    scenario: &Scenario,
    handler: &dyn EffectHandler,
    environment_models: Option<EnvironmentModels<'_>>,
    mut machine: SimulationMachine,
    coro_info: &CoroInfo,
    resolved_execution: &crate::scenario::ResolvedExecution,
    theorem_profile: ResolvedTheoremProfile,
    rounds_to_run: u64,
    middleware_checkpoint: Option<&ScenarioMiddlewareCheckpoint>,
) -> Result<ScenarioResult, String> {
    let initial_session_snapshots = machine.session_snapshots();
    let initial_role_state = current_role_state(&machine, coro_info);

    let mut trace = Trace::new();
    let steps_limit = usize::try_from(rounds_to_run.saturating_add(1))
        .map_err(|_| format!("replay step limit {} exceeds usize", rounds_to_run))?;
    let concurrency = usize::try_from(resolved_execution.scheduler_concurrency).map_err(|_| {
        format!(
            "scenario.execution.scheduler_concurrency {} exceeds usize",
            resolved_execution.scheduler_concurrency
        )
    })?;
    let mut step_idx: usize = 0;
    let mut checkpoint_writes: usize = 0;
    if steps_limit > 0 {
        record_all_roles(&machine, coro_info, 0, &mut trace);
        step_idx = 1;
    }

    let mut monitor = scenario
        .property_monitor()
        .map_err(|e| format!("properties: {e}"))?
        .unwrap_or_else(|| PropertyMonitor::new(Vec::new()));

    let mut checkpoints = scenario.checkpoint_interval.map(|interval| {
        let dir = std::path::PathBuf::from("artifacts").join(&scenario.name);
        CheckpointStore::with_dir(interval, dir)
    });

    let middleware = match middleware_checkpoint {
        Some(checkpoint) => ScenarioMiddleware::from_checkpoint(
            scenario,
            handler,
            machine.clock().tick_duration,
            checkpoint,
        ),
        None => ScenarioMiddleware::from_scenario(scenario, handler, machine.clock().tick_duration),
    }
    .map_err(|e| format!("middleware setup: {e}"))?;
    let mut environment = EnvironmentController::new(
        &scenario.roles,
        scenario
            .field
            .as_ref()
            .map(|field| field.field_name().to_string()),
        environment_models,
    );

    let execution = execute_scenario_rounds(
        &mut machine,
        scenario,
        &middleware,
        concurrency,
        rounds_to_run,
        |machine, completed_rounds| {
            if step_idx >= steps_limit {
                return Ok(());
            }

            record_all_roles(machine, coro_info, step_idx, &mut trace);
            step_idx += 1;

            if environment.is_active() {
                let current_tick = machine.clock().tick;
                let current_role_state = current_role_state(machine, coro_info);
                environment.begin_round(current_tick, completed_rounds, current_role_state)?;
                let transmissions =
                    transmissions_at_tick(machine.trace(), current_tick, completed_rounds);
                environment.finish_round(&transmissions)?;
            }

            let session_snapshots = machine.session_snapshots();
            let coroutine_snapshots = machine.coroutines();
            let ctx = PropertyContext {
                tick: machine.clock().tick,
                trace: machine.trace(),
                sessions: &session_snapshots,
                coroutines: &coroutine_snapshots,
            };
            monitor.check(&ctx);
            if let Some(store) = &mut checkpoints {
                if let Some(interval) = scenario.checkpoint_interval {
                    if interval != 0 && machine.clock().tick % interval == 0 {
                        checkpoint_writes = checkpoint_writes.saturating_add(1);
                        if let SimulationMachine::Canonical(inner) = machine {
                            let checkpoint = CheckpointArtifact::capture(
                                inner.clock().tick,
                                inner,
                                Some(middleware.checkpoint_state()?),
                            )?;
                            store.maybe_checkpoint(checkpoint);
                        }
                    }
                }
            }
            Ok(())
        },
    )?;
    let rounds_executed = execution.rounds_executed;

    if trace.records.is_empty() {
        let fallback_step = steps_limit.saturating_sub(1);
        record_all_roles(&machine, coro_info, fallback_step, &mut trace);
    }

    let obs_trace = machine.trace().to_vec();
    let effect_trace = machine.effect_trace().to_vec();
    let output_condition_trace = machine.output_condition_checks().to_vec();
    let semantic_audit_log = machine.semantic_audit_log();
    let semantic_objects = machine.semantic_objects();
    let adversary_schedule = middleware.adversary_schedule();
    let adversary_budget_history = middleware.adversary_budget_history()?;
    let adversary_summary = middleware.adversary_summary()?;
    let assumption_diagnostics = assumption_diagnostics_with_regime(
        &theorem_profile,
        middleware.adversary_assumption_diagnostics()?,
    );
    let reconfiguration_trace = middleware.reconfiguration_trace()?;
    let reconfiguration_summary = middleware.reconfiguration_summary()?;
    if environment.is_active() && environment.trace().records.is_empty() && steps_limit > 0 {
        environment.begin_round(machine.clock().tick, 0, initial_role_state)?;
    }
    let environment_trace = environment.trace().clone();
    let normalized_observability =
        crate::analysis::normalized_observability(&obs_trace, &reconfiguration_trace);
    let checkpoint_artifacts = checkpoints
        .as_ref()
        .map(|store| store.checkpoints().values().cloned().collect::<Vec<_>>())
        .unwrap_or_default();
    let checkpoint_error = checkpoints
        .as_ref()
        .and_then(|store| store.last_persist_error().map(ToOwned::to_owned));
    let final_session_snapshots = machine.session_snapshots();
    let productive_step_count = productive_event_count(&obs_trace);
    let theorem_progress = theorem_progress_summary(
        &initial_session_snapshots,
        &final_session_snapshots,
        productive_step_count,
    );
    let scheduler_profile = scheduler_profile_summary(
        resolved_execution.scheduler_policy,
        &theorem_profile,
        theorem_progress.initial_weighted_measure,
        resolved_execution.scheduler_concurrency,
    );
    let total_invoked_events = obs_trace
        .iter()
        .filter(|event| matches!(event, ObsEvent::Invoked { .. }))
        .count();

    Ok(ScenarioResult {
        trace,
        violations: monitor.violations().to_vec(),
        replay: ScenarioReplayArtifact {
            theorem_profile: theorem_profile.clone(),
            adversary_schedule,
            adversary_budget_history,
            assumption_diagnostics: assumption_diagnostics.clone(),
            obs_trace,
            effect_trace,
            effect_exchanges: machine.effect_exchanges().to_vec(),
            output_condition_trace,
            semantic_audit_log,
            semantic_objects,
            reconfiguration_trace,
            environment_trace: environment_trace.clone(),
            checkpoints: checkpoint_artifacts,
        },
        analysis: ScenarioAnalysisArtifact {
            normalized_observability,
        },
        stats: ScenarioStats {
            seed: scenario.seed,
            execution_regime: resolved_execution.regime(),
            theorem_profile,
            theorem_progress,
            scheduler_profile,
            reconfiguration_summary,
            environment_trace,
            adversary_summary,
            assumption_diagnostics,
            backend: resolved_execution.backend,
            scheduler_concurrency: resolved_execution.scheduler_concurrency,
            worker_threads: resolved_execution.worker_threads,
            rounds_executed,
            final_tick: machine.clock().tick,
            total_obs_events: machine.trace().len(),
            total_invoked_events,
            checkpoint_writes,
            checkpoint_error,
        },
    })
}

/// Resolve how many rounds remain after restoring a canonical checkpoint.
#[must_use]
pub fn remaining_rounds_from_checkpoint(scenario: &Scenario, machine: &ProtocolMachine) -> u64 {
    scenario
        .steps
        .saturating_sub(1)
        .saturating_sub(machine.clock().tick)
}

/// Resume a canonical simulator run from a previously serialized checkpoint.
///
/// The checkpoint must come from the canonical backend. When `rounds` is `None`,
/// the runner executes only the remaining rounds implied by `scenario.steps`.
///
/// # Errors
///
/// Returns an error if the scenario is not canonical, the checkpoint cannot be
/// resumed under the declared execution contract, or middleware/setup fails.
pub fn resume_with_scenario_from_checkpoint(
    scenario: &Scenario,
    machine: ProtocolMachine,
    handler: &dyn EffectHandler,
    environment_models: Option<EnvironmentModels<'_>>,
    rounds: Option<u64>,
) -> Result<ScenarioResult, String> {
    let resolved_execution = scenario.resolved_execution()?;
    if resolved_execution.backend != ResolvedExecutionBackend::Canonical {
        return Err(
            "checkpoint replay currently requires the canonical simulator backend".to_string(),
        );
    }
    validate_checkpoint_machine_matches_scenario(scenario, &machine)?;
    let theorem_profile = scenario.resolve_theorem_profile_for(&resolved_execution);
    let rounds_to_run =
        rounds.unwrap_or_else(|| remaining_rounds_from_checkpoint(scenario, &machine));
    let coro_info: CoroInfo = machine
        .coroutines()
        .iter()
        .map(|coro| (coro.id, coro.role.clone()))
        .collect();
    execute_loaded_scenario_machine(
        scenario,
        handler,
        environment_models,
        SimulationMachine::Canonical(machine),
        &coro_info,
        &resolved_execution,
        theorem_profile,
        rounds_to_run,
        None,
    )
}

/// Resume a canonical simulator run from an exact checkpoint artifact emitted by a prior run.
///
/// This path restores both protocol-machine and middleware state, so adversary,
/// network, and reconfiguration behavior continues exactly from the checkpoint.
///
/// # Errors
///
/// Returns an error if the checkpoint cannot be decoded or the scenario is not
/// resumable under the canonical backend.
pub fn resume_with_checkpoint_artifact(
    scenario: &Scenario,
    checkpoint: &CheckpointArtifact,
    handler: &dyn EffectHandler,
    environment_models: Option<EnvironmentModels<'_>>,
    rounds: Option<u64>,
) -> Result<ScenarioResult, String> {
    if checkpoint.middleware_state.is_none() {
        return Err(
            "checkpoint artifact is missing exact middleware state required for semantics-preserving resume"
                .to_string(),
        );
    }
    let machine = checkpoint.decode_machine()?;
    let resolved_execution = scenario.resolved_execution()?;
    if resolved_execution.backend != ResolvedExecutionBackend::Canonical {
        return Err(
            "checkpoint replay currently requires the canonical simulator backend".to_string(),
        );
    }
    validate_checkpoint_machine_matches_scenario(scenario, &machine)?;
    let theorem_profile = scenario.resolve_theorem_profile_for(&resolved_execution);
    let rounds_to_run =
        rounds.unwrap_or_else(|| remaining_rounds_from_checkpoint(scenario, &machine));
    let coro_info: CoroInfo = machine
        .coroutines()
        .iter()
        .map(|coro| (coro.id, coro.role.clone()))
        .collect();
    execute_loaded_scenario_machine(
        scenario,
        handler,
        environment_models,
        SimulationMachine::Canonical(machine),
        &coro_info,
        &resolved_execution,
        theorem_profile,
        rounds_to_run,
        checkpoint.middleware_state.as_ref(),
    )
}

/// Run a choreography with scenario-defined middleware and optional environment hooks.
///
/// # Errors
///
/// Returns an error string if protocol-machine execution fails.
#[allow(clippy::too_many_lines)]
pub fn run_with_scenario_and_environment(
    local_types: &BTreeMap<String, LocalTypeR>,
    global_type: &GlobalType,
    initial_states: &BTreeMap<String, Vec<FixedQ32>>,
    scenario: &Scenario,
    handler: &dyn EffectHandler,
    environment_models: Option<EnvironmentModels<'_>>,
) -> Result<ScenarioResult, String> {
    let image = CodeImage::from_local_types(local_types, global_type);
    let resolved_execution = scenario.resolved_execution()?;
    let theorem_profile = scenario.resolve_theorem_profile_for(&resolved_execution);
    if matches!(
        resolved_execution.backend,
        ResolvedExecutionBackend::Threaded
    ) && scenario.checkpoint_interval.is_some()
    {
        return Err(
            "scenario checkpoints currently require the canonical simulator backend".to_string(),
        );
    }
    let machine_config = ProtocolMachineConfig {
        sched_policy: machine_scheduler_policy(resolved_execution.scheduler_policy),
        ..ProtocolMachineConfig::default()
    };
    let mut machine = SimulationMachine::new(machine_config, &resolved_execution);
    let sid = machine
        .load_choreography_owned(&image, "sim/scenario")
        .map_err(|e| format!("load error: {e}"))?;
    let sid = sid.session_id();

    let coros = machine.session_coroutines(sid);
    let coro_info: CoroInfo = coros.iter().map(|c| (c.id, c.role.clone())).collect();
    let resolved_initial_states = if initial_states.is_empty() {
        derive_initial_states(scenario)?
    } else {
        initial_states.clone()
    };
    init_coro_regs(&mut machine, &coro_info, &resolved_initial_states)?;
    execute_loaded_scenario_machine(
        scenario,
        handler,
        environment_models,
        machine,
        &coro_info,
        &resolved_execution,
        theorem_profile,
        scenario.steps.saturating_sub(1),
        None,
    )
}
