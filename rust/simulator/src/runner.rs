//! Protocol-machine-backed simulation runner.
//!
//! Wraps `telltale-machine` to execute choreographies through the protocol machine,
//! producing simulator traces plus canonical semantic artifacts.

use std::collections::BTreeMap;
use telltale_types::FixedQ32;

use crate::analysis::{compare_observability, NormalizedObservability, ObservabilityRelation};
use crate::backend::SimulationMachine;
use crate::fault::{
    AdversaryBudgetRecord, AdversarySummary, AssumptionDiagnostic, AssumptionFailureClass,
    ScheduledAdversary,
};
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
use crate::execution::{execute_scenario_rounds, ScenarioMiddleware};
use crate::harness::derive_initial_states;
use crate::property::{PropertyContext, PropertyMonitor, PropertyViolation};
use crate::reconfiguration::{ReconfigurationRecord, ReconfigurationSummary};
use crate::scenario::{
    ExecutionRegime, ResolvedExecutionBackend, ResolvedSchedulerPolicy, ResolvedTheoremProfile,
    Scenario,
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
pub struct ScenarioAnalysisArtifact {
    /// Envelope-normalized observability class derived from raw replay traces.
    pub normalized_observability: NormalizedObservability,
}

/// Replay-ready artifact data captured from a scenario run.
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
}

/// Structured statistics emitted by scenario execution.
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

fn critical_capacity_summary(
    local_types: &BTreeMap<String, LocalTypeR>,
    productive_step_count: u64,
    initial_depth_budget: u64,
) -> CriticalCapacitySummary {
    if local_types.values().any(contains_recursion) {
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
    local_types: &BTreeMap<String, LocalTypeR>,
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
            local_types,
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
    let initial_session_snapshots = machine.session_snapshots();

    let mut trace = Trace::new();
    let max_rounds = scenario.steps.saturating_sub(1);
    let steps_limit = usize::try_from(scenario.steps)
        .map_err(|_| format!("scenario.steps {} exceeds usize", scenario.steps))?;
    let concurrency = usize::try_from(resolved_execution.scheduler_concurrency).map_err(|_| {
        format!(
            "scenario.execution.scheduler_concurrency {} exceeds usize",
            resolved_execution.scheduler_concurrency
        )
    })?;
    let mut step_idx: usize = 0;
    let mut checkpoint_writes: usize = 0;

    if scenario.steps > 0 {
        record_all_roles(&machine, &coro_info, 0, &mut trace);
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

    let middleware =
        ScenarioMiddleware::from_scenario(scenario, handler, machine.clock().tick_duration)
            .map_err(|e| format!("middleware setup: {e}"))?;

    let execution = execute_scenario_rounds(
        &mut machine,
        scenario,
        &middleware,
        concurrency,
        max_rounds,
        |machine, _completed_rounds| {
            if step_idx >= steps_limit {
                return Ok(());
            }

            record_all_roles(machine, &coro_info, step_idx, &mut trace);
            step_idx += 1;

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
                    }
                }
                if let SimulationMachine::Canonical(inner) = machine {
                    store.maybe_checkpoint(inner.clock().tick, inner);
                }
            }
            Ok(())
        },
    )?;
    let rounds_executed = execution.rounds_executed;

    if trace.records.is_empty() {
        let fallback_step = steps_limit.saturating_sub(1);
        record_all_roles(&machine, &coro_info, fallback_step, &mut trace);
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
    let normalized_observability =
        crate::analysis::normalized_observability(&obs_trace, &reconfiguration_trace);
    let final_session_snapshots = machine.session_snapshots();
    let productive_step_count = productive_event_count(&obs_trace);
    let theorem_progress = theorem_progress_summary(
        local_types,
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
        },
    })
}
