//! Explicit approximation artifacts and comparison helpers.
#![allow(missing_docs)]

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use telltale_machine::model::effects::EffectHandler;
use telltale_types::{FixedQ32, GlobalType, LocalTypeR};

use crate::analysis::NormalizedObservability;
use crate::field::FieldSpec;
use crate::runner::{run_with_scenario, ScenarioResult, SchedulerProfileSummary};
use crate::scenario::{ExecutionRegime, ResolvedTheoremProfile, Scenario, TheoremEligibility};
use crate::trace::Trace;

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ApproximationFamily {
    BatchedStochastic,
    MeanField,
    ContinuumField,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ApproximationScope {
    EmpiricalOnly,
    StochasticEnvelope,
    MeanFieldLimit,
    ContinuumLimit,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ApproximationSpec {
    pub family: ApproximationFamily,
    pub scope: ApproximationScope,
    pub non_goals: Vec<String>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ApproximationAdmissibility {
    TheoremBacked,
    EmpiricalOnly,
    Unsupported,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ApproximationManifest {
    pub scenario_name: String,
    pub execution_regime: ExecutionRegime,
    pub family: ApproximationFamily,
    pub scope: ApproximationScope,
    pub non_goals: Vec<String>,
    pub theorem_profile: ResolvedTheoremProfile,
    pub scheduler_profile: SchedulerProfileSummary,
    pub admissibility: ApproximationAdmissibility,
    pub admissibility_reason: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ApproximationObservables {
    pub final_states: BTreeMap<String, Vec<FixedQ32>>,
    pub productive_step_count: u64,
    pub rounds_executed: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ApproximationArtifact {
    pub manifest: ApproximationManifest,
    pub trace: Trace,
    pub normalized_observability: NormalizedObservability,
    pub observables: ApproximationObservables,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct ApproximationComparison {
    pub exact_scenario_name: String,
    pub approximation_manifest: ApproximationManifest,
    pub normalized_equivalence: bool,
    pub per_role_final_l1_error: BTreeMap<String, FixedQ32>,
    pub productive_step_delta: i64,
}

pub fn run_approximation(
    local_types: &BTreeMap<String, LocalTypeR>,
    global_type: &GlobalType,
    initial_states: &BTreeMap<String, Vec<FixedQ32>>,
    scenario: &Scenario,
    handler: &dyn EffectHandler,
    approximation: &ApproximationSpec,
) -> Result<ApproximationArtifact, String> {
    let exact = run_with_scenario(local_types, global_type, initial_states, scenario, handler)?;
    let (admissibility, admissibility_reason) =
        approximation_admissibility(approximation, scenario, &exact.stats.theorem_profile);
    let final_states = final_states_from_trace(&exact);
    Ok(ApproximationArtifact {
        manifest: ApproximationManifest {
            scenario_name: scenario.name.clone(),
            execution_regime: exact.stats.execution_regime,
            family: approximation.family,
            scope: approximation.scope,
            non_goals: approximation.non_goals.clone(),
            theorem_profile: exact.stats.theorem_profile.clone(),
            scheduler_profile: exact.stats.scheduler_profile.clone(),
            admissibility,
            admissibility_reason,
        },
        trace: exact.trace,
        normalized_observability: exact.analysis.normalized_observability,
        observables: ApproximationObservables {
            final_states,
            productive_step_count: exact.stats.theorem_progress.productive_step_count,
            rounds_executed: exact.stats.rounds_executed,
        },
    })
}

#[must_use]
pub fn compare_exact_and_approximate(
    exact: &ScenarioResult,
    approximation: &ApproximationArtifact,
) -> ApproximationComparison {
    let exact_final = final_states_from_trace(exact);
    let approx_final = &approximation.observables.final_states;

    let mut errors = BTreeMap::new();
    for role in exact_final.keys().chain(approx_final.keys()) {
        let exact_state = exact_final.get(role).cloned().unwrap_or_default();
        let approx_state = approx_final.get(role).cloned().unwrap_or_default();
        errors.insert(role.clone(), l1_error(&exact_state, &approx_state));
    }

    ApproximationComparison {
        exact_scenario_name: "exact_protocol_machine".to_string(),
        approximation_manifest: approximation.manifest.clone(),
        normalized_equivalence: exact
            .analysis
            .normalized_observability
            .normalized_event_class
            == approximation
                .normalized_observability
                .normalized_event_class
            && exact
                .analysis
                .normalized_observability
                .normalized_reconfiguration_class
                == approximation
                    .normalized_observability
                    .normalized_reconfiguration_class,
        per_role_final_l1_error: errors,
        productive_step_delta: i64::try_from(exact.stats.theorem_progress.productive_step_count)
            .unwrap_or(i64::MAX)
            - i64::try_from(approximation.observables.productive_step_count).unwrap_or(i64::MAX),
    }
}

fn approximation_admissibility(
    approximation: &ApproximationSpec,
    scenario: &Scenario,
    theorem_profile: &ResolvedTheoremProfile,
) -> (ApproximationAdmissibility, Option<String>) {
    if !scope_matches_family(approximation.family, approximation.scope) {
        return (
            ApproximationAdmissibility::Unsupported,
            Some("approximation scope does not match the selected family".to_string()),
        );
    }

    let family_supported = match (approximation.family, scenario.field.as_ref()) {
        (ApproximationFamily::BatchedStochastic, _) => true,
        (ApproximationFamily::MeanField, Some(FieldSpec::MeanField(_))) => true,
        (ApproximationFamily::ContinuumField, Some(FieldSpec::ContinuumField(_))) => true,
        (ApproximationFamily::MeanField, _) => false,
        (ApproximationFamily::ContinuumField, _) => false,
    };

    if !family_supported {
        return (
            ApproximationAdmissibility::Unsupported,
            Some(
                "scenario field layer does not match the selected approximation family".to_string(),
            ),
        );
    }

    if approximation.scope == ApproximationScope::EmpiricalOnly {
        return (ApproximationAdmissibility::EmpiricalOnly, None);
    }

    if theorem_profile.eligibility == TheoremEligibility::Ineligible {
        return (
            ApproximationAdmissibility::Unsupported,
            Some("theorem profile is ineligible for the selected approximation scope".to_string()),
        );
    }

    (ApproximationAdmissibility::TheoremBacked, None)
}

fn scope_matches_family(family: ApproximationFamily, scope: ApproximationScope) -> bool {
    matches!(
        (family, scope),
        (_, ApproximationScope::EmpiricalOnly)
            | (
                ApproximationFamily::BatchedStochastic,
                ApproximationScope::StochasticEnvelope
            )
            | (
                ApproximationFamily::MeanField,
                ApproximationScope::MeanFieldLimit
            )
            | (
                ApproximationFamily::ContinuumField,
                ApproximationScope::ContinuumLimit
            )
    )
}

fn final_states_from_trace(result: &ScenarioResult) -> BTreeMap<String, Vec<FixedQ32>> {
    let mut states = BTreeMap::new();
    for record in &result.trace.records {
        states.insert(record.role.clone(), record.state.clone());
    }
    states
}

fn l1_error(left: &[FixedQ32], right: &[FixedQ32]) -> FixedQ32 {
    let max_len = left.len().max(right.len());
    let mut total = FixedQ32::zero();
    for idx in 0..max_len {
        let lhs = left.get(idx).copied().unwrap_or_else(FixedQ32::zero);
        let rhs = right.get(idx).copied().unwrap_or_else(FixedQ32::zero);
        total += (lhs - rhs).abs();
    }
    total
}

#[cfg(test)]
mod tests {
    use super::*;
    use telltale_machine::coroutine::Value;
    use telltale_machine::model::effects::{
        EffectFailure, EffectResult, SendDecision, SendDecisionInput,
    };

    #[derive(Debug, Clone, Copy)]
    struct PassthroughHandler;

    impl EffectHandler for PassthroughHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            label: &str,
            _state: &[Value],
        ) -> EffectResult<Value> {
            EffectResult::success(Value::Str(label.to_string()))
        }

        fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
            EffectResult::success(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)))
        }

        fn handle_recv(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &mut Vec<Value>,
            _payload: &Value,
        ) -> EffectResult<()> {
            EffectResult::success(())
        }

        fn handle_choose(
            &self,
            _role: &str,
            _partner: &str,
            labels: &[String],
            _state: &[Value],
        ) -> EffectResult<String> {
            match labels.first().cloned() {
                Some(label) => EffectResult::success(label),
                None => EffectResult::failure(EffectFailure::invalid_input("no labels available")),
            }
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
            EffectResult::success(())
        }
    }

    fn finite_protocol() -> (GlobalType, BTreeMap<String, LocalTypeR>) {
        let global = GlobalType::send("A", "B", telltale_types::Label::new("msg"), GlobalType::End);

        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(telltale_types::Label::new("msg"), None, LocalTypeR::End)],
            },
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(telltale_types::Label::new("msg"), None, LocalTypeR::End)],
            },
        );

        (global, local_types)
    }

    fn mean_field_scenario() -> Scenario {
        Scenario::parse(
            r#"
name = "approximation_fixture"
roles = ["A", "B"]
steps = 4

[field]
layer = "mean_field"

[field.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"
"#,
        )
        .expect("parse mean-field scenario")
    }

    #[test]
    fn approximation_runs_are_deterministic_and_emit_manifest() {
        let (global, local_types) = finite_protocol();
        let scenario = mean_field_scenario();
        let spec = ApproximationSpec {
            family: ApproximationFamily::MeanField,
            scope: ApproximationScope::MeanFieldLimit,
            non_goals: vec!["not_authoritative_replay".to_string()],
        };

        let first = run_approximation(
            &local_types,
            &global,
            &BTreeMap::new(),
            &scenario,
            &PassthroughHandler,
            &spec,
        )
        .expect("first approximation run");
        let second = run_approximation(
            &local_types,
            &global,
            &BTreeMap::new(),
            &scenario,
            &PassthroughHandler,
            &spec,
        )
        .expect("second approximation run");

        assert_eq!(first.manifest, second.manifest);
        assert_eq!(first.trace.records, second.trace.records);
        assert_eq!(
            first.manifest.execution_regime,
            ExecutionRegime::CanonicalExact
        );
        assert_eq!(
            first.manifest.admissibility,
            ApproximationAdmissibility::TheoremBacked
        );
    }

    #[test]
    fn exact_and_approximate_comparison_reports_shared_observables() {
        let (global, local_types) = finite_protocol();
        let scenario = mean_field_scenario();
        let exact = run_with_scenario(
            &local_types,
            &global,
            &BTreeMap::new(),
            &scenario,
            &PassthroughHandler,
        )
        .expect("exact run");
        let approximation = run_approximation(
            &local_types,
            &global,
            &BTreeMap::new(),
            &scenario,
            &PassthroughHandler,
            &ApproximationSpec {
                family: ApproximationFamily::MeanField,
                scope: ApproximationScope::MeanFieldLimit,
                non_goals: vec!["not_authoritative_replay".to_string()],
            },
        )
        .expect("approximation run");

        let comparison = compare_exact_and_approximate(&exact, &approximation);
        assert!(comparison.normalized_equivalence);
        assert!(comparison
            .per_role_final_l1_error
            .values()
            .all(|error| *error == FixedQ32::zero()));
    }

    #[test]
    fn approximation_admissibility_fails_closed_for_mismatched_or_empirical_regimes() {
        let scenario = mean_field_scenario();
        let theorem_profile = scenario
            .resolved_theorem_profile()
            .expect("resolve theorem profile");

        let mismatch = approximation_admissibility(
            &ApproximationSpec {
                family: ApproximationFamily::ContinuumField,
                scope: ApproximationScope::ContinuumLimit,
                non_goals: Vec::new(),
            },
            &scenario,
            &theorem_profile,
        );
        assert_eq!(
            mismatch,
            (
                ApproximationAdmissibility::Unsupported,
                Some(
                    "scenario field layer does not match the selected approximation family"
                        .to_string()
                ),
            )
        );

        let empirical = approximation_admissibility(
            &ApproximationSpec {
                family: ApproximationFamily::MeanField,
                scope: ApproximationScope::EmpiricalOnly,
                non_goals: Vec::new(),
            },
            &scenario,
            &theorem_profile,
        );
        assert_eq!(empirical, (ApproximationAdmissibility::EmpiricalOnly, None));

        let ineligible_scenario = Scenario::parse(
            r#"
name = "approximation_ineligible"
roles = ["A", "B"]
steps = 4

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[theorem]
assumption_bundle = "fault_free_transport"

[network]
base_latency_ms = 1
latency_variance = "0.0"
loss_probability = "0.0"

[field]
layer = "mean_field"

[field.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"
"#,
        )
        .expect("parse approximation-ineligible scenario");
        let ineligible_profile = ineligible_scenario
            .resolved_theorem_profile()
            .expect("resolve ineligible theorem profile");
        let ineligible = approximation_admissibility(
            &ApproximationSpec {
                family: ApproximationFamily::MeanField,
                scope: ApproximationScope::MeanFieldLimit,
                non_goals: Vec::new(),
            },
            &ineligible_scenario,
            &ineligible_profile,
        );
        assert_eq!(
            ineligible,
            (
                ApproximationAdmissibility::Unsupported,
                Some(
                    "theorem profile is ineligible for the selected approximation scope"
                        .to_string()
                ),
            )
        );
    }
}
