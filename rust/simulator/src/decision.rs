//! Structured theorem-facing decision procedures and counterexample surfaces.
#![allow(missing_docs)]

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use telltale_theory::coherence::check_coherent;
use telltale_theory::subtyping::{
    async_subtype, orphan_free, sync_subtype, AsyncSubtypeError, SyncSubtypeError,
};
use telltale_theory::well_formedness::{validate_global, ValidationError};
use telltale_types::{GlobalType, LocalTypeR};

use crate::runner::ScenarioResult;
use crate::scenario::{Scenario, TheoremEligibility};

/// Supported simulator-facing decision/checker families.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DecisionKind {
    /// Global-type well-formedness.
    GlobalWellFormedness,
    /// Global coherence bundle.
    GlobalCoherence,
    /// Conservative async-subtyping.
    AsyncSubtype,
    /// Structural sync-subtyping.
    SyncSubtype,
    /// Productive-step capacity predicate.
    CapacityPredicate,
    /// Theorem-profile eligibility against execution resolution.
    TheoremEligibility,
}

/// One structured decision report.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecisionReport {
    /// Decision family.
    pub kind: DecisionKind,
    /// Certificate or counterexample result.
    pub outcome: DecisionOutcome,
}

/// Structured decision outcome.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum DecisionOutcome {
    /// The checked predicate held and a certificate is available.
    Certified(DecisionCertificate),
    /// The checked predicate failed and a structured counterexample is available.
    Counterexample(DecisionCounterexample),
}

/// Positive witness/certificate for a decision procedure.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum DecisionCertificate {
    /// Global type is well-formed.
    GlobalWellFormed { roles: Vec<String> },
    /// Global type satisfies the implemented coherence bundle.
    GlobalCoherent { roles: Vec<String> },
    /// Async-subtyping holds.
    AsyncSubtype { orphan_free: bool },
    /// Sync-subtyping holds.
    SyncSubtype,
    /// Capacity request is admissible.
    CapacityPredicate {
        threshold: u64,
        requested_productive_steps: u64,
    },
    /// Theorem profile is admissible.
    TheoremEligibility {
        eligibility: TheoremEligibility,
    },
}

/// Structured negative witness/counterexample for a decision procedure.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum DecisionCounterexample {
    /// One or more global well-formedness violations.
    GlobalWellFormed {
        violations: Vec<WellFormednessViolation>,
    },
    /// One or more coherence predicates failed.
    GlobalCoherence {
        failed_predicates: Vec<CoherenceFailure>,
    },
    /// Conservative async-subtyping failed.
    AsyncSubtype { cause: AsyncSubtypeWitness },
    /// Structural sync-subtyping failed.
    SyncSubtype { cause: SyncSubtypeWitness },
    /// Capacity predicate failed or is unsupported.
    CapacityPredicate { cause: CapacityCounterexample },
    /// Theorem profile did not admit theorem-backed output.
    TheoremEligibility {
        cause: TheoremEligibilityCounterexample,
    },
}

/// Structured well-formedness violation family.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum WellFormednessViolation {
    UnboundVariable { name: String },
    EmptyBranches,
    SelfCommunication { role: String },
    UnguardedRecursion,
    DuplicateLabel { label: String },
}

/// Individual coherence predicates that can fail.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum CoherenceFailure {
    Size,
    Action,
    UniqueLabels,
    Projectable,
    Good,
}

/// Structured async-subtyping counterexample.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum AsyncSubtypeWitness {
    NotSisoDecomposable,
    InputTreeMismatch,
    OutputTreeMismatch,
    PhaseMismatch { sub_segments: u64, super_segments: u64 },
    UnfoldLimitExceeded,
}

/// Structured sync-subtyping counterexample.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum SyncSubtypeWitness {
    PartnerMismatch { expected: String, found: String },
    DirectionMismatch { expected: String, found: String },
    MissingLabel { label: String },
    ExtraLabel { label: String },
    ContinuationMismatch { label: String },
    LabelSortMismatch {
        label: String,
        expected: String,
        found: String,
    },
    PayloadAnnotationMismatch {
        label: String,
        expected: String,
        found: String,
    },
    VariableMismatch { expected: String, found: String },
    IncompatibleTypes {
        sub_type: String,
        super_type: String,
    },
}

/// Structured capacity counterexample.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum CapacityCounterexample {
    ThresholdExceeded {
        threshold: u64,
        requested_productive_steps: u64,
    },
    RecursiveCapacityUnsupported,
}

/// Structured theorem-eligibility counterexample.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case")]
pub enum TheoremEligibilityCounterexample {
    ExecutionResolution { reason: String },
    Ineligible { reason: String },
}

impl DecisionReport {
    fn certified(kind: DecisionKind, certificate: DecisionCertificate) -> Self {
        Self {
            kind,
            outcome: DecisionOutcome::Certified(certificate),
        }
    }

    fn counterexample(kind: DecisionKind, counterexample: DecisionCounterexample) -> Self {
        Self {
            kind,
            outcome: DecisionOutcome::Counterexample(counterexample),
        }
    }
}

/// Decide global well-formedness with a structured witness.
#[must_use]
pub fn decide_global_well_formedness(global: &GlobalType) -> DecisionReport {
    match validate_global(global) {
        Ok(()) => DecisionReport::certified(
            DecisionKind::GlobalWellFormedness,
            DecisionCertificate::GlobalWellFormed {
                roles: global.roles().into_iter().collect(),
            },
        ),
        Err(error) => DecisionReport::counterexample(
            DecisionKind::GlobalWellFormedness,
            DecisionCounterexample::GlobalWellFormed {
                violations: flatten_validation_error(&error),
            },
        ),
    }
}

/// Decide global coherence with a structured witness.
#[must_use]
pub fn decide_global_coherence(global: &GlobalType) -> DecisionReport {
    let bundle = check_coherent(global);
    let mut failed = Vec::new();
    if !bundle.size {
        failed.push(CoherenceFailure::Size);
    }
    if !bundle.action {
        failed.push(CoherenceFailure::Action);
    }
    if !bundle.uniq_labels {
        failed.push(CoherenceFailure::UniqueLabels);
    }
    if !bundle.projectable {
        failed.push(CoherenceFailure::Projectable);
    }
    if !bundle.good {
        failed.push(CoherenceFailure::Good);
    }

    if failed.is_empty() {
        DecisionReport::certified(
            DecisionKind::GlobalCoherence,
            DecisionCertificate::GlobalCoherent {
                roles: global.roles().into_iter().collect(),
            },
        )
    } else {
        DecisionReport::counterexample(
            DecisionKind::GlobalCoherence,
            DecisionCounterexample::GlobalCoherence {
                failed_predicates: failed,
            },
        )
    }
}

/// Decide conservative async-subtyping with a structured witness.
#[must_use]
pub fn decide_async_subtyping(sub: &LocalTypeR, sup: &LocalTypeR) -> DecisionReport {
    match async_subtype(sub, sup) {
        Ok(()) => DecisionReport::certified(
            DecisionKind::AsyncSubtype,
            DecisionCertificate::AsyncSubtype {
                orphan_free: orphan_free(sub),
            },
        ),
        Err(error) => DecisionReport::counterexample(
            DecisionKind::AsyncSubtype,
            DecisionCounterexample::AsyncSubtype {
                cause: map_async_error(&error),
            },
        ),
    }
}

/// Decide structural sync-subtyping with a structured witness.
#[must_use]
pub fn decide_sync_subtyping(sub: &LocalTypeR, sup: &LocalTypeR) -> DecisionReport {
    match sync_subtype(sub, sup) {
        Ok(()) => DecisionReport::certified(
            DecisionKind::SyncSubtype,
            DecisionCertificate::SyncSubtype,
        ),
        Err(error) => DecisionReport::counterexample(
            DecisionKind::SyncSubtype,
            DecisionCounterexample::SyncSubtype {
                cause: map_sync_error(&error),
            },
        ),
    }
}

/// Decide a productive-step capacity predicate against recursion-free local types.
#[must_use]
pub fn decide_capacity_predicate(
    local_types: &BTreeMap<String, LocalTypeR>,
    requested_productive_steps: u64,
) -> DecisionReport {
    if local_types.values().any(contains_recursion) {
        return DecisionReport::counterexample(
            DecisionKind::CapacityPredicate,
            DecisionCounterexample::CapacityPredicate {
                cause: CapacityCounterexample::RecursiveCapacityUnsupported,
            },
        );
    }

    let threshold = local_types
        .values()
        .map(|local| u64::try_from(type_depth(local)).unwrap_or(u64::MAX))
        .fold(0u64, u64::saturating_add);

    if requested_productive_steps <= threshold {
        DecisionReport::certified(
            DecisionKind::CapacityPredicate,
            DecisionCertificate::CapacityPredicate {
                threshold,
                requested_productive_steps,
            },
        )
    } else {
        DecisionReport::counterexample(
            DecisionKind::CapacityPredicate,
            DecisionCounterexample::CapacityPredicate {
                cause: CapacityCounterexample::ThresholdExceeded {
                    threshold,
                    requested_productive_steps,
                },
            },
        )
    }
}

/// Decide theorem-profile eligibility without executing the simulator.
#[must_use]
pub fn decide_theorem_eligibility(scenario: &Scenario) -> DecisionReport {
    let resolved_execution = match scenario.resolved_execution() {
        Ok(execution) => execution,
        Err(reason) => {
            return DecisionReport::counterexample(
                DecisionKind::TheoremEligibility,
                DecisionCounterexample::TheoremEligibility {
                    cause: TheoremEligibilityCounterexample::ExecutionResolution { reason },
                },
            );
        }
    };
    let profile = scenario.resolve_theorem_profile_for(&resolved_execution);
    theorem_eligibility_report(profile.eligibility, profile.eligibility_reason)
}

/// Convert a runtime result into the same theorem-eligibility witness format.
#[must_use]
pub fn theorem_eligibility_from_result(result: &ScenarioResult) -> DecisionReport {
    theorem_eligibility_report(
        result.stats.theorem_profile.eligibility,
        result.stats.theorem_profile.eligibility_reason.clone(),
    )
}

fn theorem_eligibility_report(
    eligibility: TheoremEligibility,
    reason: Option<String>,
) -> DecisionReport {
    match eligibility {
        TheoremEligibility::Exact | TheoremEligibility::EnvelopeBounded => {
            DecisionReport::certified(
                DecisionKind::TheoremEligibility,
                DecisionCertificate::TheoremEligibility { eligibility },
            )
        }
        TheoremEligibility::Ineligible => DecisionReport::counterexample(
            DecisionKind::TheoremEligibility,
            DecisionCounterexample::TheoremEligibility {
                cause: TheoremEligibilityCounterexample::Ineligible {
                    reason: reason.unwrap_or_else(|| {
                        "theorem profile was ineligible without an explicit reason".to_string()
                    }),
                },
            },
        ),
    }
}

fn flatten_validation_error(error: &ValidationError) -> Vec<WellFormednessViolation> {
    match error {
        ValidationError::UnboundVariable(name) => {
            vec![WellFormednessViolation::UnboundVariable { name: name.clone() }]
        }
        ValidationError::EmptyBranches => vec![WellFormednessViolation::EmptyBranches],
        ValidationError::SelfCommunication(role) => {
            vec![WellFormednessViolation::SelfCommunication { role: role.clone() }]
        }
        ValidationError::UnguardedRecursion => vec![WellFormednessViolation::UnguardedRecursion],
        ValidationError::DuplicateLabel(label) => {
            vec![WellFormednessViolation::DuplicateLabel {
                label: label.clone(),
            }]
        }
        ValidationError::Multiple(errors) => errors.iter().flat_map(flatten_validation_error).collect(),
    }
}

fn map_async_error(error: &AsyncSubtypeError) -> AsyncSubtypeWitness {
    match error {
        AsyncSubtypeError::NotSisoDecomposable => AsyncSubtypeWitness::NotSisoDecomposable,
        AsyncSubtypeError::InputTreeMismatch => AsyncSubtypeWitness::InputTreeMismatch,
        AsyncSubtypeError::OutputTreeMismatch => AsyncSubtypeWitness::OutputTreeMismatch,
        AsyncSubtypeError::PhaseMismatch { sub, sup } => AsyncSubtypeWitness::PhaseMismatch {
            sub_segments: u64::try_from(*sub).unwrap_or(u64::MAX),
            super_segments: u64::try_from(*sup).unwrap_or(u64::MAX),
        },
        AsyncSubtypeError::UnfoldLimitExceeded => AsyncSubtypeWitness::UnfoldLimitExceeded,
    }
}

fn map_sync_error(error: &SyncSubtypeError) -> SyncSubtypeWitness {
    match error {
        SyncSubtypeError::PartnerMismatch { expected, found } => {
            SyncSubtypeWitness::PartnerMismatch {
                expected: expected.clone(),
                found: found.clone(),
            }
        }
        SyncSubtypeError::DirectionMismatch { expected, found } => {
            SyncSubtypeWitness::DirectionMismatch {
                expected: expected.clone(),
                found: found.clone(),
            }
        }
        SyncSubtypeError::MissingLabel { label } => SyncSubtypeWitness::MissingLabel {
            label: label.clone(),
        },
        SyncSubtypeError::ExtraLabel { label } => SyncSubtypeWitness::ExtraLabel {
            label: label.clone(),
        },
        SyncSubtypeError::ContinuationMismatch { label } => {
            SyncSubtypeWitness::ContinuationMismatch {
                label: label.clone(),
            }
        }
        SyncSubtypeError::LabelSortMismatch {
            label,
            expected,
            found,
        } => SyncSubtypeWitness::LabelSortMismatch {
            label: label.clone(),
            expected: expected.clone(),
            found: found.clone(),
        },
        SyncSubtypeError::PayloadAnnotationMismatch {
            label,
            expected,
            found,
        } => SyncSubtypeWitness::PayloadAnnotationMismatch {
            label: label.clone(),
            expected: expected.clone(),
            found: found.clone(),
        },
        SyncSubtypeError::VariableMismatch { expected, found } => {
            SyncSubtypeWitness::VariableMismatch {
                expected: expected.clone(),
                found: found.clone(),
            }
        }
        SyncSubtypeError::IncompatibleTypes {
            sub_type,
            super_type,
        } => SyncSubtypeWitness::IncompatibleTypes {
            sub_type: sub_type.clone(),
            super_type: super_type.clone(),
        },
    }
}

fn contains_recursion(local: &LocalTypeR) -> bool {
    match local {
        LocalTypeR::Mu { body, .. } => contains_recursion(body),
        LocalTypeR::Var(_) => true,
        LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
            branches.iter().any(|(_, _, cont)| contains_recursion(cont))
        }
        LocalTypeR::End => false,
    }
}

fn type_depth(local: &LocalTypeR) -> usize {
    match local {
        LocalTypeR::End | LocalTypeR::Var(_) => 0,
        LocalTypeR::Mu { body, .. } => type_depth(body),
        LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
            1 + branches
                .iter()
                .map(|(_, _, cont)| type_depth(cont))
                .max()
                .unwrap_or(0)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use telltale_types::Label;

    fn good_global() -> GlobalType {
        GlobalType::send("A", "B", Label::new("msg"), GlobalType::End)
    }

    #[test]
    fn coherence_decision_emits_certificate_for_simple_protocol() {
        let report = decide_global_coherence(&good_global());
        assert_eq!(report.kind, DecisionKind::GlobalCoherence);
        assert!(matches!(
            report.outcome,
            DecisionOutcome::Certified(DecisionCertificate::GlobalCoherent { .. })
        ));
    }

    #[test]
    fn well_formedness_counterexample_is_structured_not_string_only() {
        let invalid = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("dup"), GlobalType::End),
                (Label::new("dup"), GlobalType::End),
            ],
        );
        let report = decide_global_well_formedness(&invalid);
        assert_eq!(report.kind, DecisionKind::GlobalWellFormedness);
        assert_eq!(
            report.outcome,
            DecisionOutcome::Counterexample(DecisionCounterexample::GlobalWellFormed {
                violations: vec![WellFormednessViolation::DuplicateLabel {
                    label: "dup".to_string()
                }]
            })
        );
    }

    #[test]
    fn theorem_eligibility_decision_aligns_with_runtime_result() {
        use std::collections::BTreeMap;
        use telltale_machine::coroutine::Value;
        use telltale_machine::model::effects::{
            EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
        };
        use telltale_types::GlobalType;

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
                    None => {
                        EffectResult::failure(EffectFailure::invalid_input("no labels available"))
                    }
                }
            }

            fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
                EffectResult::success(())
            }
        }

        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let local_types = BTreeMap::from([
            (
                "A".to_string(),
                LocalTypeR::Send {
                    partner: "B".into(),
                    branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
                },
            ),
            (
                "B".to_string(),
                LocalTypeR::Recv {
                    partner: "A".into(),
                    branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
                },
            ),
        ]);
        let scenario = Scenario::parse(
            r#"
name = "decision_alignment"
roles = ["A", "B"]
steps = 4

[execution]
backend = "canonical"
scheduler_concurrency = 1
worker_threads = 1

[theorem]
scheduler_profile = "canonical_exact"
envelope_profile = "exact"
assumption_bundle = "fault_free_transport"

[[reconfigurations]]
trigger = { at_tick = 1 }
action = { type = "handoff", handoff_id = "handoff#1", from_role = "A", to_role = "B" }
"#,
        )
        .expect("parse scenario");

        let offline = decide_theorem_eligibility(&scenario);
        let runtime = theorem_eligibility_from_result(
            &crate::runner::run_with_scenario(
                &local_types,
                &global,
                &BTreeMap::from([("A".to_string(), Vec::new()), ("B".to_string(), Vec::new())]),
                &scenario,
                &PassthroughHandler,
            )
            .expect("run scenario"),
        );

        assert_eq!(offline, runtime);
        assert!(matches!(
            offline.outcome,
            DecisionOutcome::Counterexample(DecisionCounterexample::TheoremEligibility {
                cause: TheoremEligibilityCounterexample::Ineligible { .. }
            })
        ));
    }
}
