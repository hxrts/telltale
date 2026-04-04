//! Deterministic parameter sweeps and proof-carrying experiment manifests.
#![allow(missing_docs)]

use serde::{Deserialize, Serialize};

use crate::decision::{
    decide_capacity_predicate, decide_theorem_eligibility, theorem_eligibility_from_result,
    DecisionReport,
};
use crate::harness::{BatchConfig, HarnessSpec, HostAdapter, SimulationHarness};
use crate::runner::{ScenarioResult, SchedulerProfileSummary};
use crate::scenario::{
    ExecutionRegime, ReconfigurationSpec, ResolvedTheoremProfile, TheoremSchedulerProfile,
};

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SweepConfig {
    pub batch: BatchConfig,
    pub axes: Vec<SweepAxis>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "axis", rename_all = "snake_case")]
pub enum SweepAxis {
    Seed {
        values: Vec<u64>,
    },
    CapacityBudget {
        values: Vec<u64>,
    },
    SchedulerProfile {
        values: Vec<TheoremSchedulerProfile>,
    },
    ReconfigurationProgram {
        values: Vec<Vec<ReconfigurationSpec>>,
    },
    AdversaryBudget {
        adversary_id: String,
        totals: Vec<u64>,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SweepBinding {
    pub axis: String,
    pub value: String,
}

pub struct SweepRunResult {
    pub parallelism: usize,
    pub manifest: SweepManifest,
    pub results: Vec<Result<ScenarioResult, String>>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SweepManifest {
    pub parallelism: usize,
    pub runs: Vec<SweepManifestEntry>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SweepManifestEntry {
    pub input_index: usize,
    pub scenario_name: String,
    pub bindings: Vec<SweepBinding>,
    pub execution_regime: Option<ExecutionRegime>,
    pub theorem_profile: Option<ResolvedTheoremProfile>,
    pub scheduler_profile: Option<SchedulerProfileSummary>,
    pub theorem_eligibility: DecisionReport,
    pub capacity_report: Option<DecisionReport>,
    pub result_error: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SweepDiffReport {
    pub differing_runs: Vec<SweepRunDiff>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SweepRunDiff {
    pub input_index: usize,
    pub theorem_eligibility_changed: bool,
    pub productive_step_delta: Option<i64>,
    pub assumption_diagnostics_changed: bool,
}

#[derive(Debug, Clone)]
struct SweepItem {
    spec: HarnessSpec,
    bindings: Vec<SweepBinding>,
    capacity_budget: Option<u64>,
}

#[must_use]
pub fn compare_sweep_results(left: &SweepRunResult, right: &SweepRunResult) -> SweepDiffReport {
    let max_len = left.manifest.runs.len().max(right.manifest.runs.len());
    let mut differing_runs = Vec::new();

    for idx in 0..max_len {
        let Some(left_entry) = left.manifest.runs.get(idx) else {
            differing_runs.push(SweepRunDiff {
                input_index: idx,
                theorem_eligibility_changed: true,
                productive_step_delta: None,
                assumption_diagnostics_changed: true,
            });
            continue;
        };
        let Some(right_entry) = right.manifest.runs.get(idx) else {
            differing_runs.push(SweepRunDiff {
                input_index: idx,
                theorem_eligibility_changed: true,
                productive_step_delta: None,
                assumption_diagnostics_changed: true,
            });
            continue;
        };

        let left_result = left.results.get(idx).and_then(|entry| entry.as_ref().ok());
        let right_result = right.results.get(idx).and_then(|entry| entry.as_ref().ok());
        let productive_step_delta = match (left_result, right_result) {
            (Some(lhs), Some(rhs)) => Some(
                i64::try_from(lhs.stats.theorem_progress.productive_step_count).unwrap_or(i64::MAX)
                    - i64::try_from(rhs.stats.theorem_progress.productive_step_count)
                        .unwrap_or(i64::MAX),
            ),
            _ => None,
        };

        let assumption_diagnostics_changed = match (left_result, right_result) {
            (Some(lhs), Some(rhs)) => {
                lhs.stats.assumption_diagnostics != rhs.stats.assumption_diagnostics
            }
            _ => left_result.is_some() != right_result.is_some(),
        };

        if left_entry.theorem_eligibility != right_entry.theorem_eligibility
            || productive_step_delta.unwrap_or(0) != 0
            || assumption_diagnostics_changed
        {
            differing_runs.push(SweepRunDiff {
                input_index: idx,
                theorem_eligibility_changed: left_entry.theorem_eligibility
                    != right_entry.theorem_eligibility,
                productive_step_delta,
                assumption_diagnostics_changed,
            });
        }
    }

    SweepDiffReport { differing_runs }
}

pub fn run_sweep<'a, A>(
    harness: &SimulationHarness<'a, A>,
    base: &HarnessSpec,
    config: &SweepConfig,
) -> Result<SweepRunResult, String>
where
    A: HostAdapter + Sync + ?Sized,
{
    let expanded = expand_sweep(base, &config.axes)?;
    let specs = expanded
        .iter()
        .map(|item| item.spec.clone())
        .collect::<Vec<_>>();
    let batch = harness.run_batch_with(&specs, config.batch);

    let manifest = SweepManifest {
        parallelism: batch.parallelism,
        runs: expanded
            .iter()
            .zip(batch.results.iter())
            .enumerate()
            .map(|(idx, (item, result))| {
                let theorem_eligibility = match result {
                    Ok(result) => theorem_eligibility_from_result(result),
                    Err(_) => decide_theorem_eligibility(&item.spec.scenario),
                };
                let capacity_report = item
                    .capacity_budget
                    .map(|budget| decide_capacity_predicate(&item.spec.local_types, budget));

                SweepManifestEntry {
                    input_index: idx,
                    scenario_name: item.spec.scenario.name.clone(),
                    bindings: item.bindings.clone(),
                    execution_regime: result
                        .as_ref()
                        .ok()
                        .map(|run| run.stats.execution_regime)
                        .or_else(|| {
                            item.spec
                                .scenario
                                .resolved_execution()
                                .ok()
                                .map(|execution| execution.regime())
                        }),
                    theorem_profile: result
                        .as_ref()
                        .ok()
                        .map(|run| run.stats.theorem_profile.clone()),
                    scheduler_profile: result
                        .as_ref()
                        .ok()
                        .map(|run| run.stats.scheduler_profile.clone()),
                    theorem_eligibility,
                    capacity_report,
                    result_error: result.as_ref().err().cloned(),
                }
            })
            .collect(),
    };

    Ok(SweepRunResult {
        parallelism: batch.parallelism,
        manifest,
        results: batch.results,
    })
}

fn expand_sweep(base: &HarnessSpec, axes: &[SweepAxis]) -> Result<Vec<SweepItem>, String> {
    let mut items = vec![SweepItem {
        spec: base.clone(),
        bindings: Vec::new(),
        capacity_budget: None,
    }];

    for axis in axes {
        let mut next = Vec::new();
        for item in items {
            for variant in expand_axis(&item, axis)? {
                next.push(variant);
            }
        }
        items = next;
    }

    Ok(items)
}

fn expand_axis(item: &SweepItem, axis: &SweepAxis) -> Result<Vec<SweepItem>, String> {
    match axis {
        SweepAxis::Seed { values } => Ok(values
            .iter()
            .map(|value| {
                let mut next = item.clone();
                next.spec.scenario.seed = *value;
                next.bindings.push(SweepBinding {
                    axis: "seed".to_string(),
                    value: value.to_string(),
                });
                next
            })
            .collect()),
        SweepAxis::CapacityBudget { values } => Ok(values
            .iter()
            .map(|value| {
                let mut next = item.clone();
                next.capacity_budget = Some(*value);
                next.bindings.push(SweepBinding {
                    axis: "capacity_budget".to_string(),
                    value: value.to_string(),
                });
                next
            })
            .collect()),
        SweepAxis::SchedulerProfile { values } => Ok(values
            .iter()
            .map(|value| {
                let mut next = item.clone();
                next.spec.scenario.theorem.scheduler_profile = *value;
                next.bindings.push(SweepBinding {
                    axis: "scheduler_profile".to_string(),
                    value: format!("{value:?}").to_lowercase(),
                });
                next
            })
            .collect()),
        SweepAxis::ReconfigurationProgram { values } => Ok(values
            .iter()
            .enumerate()
            .map(|(idx, value)| {
                let mut next = item.clone();
                next.spec.scenario.reconfigurations = value.clone();
                next.bindings.push(SweepBinding {
                    axis: "reconfiguration_program".to_string(),
                    value: idx.to_string(),
                });
                next
            })
            .collect()),
        SweepAxis::AdversaryBudget {
            adversary_id,
            totals,
        } => totals
            .iter()
            .map(|value| {
                let mut next = item.clone();
                let target = next
                    .spec
                    .scenario
                    .adversaries
                    .iter_mut()
                    .find(|adversary| adversary.id.as_deref() == Some(adversary_id.as_str()))
                    .ok_or_else(|| format!("missing adversary id '{adversary_id}' in base spec"))?;
                target.budget.total = *value;
                next.bindings.push(SweepBinding {
                    axis: format!("adversary_budget:{adversary_id}"),
                    value: value.to_string(),
                });
                Ok(next)
            })
            .collect(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;
    use telltale_machine::coroutine::Value;
    use telltale_machine::model::effects::{
        EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
    };
    use telltale_types::{FixedQ32, GlobalType, Label, LocalTypeR};

    use crate::harness::{DirectAdapter, HarnessSpec};

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

    fn harness_spec() -> HarnessSpec {
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );

        let scenario = crate::scenario::Scenario::parse(
            r#"
name = "sweep_fixture"
roles = ["A", "B"]
steps = 4

[field]
layer = "mean_field"

[field.params]
beta = "1.0"
species = ["up", "down"]
initial_state = ["0.5", "0.5"]
step_size = "0.01"

[[adversaries]]
id = "budgeted"
trigger = { immediate = true }
action = { type = "withholding" }
budget = { total = 1, mode = "activation" }
"#,
        )
        .expect("parse scenario");

        HarnessSpec::new(local_types, global, scenario).with_initial_states(BTreeMap::from([
            ("A".to_string(), Vec::<FixedQ32>::new()),
            ("B".to_string(), Vec::<FixedQ32>::new()),
        ]))
    }

    #[test]
    fn sweep_manifest_is_reproducible_and_ordered() {
        let adapter = DirectAdapter::new(&PassthroughHandler);
        let harness = SimulationHarness::new(&adapter);
        let spec = harness_spec();
        let config = SweepConfig {
            batch: BatchConfig {
                parallelism: Some(2),
            },
            axes: vec![
                SweepAxis::Seed { values: vec![1, 2] },
                SweepAxis::SchedulerProfile {
                    values: vec![
                        TheoremSchedulerProfile::CanonicalExact,
                        TheoremSchedulerProfile::ThreadedEnvelope,
                    ],
                },
            ],
        };

        let first = run_sweep(&harness, &spec, &config).expect("first sweep");
        let second = run_sweep(&harness, &spec, &config).expect("second sweep");

        assert_eq!(first.manifest, second.manifest);
        assert_eq!(first.manifest.runs.len(), 4);
        assert_eq!(first.manifest.runs[0].input_index, 0);
        assert_eq!(first.manifest.runs[3].input_index, 3);
        assert!(first
            .manifest
            .runs
            .iter()
            .all(|entry| entry.execution_regime.is_some()));
    }

    #[test]
    fn sweep_manifest_retains_capacity_and_eligibility_witnesses() {
        let adapter = DirectAdapter::new(&PassthroughHandler);
        let harness = SimulationHarness::new(&adapter);
        let spec = harness_spec();

        let result = run_sweep(
            &harness,
            &spec,
            &SweepConfig {
                batch: BatchConfig {
                    parallelism: Some(1),
                },
                axes: vec![
                    SweepAxis::CapacityBudget { values: vec![1, 2] },
                    SweepAxis::AdversaryBudget {
                        adversary_id: "budgeted".to_string(),
                        totals: vec![1],
                    },
                ],
            },
        )
        .expect("run sweep");

        assert_eq!(result.manifest.runs.len(), 2);
        assert!(result
            .manifest
            .runs
            .iter()
            .all(|entry| entry.capacity_report.is_some()));
        assert!(result.manifest.runs.iter().all(|entry| matches!(
            entry.theorem_eligibility.outcome,
            crate::decision::DecisionOutcome::Certified(_)
                | crate::decision::DecisionOutcome::Counterexample(_)
        )));
    }
}
