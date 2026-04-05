//! Scenario and property presets for integration tests.

use telltale_types::FixedQ32;

use crate::field::FieldSpec;
use crate::property::Property;
use crate::scenario::{
    AdversaryActionSpec, AdversaryBudgetModeSpec, AdversaryBudgetSpec, AdversarySpec,
    DurabilitySpec, ExecutionSpec, LivenessSpec, PropertiesSpec, Scenario, TheoremProfileSpec,
    TriggerSpec,
};

/// Build a deterministic baseline scenario with no network or adversary declarations.
#[must_use]
pub fn deterministic_baseline(
    name: impl Into<String>,
    roles: Vec<String>,
    steps: u64,
    field: FieldSpec,
) -> Scenario {
    Scenario {
        name: name.into(),
        roles,
        steps,
        execution: ExecutionSpec::default(),
        seed: 0,
        network: None,
        field: Some(field),
        reconfigurations: Vec::new(),
        adversaries: Vec::new(),
        properties: None,
        checkpoint_interval: None,
        theorem: TheoremProfileSpec::default(),
        durability: DurabilitySpec::default(),
        extensions: Default::default(),
    }
}

/// Build a default property set for one session id.
#[must_use]
pub fn standard_properties(
    session_id: usize,
    buffer_bound: usize,
    liveness_bound: u64,
) -> PropertiesSpec {
    PropertiesSpec {
        invariants: vec![
            "no_faults".to_string(),
            "simplex".to_string(),
            format!("buffer_bound({session_id},{buffer_bound})"),
            format!("send_recv_liveness({session_id},{liveness_bound})"),
        ],
        liveness: vec![LivenessSpec {
            name: "eventual_activity".to_string(),
            precondition: "tick >= 1".to_string(),
            goal: "tick > 1".to_string(),
            bound: liveness_bound,
        }],
    }
}

/// Attach standard properties to a scenario.
#[must_use]
pub fn with_standard_properties(
    mut scenario: Scenario,
    session_id: usize,
    buffer_bound: usize,
    liveness_bound: u64,
) -> Scenario {
    scenario.properties = Some(standard_properties(
        session_id,
        buffer_bound,
        liveness_bound,
    ));
    scenario
}

/// Add a withholding adversary starting at a specific tick.
#[must_use]
pub fn with_withholding_adversary(
    mut scenario: Scenario,
    at_tick: u64,
    probability: FixedQ32,
) -> Scenario {
    scenario.adversaries.push(AdversarySpec {
        id: None,
        trigger: TriggerSpec {
            immediate: false,
            at_tick: Some(at_tick),
            after_step: None,
            random: None,
            on_event: None,
        },
        action: AdversaryActionSpec::Withholding,
        budget: AdversaryBudgetSpec {
            total: u64::MAX,
            assumption_failure: None,
            mode: AdversaryBudgetModeSpec::Independent { probability },
        },
    });
    scenario
}

/// Convert a `Property` value to the matching invariant string form.
#[must_use]
pub fn property_to_invariant(property: &Property) -> String {
    match property {
        Property::NoFaults => "no_faults".to_string(),
        Property::Simplex => "simplex".to_string(),
        Property::SendRecvLiveness { sid, bound } => {
            format!("send_recv_liveness({sid},{bound})")
        }
        Property::TypeMonotonicity { sid } => format!("type_monotonicity({sid})"),
        Property::BufferBound { sid, max } => format!("buffer_bound({sid},{max})"),
        Property::Liveness { name, .. } => name.clone(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::field::MeanFieldSpec;

    fn field() -> FieldSpec {
        FieldSpec::MeanField(MeanFieldSpec {
            beta: FixedQ32::one(),
            species: vec!["up".into(), "down".into()],
            initial_state: vec![FixedQ32::half(), FixedQ32::half()],
            step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
        })
    }

    #[test]
    fn baseline_has_expected_defaults() {
        let scenario =
            deterministic_baseline("baseline", vec!["A".into(), "B".into()], 16, field());
        assert_eq!(scenario.seed, 0);
        let execution = scenario.resolved_execution().expect("resolve execution");
        assert!(execution.scheduler_concurrency >= 1);
        assert!(scenario.adversaries.is_empty());
        assert!(scenario.properties.is_none());
    }

    #[test]
    fn standard_properties_emit_expected_invariants() {
        let props = standard_properties(0, 32, 12);
        assert!(props.invariants.iter().any(|item| item == "no_faults"));
        assert!(props
            .invariants
            .iter()
            .any(|item| item == "buffer_bound(0,32)"));
    }

    #[test]
    fn withholding_adversary_is_added() {
        let scenario =
            deterministic_baseline("baseline", vec!["A".into(), "B".into()], 16, field());
        let updated =
            with_withholding_adversary(scenario, 5, FixedQ32::from_ratio(1, 4).expect("0.25"));
        assert_eq!(updated.adversaries.len(), 1);
        assert!(matches!(
            updated.adversaries[0].action,
            AdversaryActionSpec::Withholding
        ));
        match updated.adversaries[0].budget.mode {
            AdversaryBudgetModeSpec::Independent { probability } => {
                assert_eq!(probability, FixedQ32::from_ratio(1, 4).expect("0.25"));
            }
            _ => panic!("expected independent withholding budget"),
        }
    }
}
