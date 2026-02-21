//! Scenario and property presets for integration tests.

use telltale_types::FixedQ32;

use crate::fault::Fault;
use crate::material::MaterialParams;
use crate::property::Property;
use crate::scenario::{
    EventSpec, FaultActionSpec, LivenessSpec, OutputConfig, OutputFormat, PropertiesSpec, Scenario,
    TriggerSpec,
};

/// Build a deterministic baseline scenario with no network or fault events.
#[must_use]
pub fn deterministic_baseline(
    name: impl Into<String>,
    roles: Vec<String>,
    steps: u64,
    material: MaterialParams,
) -> Scenario {
    Scenario {
        name: name.into(),
        roles,
        steps,
        concurrency: 1,
        seed: 0,
        network: None,
        material,
        events: Vec::new(),
        properties: None,
        checkpoint_interval: None,
        output: OutputConfig {
            file: None,
            format: OutputFormat::Json,
        },
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

/// Add a message-drop fault window starting at a specific tick.
#[must_use]
pub fn with_message_drop_fault(
    mut scenario: Scenario,
    at_tick: u64,
    probability: FixedQ32,
) -> Scenario {
    scenario.events.push(EventSpec {
        trigger: TriggerSpec {
            immediate: false,
            at_tick: Some(at_tick),
            after_step: None,
            random: None,
            on_event: None,
        },
        action: FaultActionSpec::MessageDrop { probability },
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

/// Convert a `Fault` value to a scenario fault action when possible.
#[must_use]
pub fn fault_to_action(fault: &Fault) -> Option<FaultActionSpec> {
    match fault {
        Fault::MessageDrop { probability } => Some(FaultActionSpec::MessageDrop {
            probability: *probability,
        }),
        Fault::MessageDelay { ticks } => Some(FaultActionSpec::MessageDelay {
            ticks: *ticks as u64,
        }),
        Fault::MessageCorruption { probability } => Some(FaultActionSpec::MessageCorruption {
            probability: *probability,
        }),
        Fault::NodeCrash { role, duration } => Some(FaultActionSpec::NodeCrash {
            role: role.clone(),
            duration: duration.map(|value| value as u64),
        }),
        Fault::NetworkPartition { groups, duration } => Some(FaultActionSpec::NetworkPartition {
            groups: groups.clone(),
            duration: *duration as u64,
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::material::MeanFieldParams;

    fn material() -> MaterialParams {
        MaterialParams::MeanField(MeanFieldParams {
            beta: FixedQ32::one(),
            species: vec!["up".into(), "down".into()],
            initial_state: vec![FixedQ32::half(), FixedQ32::half()],
            step_size: FixedQ32::from_ratio(1, 100).expect("0.01"),
        })
    }

    #[test]
    fn baseline_has_expected_defaults() {
        let scenario =
            deterministic_baseline("baseline", vec!["A".into(), "B".into()], 16, material());
        assert_eq!(scenario.seed, 0);
        assert_eq!(scenario.concurrency, 1);
        assert!(scenario.events.is_empty());
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
    fn message_drop_fault_is_added() {
        let scenario =
            deterministic_baseline("baseline", vec!["A".into(), "B".into()], 16, material());
        let updated =
            with_message_drop_fault(scenario, 5, FixedQ32::from_ratio(1, 4).expect("0.25"));
        assert_eq!(updated.events.len(), 1);
        match updated.events[0].action {
            FaultActionSpec::MessageDrop { probability } => {
                assert_eq!(probability, FixedQ32::from_ratio(1, 4).expect("0.25"));
            }
            _ => panic!("expected message drop action"),
        }
    }
}
