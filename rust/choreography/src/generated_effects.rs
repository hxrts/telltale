use crate::ast::{Choreography, EffectOpAuthorityClass};
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GeneratedEffectBehavior {
    OneShot,
    Stream,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GeneratedSimulationMode {
    Deterministic,
    Adversarial,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeneratedSimulationMetadata {
    pub behavior: GeneratedEffectBehavior,
    pub mode: GeneratedSimulationMode,
    pub latency_policy: String,
    pub timeout_policy: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeneratedEffectOperation {
    pub interface_name: String,
    pub operation_name: String,
    pub rust_method_name: String,
    pub request_type_name: String,
    pub outcome_type_name: String,
    pub authority_class: EffectOpAuthorityClass,
    pub input_type: String,
    pub output_type: String,
    pub simulation: GeneratedSimulationMetadata,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeneratedEffectFamily {
    pub interface_name: String,
    pub request_enum_name: String,
    pub outcome_enum_name: String,
    pub host_trait_name: String,
    pub simulator_trait_name: String,
    pub scenario_builder_name: String,
    pub operations: Vec<GeneratedEffectOperation>,
}

impl Choreography {
    #[must_use]
    pub fn generated_effect_families(&self) -> Vec<GeneratedEffectFamily> {
        self.effect_decls()
            .into_iter()
            .map(|effect| {
                let request_enum_name = format!("{}Request", effect.name);
                let outcome_enum_name = format!("{}Outcome", effect.name);
                let host_trait_name = format!("{}ExternalHandler", effect.name);
                let simulator_trait_name = format!("{}SimulatorHandler", effect.name);
                let scenario_builder_name = format!("{}ScenarioBuilder", effect.name);
                let operations = effect
                    .operations
                    .into_iter()
                    .map(|op| {
                        let operation_type_name = to_upper_camel_case(&op.name);
                        GeneratedEffectOperation {
                            interface_name: effect.name.clone(),
                            operation_name: op.name.clone(),
                            rust_method_name: to_snake_case(&op.name),
                            request_type_name: format!(
                                "{}{}Request",
                                effect.name, operation_type_name
                            ),
                            outcome_type_name: format!(
                                "{}{}Outcome",
                                effect.name, operation_type_name
                            ),
                            authority_class: op.authority_class,
                            input_type: op.input_type,
                            output_type: op.output_type,
                            simulation: simulation_defaults(op.authority_class),
                        }
                    })
                    .collect();

                GeneratedEffectFamily {
                    interface_name: effect.name,
                    request_enum_name,
                    outcome_enum_name,
                    host_trait_name,
                    simulator_trait_name,
                    scenario_builder_name,
                    operations,
                }
            })
            .collect()
    }
}

fn simulation_defaults(authority_class: EffectOpAuthorityClass) -> GeneratedSimulationMetadata {
    match authority_class {
        EffectOpAuthorityClass::Observe => GeneratedSimulationMetadata {
            behavior: GeneratedEffectBehavior::Stream,
            mode: GeneratedSimulationMode::Deterministic,
            latency_policy: "best_effort".to_string(),
            timeout_policy: "not_authoritative".to_string(),
        },
        EffectOpAuthorityClass::Authoritative => GeneratedSimulationMetadata {
            behavior: GeneratedEffectBehavior::OneShot,
            mode: GeneratedSimulationMode::Deterministic,
            latency_policy: "bounded".to_string(),
            timeout_policy: "required".to_string(),
        },
        EffectOpAuthorityClass::Command => GeneratedSimulationMetadata {
            behavior: GeneratedEffectBehavior::OneShot,
            mode: GeneratedSimulationMode::Deterministic,
            latency_policy: "immediate".to_string(),
            timeout_policy: "optional".to_string(),
        },
    }
}

fn to_snake_case(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    for (idx, ch) in input.chars().enumerate() {
        if ch.is_ascii_uppercase() {
            if idx > 0 {
                out.push('_');
            }
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push(ch);
        }
    }
    out
}

fn to_upper_camel_case(input: &str) -> String {
    let mut out = String::with_capacity(input.len());
    let mut uppercase_next = true;
    for ch in input.chars() {
        if ch == '_' || ch == '-' {
            uppercase_next = true;
            continue;
        }
        if uppercase_next {
            out.push(ch.to_ascii_uppercase());
            uppercase_next = false;
        } else {
            out.push(ch);
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::GeneratedEffectBehavior;
    use crate::compiler::parser::parse_choreography_str;

    #[test]
    fn generated_effect_families_follow_declared_effect_interfaces() {
        let choreography = parse_choreography_str(
            r#"
effect Runtime
  authoritative readChannel : ChannelRef -> Result ReadError ChannelSnapshot
  command acceptInvite : InviteRef -> Result AcceptError MaterializedChannel
  observe watchPresence : ChannelId -> PresenceView

protocol Flow uses Runtime =
  roles Coordinator
  Coordinator -> Coordinator : Ping
"#,
        )
        .expect("parse effect surface");

        let families = choreography.generated_effect_families();
        assert_eq!(families.len(), 1);
        let runtime = &families[0];
        assert_eq!(runtime.interface_name, "Runtime");
        assert_eq!(runtime.host_trait_name, "RuntimeExternalHandler");
        assert_eq!(runtime.simulator_trait_name, "RuntimeSimulatorHandler");
        assert_eq!(runtime.operations.len(), 3);
        assert_eq!(runtime.operations[0].rust_method_name, "read_channel");
        assert_eq!(
            runtime.operations[2].simulation.behavior,
            GeneratedEffectBehavior::Stream
        );
    }
}
