use crate::ast::Choreography;
pub use telltale_parser::{
    GeneratedEffectBehavior, GeneratedEffectFamily, GeneratedEffectOperation,
    GeneratedSimulationMetadata, GeneratedSimulationMode,
};

/// Extension trait adding generated-effect-family support to `Choreography`.
pub trait ChoreographyEffectExt {
    fn generated_effect_families(&self) -> Vec<GeneratedEffectFamily>;
}

impl ChoreographyEffectExt for Choreography {
    fn generated_effect_families(&self) -> Vec<GeneratedEffectFamily> {
        telltale_parser::generated_effect_families(self)
    }
}

#[cfg(test)]
mod tests {
    use super::{ChoreographyEffectExt, GeneratedEffectBehavior};
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
