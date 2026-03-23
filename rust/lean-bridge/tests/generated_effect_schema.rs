use telltale_choreography::compiler::parser::parse_choreography_str;
use telltale_choreography::{GeneratedEffectBehavior, GeneratedEffectFamily};

#[test]
fn generated_effect_family_schema_roundtrips_with_simulation_metadata() {
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
    .expect("parse choreography");

    let families = choreography.generated_effect_families();
    assert_eq!(families.len(), 1);
    assert_eq!(families[0].interface_name, "Runtime");
    assert_eq!(families[0].host_trait_name, "RuntimeExternalHandler");
    assert_eq!(families[0].simulator_trait_name, "RuntimeSimulatorHandler");
    assert_eq!(
        families[0]
            .operations
            .iter()
            .find(|op| op.operation_name == "watchPresence")
            .expect("watchPresence op")
            .simulation
            .behavior,
        GeneratedEffectBehavior::Stream
    );

    let json = serde_json::to_string_pretty(&families).expect("encode manifest");
    assert!(json.contains("\"interface_name\": \"Runtime\""));
    assert!(json.contains("\"host_trait_name\": \"RuntimeExternalHandler\""));
    assert!(json.contains("\"simulator_trait_name\": \"RuntimeSimulatorHandler\""));

    let decoded: Vec<GeneratedEffectFamily> =
        serde_json::from_str(&json).expect("decode manifest");
    assert_eq!(decoded, families);
}
