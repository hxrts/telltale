use telltale_language::compiler::parser::parse_choreography_str;
use telltale_language::{generated_effect_families, GeneratedEffectBehavior, GeneratedEffectFamily};

#[test]
fn generated_effect_family_schema_roundtrips_with_simulation_metadata() {
    let choreography = parse_choreography_str(
        r#"
effect Runtime
  authoritative readChannel : ChannelRef -> Result ReadError ChannelSnapshot
  {
    class : authoritative
    progress : may_block
    region : fragment
    agreement_use : required
    reentrancy : reject_same_fragment
  }
  command acceptInvite : InviteRef -> Result AcceptError MaterializedChannel
  {
    class : best_effort
    progress : immediate
    region : session
    agreement_use : none
    reentrancy : allow
  }
  observe watchPresence : ChannelId -> PresenceView
  {
    class : observational
    progress : immediate
    region : session
    agreement_use : forbidden
    reentrancy : allow
  }

protocol Flow uses Runtime =
  roles Coordinator
  Coordinator -> Coordinator : Ping
"#,
    )
    .expect("parse choreography");

    let families = generated_effect_families(&choreography);
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

    let decoded: Vec<GeneratedEffectFamily> = serde_json::from_str(&json).expect("decode manifest");
    assert_eq!(decoded, families);
}
