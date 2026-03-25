use telltale_choreography::compiler::parser::parse_choreography_str;
use telltale_parser::generated_effect_families;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = r#"
type CommitError =
  | NotReady
  | TimedOut

type alias ReadyWitness = { epoch : Int, issuedBy : Role }

effect Runtime
  authoritative ready : Session -> Result CommitError ReadyWitness
  command transfer : TransferRequest -> Result TransferError TransferReceipt
  observe watchPresence : Session -> PresenceView

effect Audit
  observe record : AuditEvent -> Unit

protocol CommitFlow uses Runtime, Audit =
  roles Coordinator, Worker, Client
  let readiness = check Runtime.ready(session)
  case readiness of
    | Ok(witness) =>
        Coordinator -> Worker : Commit(witness)
    | Err(reason) =>
        Coordinator -> Client : Retry(reason)
  let receipt = transfer Session from Coordinator to Worker
  Worker -> Client : TransferAccepted(receipt)
  timeout 5s Coordinator at
    Worker -> Coordinator : Ready
  on timeout =>
    Coordinator -> Worker : Cancel
  on cancel =>
    Coordinator -> Client : Cancelled
"#;

    let choreography = parse_choreography_str(input)?;
    let generated = generated_effect_families(&choreography);
    println!("protocol: {}", choreography.qualified_name());
    println!(
        "strongest tier: {}",
        match choreography.language_tier_status().strongest_tier {
            telltale_parser::ast::LanguageTier::FullSpec => "full_spec",
            telltale_parser::ast::LanguageTier::SessionProjectable => "session_projectable",
            telltale_parser::ast::LanguageTier::ProtocolMachineExecutable =>
                "protocol_machine_executable",
            telltale_parser::ast::LanguageTier::ProofOnly => "proof_only",
        }
    );
    println!("types: {}", choreography.type_declarations().len());
    println!(
        "effects: {}",
        choreography.effect_interface_declarations().len()
    );
    println!("uses: {}", choreography.protocol_uses().join(", "));
    println!("generated effect families: {}", generated.len());
    for family in generated {
        println!(
            "family {} => host trait {}, simulator trait {}, operations: {}",
            family.interface_name,
            family.host_trait_name,
            family.simulator_trait_name,
            family.operations.len()
        );
    }
    Ok(())
}
