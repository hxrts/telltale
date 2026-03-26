use telltale_language::generated_effect_families;
use telltale_runtime::compiler::parser::parse_choreography_str;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = r#"
type CommitError =
  | NotReady
  | TimedOut

type alias ReadyWitness =
{
  epoch : Int
  issuedBy : Role
}

effect Runtime
  authoritative ready : Session -> Result CommitError ReadyWitness
  {
    class : authoritative
    progress : may_block
    region : fragment
    agreement_use : required
    reentrancy : reject_same_fragment
  }
  command transfer : TransferRequest -> Result TransferError TransferReceipt
  {
    class : best_effort
    progress : immediate
    region : session
    agreement_use : none
    reentrancy : allow
  }
  observe watchPresence : Session -> PresenceView
  {
    class : observational
    progress : immediate
    region : session
    agreement_use : forbidden
    reentrancy : allow
  }

effect Audit
  observe record : AuditEvent -> Unit
  {
    class : observational
    progress : immediate
    region : global
    agreement_use : forbidden
    reentrancy : allow
  }

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
            telltale_language::ast::LanguageTier::FullSpec => "full_spec",
            telltale_language::ast::LanguageTier::SessionProjectable => "session_projectable",
            telltale_language::ast::LanguageTier::ProtocolMachineExecutable =>
                "protocol_machine_executable",
            telltale_language::ast::LanguageTier::ProofOnly => "proof_only",
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
