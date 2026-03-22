use telltale_choreography::compiler::parser::parse_choreography_str;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let input = r#"
type CommitError | NotReady | TimedOut

type alias ReadyWitness = { epoch : Int, issuedBy : Role }

effect Runtime
  authoritative ready : Session -> Result CommitError ReadyWitness
  command transfer : TransferRequest -> Result TransferError TransferReceipt
  observe watchPresence : Session -> PresenceView

effect Audit
  observe record : AuditEvent -> Unit

protocol CommitFlow uses Runtime, Audit =
  {
    roles Coordinator, Worker, Client
    let readiness = check Runtime.ready(session)
    case readiness of {
      | Ok witness -> {
        Coordinator -> Worker : Commit(witness)
      }
      | Err reason -> {
        Coordinator -> Client : Retry(reason)
      }
    }
    let receipt = transfer Session from Coordinator to Worker
    Worker -> Client : TransferAccepted(receipt)
    timeout 5s at Coordinator {
      Worker -> Coordinator : Ready
    } on timeout {
      Coordinator -> Worker : Cancel
    } on cancel {
      Coordinator -> Client : Cancelled
    }
  }
"#;

    let choreography = parse_choreography_str(input)?;
    println!("protocol: {}", choreography.qualified_name());
    println!("types: {}", choreography.type_decls().len());
    println!("effects: {}", choreography.effect_decls().len());
    println!("uses: {}", choreography.protocol_uses().join(", "));
    Ok(())
}
