use crate::compiler::parser::parse_choreography_str;

#[test]
fn test_parse_authority_surface_with_effects_types_and_uses() {
    let input = r#"
type CommitError | NotReady | TimedOut

type alias ReadyWitness = { epoch : Int, issuedBy : Role }

effect Runtime
  ready : Session -> Result CommitError ReadyWitness
  transfer : TransferRequest -> Result TransferError TransferReceipt

effect Audit
  record : AuditEvent -> Unit

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
    timeout 5s at Coordinator {
      Worker -> Coordinator : Ready
    } on timeout {
      Coordinator -> Worker : Cancel
    } on cancel {
      Coordinator -> Client : Cancelled
    }
    choice at Coordinator {
      | Commit when check Runtime.ready(session) yields witness -> {
        Coordinator -> Worker : CommitAgain(witness)
      }
      | Abort -> {
        Coordinator -> Worker : Abort
      }
    }
  }
"#;

    let choreography = parse_choreography_str(input).expect("authority surface should parse");
    assert_eq!(choreography.type_decls().len(), 2);
    assert_eq!(choreography.effect_decls().len(), 2);
    assert_eq!(
        choreography.protocol_uses(),
        vec!["Runtime".to_string(), "Audit".to_string()]
    );
    choreography.validate().expect("declared effect uses should validate");
}

#[test]
fn test_reject_non_exhaustive_result_case() {
    let input = r#"
effect Runtime
  ready : Session -> Result CommitError ReadyWitness

protocol CommitFlow uses Runtime =
  {
    roles Coordinator, Worker
    let readiness = check Runtime.ready(session)
    case readiness of {
      | Ok witness -> {
        Coordinator -> Worker : Commit(witness)
      }
    }
  }
"#;

    let err = parse_choreography_str(input).expect_err("non-exhaustive Result case should fail");
    assert!(!err.to_string().is_empty());
}

#[test]
fn test_reject_duplicate_linear_binding_use() {
    let input = r#"
protocol TransferFlow =
  {
    roles Coordinator, Worker, Client
    let receipt = transfer Session from Coordinator to Worker
    Coordinator -> Worker : TransferAccepted(receipt)
    Coordinator -> Client : ReceiptAudit(receipt)
  }
"#;

    let err = parse_choreography_str(input).expect_err("duplicate linear use should fail");
    assert!(err.to_string().contains("consumed more than once"));
}

#[test]
fn test_reject_undeclared_protocol_use() {
    let input = r#"
protocol CommitFlow uses Runtime =
  {
    roles Coordinator, Worker
    Coordinator -> Worker : Ping
  }
"#;

    let choreography = parse_choreography_str(input).expect("parse should succeed");
    let err = choreography
        .validate()
        .expect_err("undeclared effect interface should fail validation");
    assert!(err.to_string().contains("undeclared effect interface"));
}
