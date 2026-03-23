use crate::compiler::parser::parse_choreography_str;

#[test]
fn test_parse_authority_surface_with_effects_types_and_uses() {
    let input = r#"
type CommitError =
  | NotReady
  | TimedOut

type alias ReadyWitness = { epoch : Int, issuedBy : Role }

effect Runtime
  authoritative ready : Session -> Result CommitError ReadyWitness
  command transfer : TransferRequest -> Result TransferError TransferReceipt

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
  timeout 5s Coordinator at
    Worker -> Coordinator : Ready
  on timeout =>
    Coordinator -> Worker : Cancel
  on cancel =>
    Coordinator -> Client : Cancelled
  choice Coordinator at
    | Commit when check Runtime.ready(session) yields witness =>
        Coordinator -> Worker : CommitAgain(witness)
    | Abort =>
        Coordinator -> Worker : Abort
"#;

    let choreography = parse_choreography_str(input).expect("authority surface should parse");
    assert_eq!(choreography.type_decls().len(), 2);
    assert_eq!(choreography.effect_decls().len(), 2);
    assert_eq!(
        choreography.protocol_uses(),
        vec!["Runtime".to_string(), "Audit".to_string()]
    );
    let runtime_metadata = choreography.runtime_effect_metadata();
    assert!(
        runtime_metadata.iter().any(|op| {
            op.interface_name == "Runtime"
                && op.operation_name == "ready"
                && op.authority_class == crate::ast::EffectOpAuthorityClass::Authoritative
        }),
        "runtime effect metadata should carry effect authority class"
    );
    choreography.validate().expect("declared effect uses should validate");
}

#[test]
fn test_parse_let_in_and_maybe_surface() {
    let input = r#"
type alias InviteHandle = { id : Int }

effect Runtime
  lookupInvite : Session -> Maybe InviteHandle

protocol InviteFlow uses Runtime =
  roles Coordinator, Worker
  let invite = check Runtime.lookupInvite(session) in
    case invite of
      | Just(handle) =>
          Coordinator -> Worker : UseInvite(handle)
      | Nothing =>
          Coordinator -> Worker : MissingInvite
"#;

    let choreography = parse_choreography_str(input).expect("let-in Maybe surface should parse");
    choreography.validate().expect("effect invocation should validate");
}

#[test]
fn test_reject_non_exhaustive_result_case() {
    let input = r#"
effect Runtime
  ready : Session -> Result CommitError ReadyWitness

protocol CommitFlow uses Runtime =
  roles Coordinator, Worker
  let readiness = check Runtime.ready(session)
  case readiness of
    | Ok(witness) =>
        Coordinator -> Worker : Commit(witness)
"#;

    let err = parse_choreography_str(input).expect_err("non-exhaustive Result case should fail");
    assert!(!err.to_string().is_empty());
}

#[test]
fn test_reject_duplicate_linear_binding_use() {
    let input = r#"
protocol TransferFlow =
  roles Coordinator, Worker, Client
  let receipt = transfer Session from Coordinator to Worker
  Coordinator -> Worker : TransferAccepted(receipt)
  Coordinator -> Client : ReceiptAudit(receipt)
"#;

    let err = parse_choreography_str(input).expect_err("duplicate linear use should fail");
    assert!(err.to_string().contains("consumed more than once"));
}

#[test]
fn test_reject_dropped_linear_binding_use() {
    let input = r#"
protocol TransferFlow =
  roles Coordinator, Worker
  let receipt = transfer Session from Coordinator to Worker
  Coordinator -> Worker : TransferAccepted
"#;

    let err = parse_choreography_str(input).expect_err("dropped linear binding should fail");
    assert!(err.to_string().contains("never consumed"));
}

#[test]
fn test_reject_undeclared_protocol_use() {
    let input = r#"
protocol CommitFlow uses Runtime =
  roles Coordinator, Worker
  Coordinator -> Worker : Ping
"#;

    let choreography = parse_choreography_str(input).expect("parse should succeed");
    let err = choreography
        .validate()
        .expect_err("undeclared effect interface should fail validation");
    assert!(err.to_string().contains("undeclared effect interface"));
}

#[test]
fn test_reject_undeclared_effect_operation_invocation() {
    let input = r#"
effect Runtime
  ready : Session -> Result CommitError ReadyWitness

protocol CommitFlow uses Runtime =
  roles Coordinator, Worker
  let readiness = check Runtime.lookup(session)
  case readiness of
    | Ok(witness) =>
        Coordinator -> Worker : Commit(witness)
    | Err(reason) =>
        Coordinator -> Worker : Retry(reason)
"#;

    let choreography = parse_choreography_str(input).expect("parse should succeed");
    let err = choreography
        .validate()
        .expect_err("undeclared effect operation should fail validation");
    assert!(err.to_string().contains("undeclared operation"));
}

#[test]
fn test_reject_duplicate_effect_declarations() {
    let input = r#"
effect Runtime
  ready : Session -> Result CommitError ReadyWitness

effect Runtime
  transfer : TransferRequest -> Result TransferError TransferReceipt

protocol CommitFlow uses Runtime =
  roles Coordinator, Worker
  Coordinator -> Worker : Ping
"#;

    let choreography = parse_choreography_str(input).expect("parse should succeed");
    let err = choreography
        .validate()
        .expect_err("duplicate effect declarations should fail validation");
    assert!(err.to_string().contains("duplicate effect interface declaration"));
}

#[test]
fn test_reject_observational_effect_used_with_check() {
    let input = r#"
effect Runtime
  observe watchPresence : Session -> PresenceView

protocol WatchFlow uses Runtime =
  roles Coordinator, Worker
  let presence = check Runtime.watchPresence(session)
  Coordinator -> Worker : Seen(presence)
"#;

    let choreography = parse_choreography_str(input).expect("parse should succeed");
    let err = choreography
        .validate()
        .expect_err("observational effect use should fail validation");
    assert!(err.to_string().contains("observational"));
}
