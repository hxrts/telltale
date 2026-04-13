//! Pass: authority surface with effect declarations.
use telltale::tell;

tell! {
    effect Runtime
      authoritative ready : Session -> Result ReadyErr ReadyWitness
      {
        class : authoritative
        progress : may_block
        region : fragment
        agreement_use : required
        reentrancy : reject_same_fragment
      }
      observe watchPresence : Session -> PresenceView
      {
        class : observational
        progress : immediate
        region : session
        agreement_use : forbidden
        reentrancy : allow
      }

    type ReadyErr =
      | NotReady

    type alias ReadyWitness =
    {
      epoch : Int
      issuedBy : Role
    }

    protocol AuthorityFlow uses Runtime =
      roles Coordinator, Worker
      observe let presence = observe Runtime.watchPresence(commitSession)
      authoritative let witness = check Runtime.ready(commitSession)
      publish witness as AcceptedPublication
      materialize acceptedProof from AcceptedPublication
      let receipt = transfer Session from Coordinator to Worker
      handoff acceptInvite to Worker with receipt
      Coordinator -> Worker : Commit
}

fn main() {
    let observed = AuthorityFlow::authority::observed_binding("presence").unwrap();
    let authoritative = AuthorityFlow::authority::authoritative_binding("witness").unwrap();
    let publication = AuthorityFlow::authority::publication("AcceptedPublication").unwrap();
    let materialization = AuthorityFlow::authority::materialization("acceptedProof").unwrap();
    let canonical_handle = AuthorityFlow::authority::canonical_handle("acceptedProof").unwrap();
    let receipt = AuthorityFlow::authority::receipt("receipt").unwrap();
    let proof = materialization.materialization_proof("proof#1", "Runtime.ready", "digest:ready");
    let handle = canonical_handle.canonical_handle("handle#1", &proof);
    let handoff = AuthorityFlow::authority::handoff("acceptInvite").unwrap();

    assert_eq!(observed.binding_name, "presence");
    assert_eq!(authoritative.binding_name, "witness");
    assert_eq!(
        authoritative.capability_class,
        telltale::dsl::semantic::ProtocolCriticalCapabilityClass::Evidence
    );
    assert_eq!(publication.publication_name, "AcceptedPublication");
    assert_eq!(
        canonical_handle.handle_kind,
        telltale::dsl::semantic::CanonicalHandleKind::Materialization
    );
    assert_eq!(receipt.subject, "Session");
    assert_eq!(receipt.from_role, "Coordinator");
    assert_eq!(receipt.to_role, "Worker");
    assert_eq!(handle.proof_ref.as_deref(), Some("proof#1"));
    assert_eq!(handoff.target_role, "Worker");
    let ready = AuthorityFlow::effects::runtime::operation("ready").unwrap();
    assert_eq!(
        ready.semantic_class,
        telltale::dsl::semantic::EffectSemanticClass::Authoritative
    );
    assert!(ready.architecturally_legal());
    let watch_request =
        AuthorityFlow::effects::RuntimeRequest::WatchPresence(AuthorityFlow::effects::Session::new(
            "authority-flow#1",
        ));
    let watch = AuthorityFlow::effects::runtime::request_metadata(&watch_request);
    assert_eq!(watch.operation_name, "watchPresence");
    assert!(AuthorityFlow::proof_status::SESSION_PROJECTABLE);
}
