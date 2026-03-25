use telltale::tell;

tell! {
    effect Runtime
      authoritative ready : Session -> Result ReadyErr ReadyWitness
      observe watchPresence : Session -> PresenceView

    type ReadyErr =
      | NotReady

    type alias ReadyWitness = { epoch : Int, issuedBy : Role }

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
    let proof = materialization.materialization_proof("proof#1", "Runtime.ready", "digest:ready");
    let handle = materialization.canonical_handle("handle#1", &proof);
    let handoff = AuthorityFlow::authority::handoff("acceptInvite").unwrap();

    assert_eq!(observed.binding_name, "presence");
    assert_eq!(authoritative.binding_name, "witness");
    assert_eq!(publication.publication_name, "AcceptedPublication");
    assert_eq!(handle.proof_ref.as_deref(), Some("proof#1"));
    assert_eq!(handoff.target_role, "Worker");
    assert!(!AuthorityFlow::proof_status::SESSION_PROJECTABLE);
}
