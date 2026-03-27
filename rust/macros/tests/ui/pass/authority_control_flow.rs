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
    }

    protocol AuthorityControlFlow uses Runtime =
      roles Coordinator, Worker
      observe let presence = observe Runtime.watchPresence(session)
      authoritative let readiness = check Runtime.ready(session)
      choice Coordinator at
        | Continue =>
            Coordinator -> Worker : Prepare
            Coordinator -> Worker : ContinueObserved
        | Retry =>
            Coordinator -> Worker : RetryObserved
      case readiness of
        | Ok(witness) =>
            Coordinator -> Worker : Commit
        | Err(reason) =>
            Coordinator -> Worker : Abort
}

fn main() {
    let observed = AuthorityControlFlow::authority::observed_binding("presence").unwrap();
    let authoritative =
        AuthorityControlFlow::authority::authoritative_binding("readiness").unwrap();
    assert_eq!(observed.binding_name, "presence");
    assert_eq!(authoritative.binding_name, "readiness");
    assert!(AuthorityControlFlow::proof_status::SESSION_PROJECTABLE);
}
