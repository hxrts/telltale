use telltale_macros::tell;

tell! {
    effect Runtime
      observe watchPresence : Session -> PresenceView
      {
        class : observational
        progress : immediate
        region : session
        agreement_use : forbidden
        reentrancy : allow
      }

    protocol WatchFlow uses Runtime =
      roles Coordinator, Worker
      choice Coordinator at
        | Continue =>
            Coordinator -> Worker : Prepare
            authoritative let presence = check Runtime.watchPresence(session)
            Coordinator -> Worker : Seen(presence)
        | Abort =>
            Coordinator -> Worker : Abort
}

fn main() {}
