use telltale_macros::tell;

tell! {
    protocol TransferFlow =
      roles Coordinator, Worker
      let receipt = transfer Session from Coordinator to Worker
      choice Coordinator at
        | Continue =>
            Coordinator -> Worker : Prepare
            handoff acceptInvite to Worker with receipt
        | Abort =>
            Coordinator -> Worker : Abort
}

fn main() {}
