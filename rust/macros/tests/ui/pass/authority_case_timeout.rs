//! Pass: Result-pattern case labels plus timeout remain codegen-safe.
use telltale::tell;

tell! {
    profile Replay fairness eventual admissibility replay escalation_window bounded

    effect AgencyRuntime
      authoritative quote : Int -> Result QuoteError QuoteApproval
      {
        class : authoritative
        progress : may_block
        region : fragment
        agreement_use : none
        reentrancy : reject_same_fragment
      }

    type QuoteError =
      | NotAvailable
      | TooExpensive

    type alias QuoteApproval =
    {
      price : Int
      nights : Int
    }

    protocol AuthorityCaseTimeout uses AgencyRuntime under Replay =
      roles Customer, Agency
      Customer -> Agency : Order
      authoritative let approval = check AgencyRuntime.quote(distance)
      case approval of
        | Ok(witness) =>
            Agency -> Customer : Confirmation
        | Err(reason) =>
            Agency -> Customer : Rejection
      timeout 5s Agency at
        Agency -> Customer : Scheduled
      on timeout =>
        Agency -> Customer : TimedOut
      on cancel =>
        Agency -> Customer : Cancelled
}

fn main() {
    assert!(AuthorityCaseTimeout::proof_status::SESSION_PROJECTABLE);
    assert!(!AuthorityCaseTimeout::proof_status::DEADLOCK_AUTOMATION_ELIGIBLE);
}
