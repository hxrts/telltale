//! Two-party travel agency negotiation with evidence binding and typed failure.
//!
//! This is an effect-boundary example demonstrating authority constructs with
//! proof-backed metadata: `let`/`check` evidence bindings, `case`/`of` typed
//! result matching, and `timeout`/`on cancel` failure paths. Rust reads the
//! generated metadata to inspect the authority surface.

use telltale::tell;

tell! {
    -- // Execution profile for the proof-backed effect boundary.
    profile Replay fairness eventual admissibility replay escalation_window bounded

    -- // Typed error carries the rejection reason.
    type QuoteError =
      | NotAvailable
      | TooExpensive

    -- // Typed approval carries the quoted price and delivery window.
    type alias QuoteApproval =
    {
      price : Int
    }

    -- // Agency host computes a quote, which may fail.
    effect AgencyRuntime
      authoritative quote : Int -> Result QuoteError QuoteApproval
      {
        class : authoritative
        progress : may_block
        region : fragment
        agreement_use : none
        reentrancy : reject_same_fragment
      }

    -- // Customer places an order. The agency quote is checked as typed evidence.
    -- // A successful quote flows into the accept branch as a witness value.
    -- // A failed quote ends with an explicit typed rejection. The timeout
    -- // branch fires if the agency does not respond within 5 seconds.
    protocol TravelAgency uses AgencyRuntime under Replay =
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

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!(
        "strongest tier = {}",
        TravelAgency::proof_status::STRONGEST_TIER
    );
    println!(
        "session projectable = {}",
        TravelAgency::proof_status::SESSION_PROJECTABLE
    );
    println!(
        "protocol machine executable = {}",
        TravelAgency::proof_status::PROTOCOL_MACHINE_EXECUTABLE
    );
    println!(
        "projection blocker = {:?}",
        TravelAgency::proof_status::SESSION_PROJECTION_ERROR
    );

    // The authority module exposes the check bindings and evidence metadata.
    let reads = TravelAgency::authority::AUTHORITATIVE_READS;
    println!("authoritative reads = {}", reads.len());
    for entry in reads {
        println!(
            "  {} via {}.{}",
            entry.binding_name, entry.effect_interface, entry.effect_operation
        );
    }

    // Demonstrate creating typed semantic objects from the generated metadata.
    if let Some(binding) = TravelAgency::authority::authoritative_binding("approval") {
        let read = binding.authoritative_read("travel-quote#1");
        println!("authoritative read id = {}", read.read_id);
        println!("predicate ref = {:?}", read.predicate_ref);

        let observed = binding.observed_read("travel-observed#1", 0, "test-handler");
        println!("observed read id = {}", observed.read_id);
    }

    Ok(())
}
