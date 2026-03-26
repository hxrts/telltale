//! Elevator controller with authority handoff and publication.
//!
//! This is an effect-boundary example demonstrating ownership transfer and
//! publication constructs: `handoff` transfers door control authority from the
//! user panel to the elevator relay, and `publish` records the door state
//! transition as a protocol-visible event. The protocol uses authority-level
//! constructs and is not session-projectable. Rust reads the generated metadata
//! to inspect the handoff and publication surfaces.

use telltale::tell;

tell! {
    -- // Execution profile for the proof-backed effect boundary.
    profile Replay fairness eventual admissibility replay escalation_window bounded

    -- // Host-side door action selected by the user.
    type DoorAction =
      | Open
      | Close

    -- // User-facing panel chooses one door action for this session.
    effect UserPanel
      command choose : Session -> DoorAction
      {
        class : best_effort
        progress : immediate
        region : session
        agreement_use : none
        reentrancy : allow
      }

    -- // Door motor realizes the physical open/close operations.
    effect DoorMotor
      command open : Unit -> Unit
      {
        class : best_effort
        progress : immediate
        region : fragment
        agreement_use : none
        reentrancy : allow
      }
      command close : Unit -> Unit
      {
        class : best_effort
        progress : immediate
        region : fragment
        agreement_use : none
        reentrancy : allow
      }

    -- // User chooses a door command. Authority over the door operation is
    -- // handed off from the user panel to the elevator relay via an explicit
    -- // receipt. The relay publishes the state transition as a protocol event.
    protocol Elevator uses UserPanel, DoorMotor under Replay =
      roles U, D, E
      choice U at
        | OpenDoor =>
          U -> E : OpenDoor
          handoff door_control to E with control_receipt
          E -> D : OpenDoor
          D -> E : DoorOpened
          publish door_state as DoorStateChanged
          E -> D : CloseDoor
          D -> E : DoorClosed
          E -> U : DoorClosed
        | CloseDoor =>
          U -> E : CloseDoor
          handoff door_control to E with control_receipt
          E -> D : CloseDoor
          D -> E : DoorClosed
          publish door_state as DoorStateChanged
          E -> U : DoorClosed
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!(
        "strongest tier = {}",
        Elevator::proof_status::STRONGEST_TIER
    );
    println!(
        "session projectable = {}",
        Elevator::proof_status::SESSION_PROJECTABLE
    );
    println!(
        "protocol machine executable = {}",
        Elevator::proof_status::PROTOCOL_MACHINE_EXECUTABLE
    );
    println!(
        "projection blocker = {:?}",
        Elevator::proof_status::SESSION_PROJECTION_ERROR
    );

    // The authority module exposes handoff and publication metadata.
    let handoffs = Elevator::authority::HANDOFFS;
    println!("handoffs = {}", handoffs.len());
    for h in handoffs {
        println!(
            "  {} -> {} with receipt {}",
            h.operation_name, h.target_role, h.receipt_name
        );
    }

    let publications = Elevator::authority::PUBLICATIONS;
    println!("publications = {}", publications.len());
    for p in publications {
        println!("  {}", p.publication_name);
    }

    // Demonstrate creating typed semantic objects from the generated metadata.
    if let Some(h) = Elevator::authority::handoff("door_control") {
        let handoff = h.semantic_handoff(1, 0, 0, 2);
        println!("handoff id = {}", handoff.handoff_id);
        println!("from coroutine = {}", handoff.from_coro);
        println!("to coroutine = {}", handoff.to_coro);
    }

    if let Some(p) = Elevator::authority::publication("DoorStateChanged") {
        let event = p.publication_event("door-pub#1", "open-door-op#1");
        println!("publication id = {}", event.publication_id);
        println!("operation id = {}", event.operation_id);
    }

    Ok(())
}
