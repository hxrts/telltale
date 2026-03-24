//! Elevator controller with three-way coordination.
//!
//! Three roles -- User (U), Door (D), and Elevator (E) -- coordinate
//! open/close commands through a bounded request-response cycle:
//!
//! 1. The user selects **OpenDoor** or **CloseDoor** (communicated to the
//!    elevator).
//! 2. The elevator relays the same command label to the door.
//! 3. The door executes the action and reports the result back to the
//!    elevator.
//! 4. The elevator confirms the outcome to the user.
//! 5. On **OpenDoor**, the elevator automatically closes the door afterward
//!    (the full open-wait-close cycle from the original protocol).
//!
//! The original implementation used infinite mutually recursive session types
//! (the user continuously selected commands in an unbounded loop, and the
//! elevator/door state machine cycled through open/close/stop transitions
//! without any `End` state). This version models a single command cycle with
//! the automatic close-after-open behavior, demonstrating the same three-role
//! topology and choice-based coordination in a form the `choreography!` macro
//! can project.
//!
//! ```text
//! protocol Elevator =
//!   roles U, D, E
//!   choice U at
//!     | OpenDoor =>
//!         U -> E : OpenDoor
//!         E -> D : OpenDoor
//!         D -> E : DoorOpened
//!         E -> U : DoorOpened
//!         E -> D : CloseDoor
//!         D -> E : DoorClosed
//!         E -> U : DoorClosed
//!     | CloseDoor =>
//!         U -> E : CloseDoor
//!         E -> D : CloseDoor
//!         D -> E : DoorClosed
//!         E -> U : DoorClosed
//! ```
//!
//! Uses the `choreography!` macro to derive session types, roles, messages,
//! and channel wiring from the global protocol specification.
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
#![allow(missing_docs)]

use futures::{executor, try_join};
use std::error::Error;
use telltale::try_session;
use telltale_macros::choreography;

choreography! {
    protocol Elevator {
        roles U, D, E;

        choice U at {
            | OpenDoor => {
                U -> E : OpenDoor;
                E -> D : OpenDoor;
                D -> E : DoorOpened;
                E -> U : DoorOpened;
                // Elevator auto-closes door after opening
                E -> D : CloseDoor;
                D -> E : DoorClosed;
                E -> U : DoorClosed;
            }
            | CloseDoor => {
                U -> E : CloseDoor;
                E -> D : CloseDoor;
                D -> E : DoorClosed;
                E -> U : DoorClosed;
            }
        }
    }
}

// ---------------------------------------------------------------------------
// User
// ---------------------------------------------------------------------------

async fn user(role: &mut U) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: USession<'_, _>| async {
        // User decides to open the door
        println!("U: requesting door open");
        let s = s.select(OpenDoor).await?;

        // Wait for door to open
        let (DoorOpened, s) = s.receive().await?;
        println!("U: door is open");

        // Wait for automatic close
        let (DoorClosed, end) = s.receive().await?;
        println!("U: door has closed");

        Ok(((), end))
    })
    .await
}

// ---------------------------------------------------------------------------
// Door
// ---------------------------------------------------------------------------

async fn door(role: &mut D) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: DSession<'_, _>| async {
        match s.branch().await? {
            DChoice1::OpenDoor(OpenDoor, s) => {
                println!("D: opening door");
                let s = s.send(DoorOpened).await?;
                println!("D: door opened");

                // Auto-close command from elevator
                let (CloseDoor, s) = s.receive().await?;
                println!("D: closing door (auto-close)");
                let end = s.send(DoorClosed).await?;
                println!("D: door closed");

                Ok(((), end))
            }
            DChoice1::CloseDoor(CloseDoor, s) => {
                println!("D: closing door");
                let end = s.send(DoorClosed).await?;
                println!("D: door closed");

                Ok(((), end))
            }
        }
    })
    .await
}

// ---------------------------------------------------------------------------
// Elevator
// ---------------------------------------------------------------------------

async fn elevator(role: &mut E) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: ESession<'_, _>| async {
        match s.branch().await? {
            EChoice1::OpenDoor(OpenDoor, s) => {
                // Forward open command to door
                println!("E: received open request");
                let s = s.send(OpenDoor).await?;

                // Wait for door to confirm opened
                let (DoorOpened, s) = s.receive().await?;
                println!("E: door opened, notifying user");
                let s = s.send(DoorOpened).await?;

                // Auto-close: tell door to close
                println!("E: auto-closing door");
                let s = s.send(CloseDoor).await?;

                let (DoorClosed, s) = s.receive().await?;
                println!("E: door closed, notifying user");
                let end = s.send(DoorClosed).await?;

                Ok(((), end))
            }
            EChoice1::CloseDoor(CloseDoor, s) => {
                // Forward close command to door
                println!("E: received close request");
                let s = s.send(CloseDoor).await?;

                let (DoorClosed, s) = s.receive().await?;
                println!("E: door closed, notifying user");
                let end = s.send(DoorClosed).await?;

                Ok(((), end))
            }
        }
    })
    .await
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    let Roles(mut u, mut d, mut e) = Roles::default();
    executor::block_on(async {
        try_join!(user(&mut u), door(&mut d), elevator(&mut e)).unwrap();
    });
    println!("\nElevator protocol completed successfully");
}
