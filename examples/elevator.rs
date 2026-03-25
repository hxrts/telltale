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
//! This is a projection-surface example: `tell!` owns the command and relay
//! structure, while Rust provides the user's local command input and the
//! door/elevator host behavior.

use futures::{executor, try_join};
use std::error::Error;
use telltale::{tell, try_session};

#[derive(Clone, Copy, Debug)]
enum UserCommand {
    OpenDoor,
    CloseDoor,
}

fn user_command() -> UserCommand {
    match std::env::var("ELEVATOR_COMMAND").ok().as_deref() {
        Some("close") => UserCommand::CloseDoor,
        _ => UserCommand::OpenDoor,
    }
}

tell! {
    -- // User chooses one door command and the elevator relays it to the door.
    protocol Elevator =
      roles U, D, E
      choice U at
        -- // Open the door, confirm it, then auto-close and confirm closure.
        | OpenDoor =>
          U -> E : OpenDoor
          E -> D : OpenDoor
          D -> E : DoorOpened
          E -> U : DoorOpened
          E -> D : CloseDoor
          D -> E : DoorClosed
          E -> U : DoorClosed
        -- // Close the door directly and confirm the result.
        | CloseDoor =>
          U -> E : CloseDoor
          E -> D : CloseDoor
          D -> E : DoorClosed
          E -> U : DoorClosed
}

use Elevator::sessions::*;

// ---------------------------------------------------------------------------
// User
// ---------------------------------------------------------------------------

async fn user(role: &mut U, command: UserCommand) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: USession<'_, _>| async {
        match command {
            UserCommand::OpenDoor => {
                println!("U: requesting door open");
                let s = s.select(OpenDoor).await?;
                let (DoorOpened, s) = s.receive().await?;
                println!("U: door is open");
                let (DoorClosed, end) = s.receive().await?;
                println!("U: door has closed");
                Ok(((), end))
            }
            UserCommand::CloseDoor => {
                println!("U: requesting door close");
                let s = s.select(CloseDoor).await?;
                let (DoorClosed, end) = s.receive().await?;
                println!("U: door has closed");
                Ok(((), end))
            }
        }
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

fn main() -> Result<(), Box<dyn Error>> {
    let Roles(mut u, mut d, mut e) = Roles::default();
    let command = user_command();
    executor::block_on(async { try_join!(user(&mut u, command), door(&mut d), elevator(&mut e)) })?;
    println!("\nElevator protocol completed successfully");
    Ok(())
}
