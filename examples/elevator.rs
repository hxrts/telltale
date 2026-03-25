//! Elevator controller with three-way coordination.
//!
//! This is an effect-boundary example: `tell!` owns the relay structure, while
//! generated effect traits model the user panel input and the physical door
//! motor operations.

use futures::{executor, try_join};
use std::error::Error;
use telltale::{tell, try_session};

tell! {
    -- // Host-side door action selected by the user.
    type DoorAction =
      | Open
      | Close

    -- // User-facing panel chooses one door action for this session.
    effect UserPanel
      command choose : Session -> DoorAction

    -- // Door motor realizes the physical open/close operations.
    effect DoorMotor
      command open : Unit -> Unit
      command close : Unit -> Unit

    -- // User chooses one door command and the elevator relays it to the door.
    protocol Elevator uses UserPanel, DoorMotor =
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

use Elevator::effects;
use Elevator::sessions::*;

#[derive(Clone, Debug)]
struct UserHost {
    command: effects::DoorAction,
}

#[derive(Default)]
struct DoorHost {
    actions: Vec<&'static str>,
}

impl effects::UserPanel for UserHost {
    fn choose(&mut self, _input: effects::Session) -> effects::DoorAction {
        self.command.clone()
    }
}

impl effects::DoorMotor for DoorHost {
    fn open(&mut self, _input: ()) {
        self.actions.push("open");
    }

    fn close(&mut self, _input: ()) {
        self.actions.push("close");
    }
}

fn user_command() -> effects::DoorAction {
    match std::env::var("ELEVATOR_COMMAND").ok().as_deref() {
        Some("close") => effects::DoorAction::Close,
        _ => effects::DoorAction::Open,
    }
}

async fn user(role: &mut U, host: &mut UserHost) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: USession<'_, _>| async {
        match effects::UserPanel::choose(host, effects::Session::new("elevator")) {
            effects::DoorAction::Open => {
                println!("U: requesting door open");
                let s = s.select(OpenDoor).await?;
                let (DoorOpened, s) = s.receive().await?;
                println!("U: door is open");
                let (DoorClosed, end) = s.receive().await?;
                println!("U: door has closed");
                Ok(((), end))
            }
            effects::DoorAction::Close => {
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

async fn door(role: &mut D, host: &mut DoorHost) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: DSession<'_, _>| async {
        match s.branch().await? {
            DChoice1::OpenDoor(OpenDoor, s) => {
                println!("D: opening door");
                effects::DoorMotor::open(host, ());
                let s = s.send(DoorOpened).await?;
                println!("D: door opened");

                let (CloseDoor, s) = s.receive().await?;
                println!("D: closing door (auto-close)");
                effects::DoorMotor::close(host, ());
                let end = s.send(DoorClosed).await?;
                println!("D: door closed");

                Ok(((), end))
            }
            DChoice1::CloseDoor(CloseDoor, s) => {
                println!("D: closing door");
                effects::DoorMotor::close(host, ());
                let end = s.send(DoorClosed).await?;
                println!("D: door closed");

                Ok(((), end))
            }
        }
    })
    .await
}

async fn elevator(role: &mut E) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: ESession<'_, _>| async {
        match s.branch().await? {
            EChoice1::OpenDoor(OpenDoor, s) => {
                println!("E: received open request");
                let s = s.send(OpenDoor).await?;

                let (DoorOpened, s) = s.receive().await?;
                println!("E: door opened, notifying user");
                let s = s.send(DoorOpened).await?;

                println!("E: auto-closing door");
                let s = s.send(CloseDoor).await?;

                let (DoorClosed, s) = s.receive().await?;
                println!("E: door closed, notifying user");
                let end = s.send(DoorClosed).await?;

                Ok(((), end))
            }
            EChoice1::CloseDoor(CloseDoor, s) => {
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

fn main() -> Result<(), Box<dyn Error>> {
    let Roles(mut u, mut d, mut e) = Roles::default();
    let mut user_host = UserHost {
        command: user_command(),
    };
    let mut door_host = DoorHost::default();
    executor::block_on(async {
        try_join!(user(&mut u, &mut user_host), door(&mut d, &mut door_host), elevator(&mut e))
    })?;
    println!("\nElevator protocol completed successfully");
    Ok(())
}
