//! Recursive adder protocol between a client and server.
//!
//! The client sends an initial value, then repeatedly chooses to either add
//! another pair of numbers (receiving back the running sum) or say goodbye.
//! The recursive `Select`/`Branch` loop (Add -> Add -> Sum -> choose again)
//! encodes an unbounded number of additions terminated by a `Bye` exit.
//! Uses the `tell!` macro to derive session types, roles, messages,
//! and channel wiring from the global protocol specification.

use futures::{executor, try_join};
use std::error::Error;
use telltale::{tell, try_session};

#[derive(Clone, Copy, Debug)]
enum AdderAction {
    Add(i32, i32),
    Bye,
}

const CLIENT_PLAN: &[AdderAction] = &[
    AdderAction::Add(2, 3),
    AdderAction::Add(4, 5),
    AdderAction::Add(6, 7),
    AdderAction::Bye,
];

tell! {
    -- // Client opens the session, then loops through add-or-bye decisions.
    protocol Adder =
      roles C, S
      C -> S : Hello(i32)
      -- // Recursive request loop for repeated additions.
      rec adder_loop
        choice C at
          -- // Send two addends and receive the computed running sum.
          | Add =>
            C -> S : Add(i32)
            C -> S : Add(i32)
            S -> C : Sum(i32)
            continue adder_loop
          -- // Terminate the session cleanly once no more additions remain.
          | Bye =>
            C -> S : Bye
            S -> C : Bye
}

use Adder::sessions::*;

// ---------------------------------------------------------------------------
// Endpoint implementations
// ---------------------------------------------------------------------------

async fn client(role: &mut C) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: CSession<'_, _>| async {
        let initial = 1;
        let mut s = s.send(Hello(initial)).await?;

        for action in CLIENT_PLAN {
            match *action {
                AdderAction::Add(left, right) => {
                    let add_session = s.select(Add(left)).await?;
                    let add_session = add_session.send(Add(right)).await?;
                    let (Sum(total), next) = add_session.receive().await?;
                    println!("{initial} + {left} + {right} = {total}");
                    assert_eq!(total, initial + left + right);
                    s = next;
                }
                AdderAction::Bye => {
                    let bye_session = s.select(Bye).await?;
                    let (Bye, end) = bye_session.receive().await?;
                    return Ok(((), end));
                }
            }
        }

        unreachable!("the client plan must terminate with Bye")
    })
    .await
}

async fn server(role: &mut S) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: SSession<'_, _>| async {
        let (Hello(u), mut s) = s.receive().await?;
        let s = loop {
            s = match s.branch().await? {
                SChoice1::Add(Add(v), s) => {
                    let (Add(w), s) = s.receive().await?;
                    s.send(Sum(u + v + w)).await?
                }
                SChoice1::Bye(Bye, s) => break s.send(Bye).await?,
            };
        };

        Ok(((), s))
    })
    .await
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() -> Result<(), Box<dyn Error>> {
    let Roles(mut c, mut s) = Roles::default();
    executor::block_on(async { try_join!(client(&mut c), server(&mut s)) })?;
    Ok(())
}
