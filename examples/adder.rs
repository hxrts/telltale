//! Recursive adder protocol between a client and server.
//!
//! This is a projection-surface example: `tell!` owns the protocol-visible
//! loop and branching structure, while Rust only provides the client's local
//! request plan and the server's arithmetic.

use futures::{executor, try_join};
use std::error::Error;
use telltale::{tell, try_session};

#[derive(Clone, Copy, Debug)]
struct AddRequest {
    left: i32,
    right: i32,
}

const CLIENT_PLAN: &[AddRequest] = &[
    AddRequest { left: 2, right: 3 },
    AddRequest { left: 4, right: 5 },
    AddRequest { left: 6, right: 7 },
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

async fn client(role: &mut C, initial: i32, plan: &[AddRequest]) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: CSession<'_, _>| async {
        let mut s = s.send(Hello(initial)).await?;

        for request in plan {
            let add_session = s.select(Add(request.left)).await?;
            let add_session = add_session.send(Add(request.right)).await?;
            let (Sum(total), next) = add_session.receive().await?;
            println!("{initial} + {} + {} = {total}", request.left, request.right);
            assert_eq!(total, initial + request.left + request.right);
            s = next;
        }

        let bye_session = s.select(Bye).await?;
        let (Bye, end) = bye_session.receive().await?;
        Ok(((), end))
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
    executor::block_on(async { try_join!(client(&mut c, 1, CLIENT_PLAN), server(&mut s)) })?;
    Ok(())
}
