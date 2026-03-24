//! Recursive adder protocol between a client and server.
//!
//! The client sends an initial value, then repeatedly chooses to either add
//! another pair of numbers (receiving back the running sum) or say goodbye.
//! The recursive `Select`/`Branch` loop (Add -> Add -> Sum -> choose again)
//! encodes an unbounded number of additions terminated by a `Bye` exit.
//!
//! ```tell
//! protocol Adder =
//!   roles C, S
//!   C -> S : Hello(i32)
//!   rec adder_loop
//!     choice C at
//!       | Add =>
//!         C -> S : Add(i32)
//!         C -> S : Add(i32)
//!         S -> C : Sum(i32)
//!         continue adder_loop
//!       | Bye =>
//!         C -> S : Bye
//!         S -> C : Bye
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
    protocol Adder =
      roles C, S
      C -> S : Hello(i32)
      rec adder_loop
        choice C at
          | Add =>
            C -> S : Add(i32)
            C -> S : Add(i32)
            S -> C : Sum(i32)
            continue adder_loop
          | Bye =>
            C -> S : Bye
            S -> C : Bye
}

// ---------------------------------------------------------------------------
// Endpoint implementations
// ---------------------------------------------------------------------------

async fn client(role: &mut C) -> Result<(), Box<dyn Error>> {
    try_session(role, |s: CSession<'_, _>| async {
        let s = s.send(Hello(1)).await?;

        let s = s.select(Add(2)).await?;
        let s = s.send(Add(3)).await?;
        let (Sum(f), s) = s.receive().await?;
        println!("1 + 2 + 3 = {f}");
        assert_eq!(f, 6);

        let s = s.select(Add(4)).await?;
        let s = s.send(Add(5)).await?;
        let (Sum(f), s) = s.receive().await?;
        println!("1 + 4 + 5 = {f}");
        assert_eq!(f, 10);

        let s = s.select(Add(6)).await?;
        let s = s.send(Add(7)).await?;
        let (Sum(f), s) = s.receive().await?;
        println!("1 + 6 + 7 = {f}");
        assert_eq!(f, 14);

        let s = s.select(Bye).await?;
        let (Bye, s) = s.receive().await?;

        Ok(((), s))
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

fn main() {
    let Roles(mut c, mut s) = Roles::default();
    executor::block_on(async {
        try_join!(client(&mut c), server(&mut s)).unwrap();
    });
}
