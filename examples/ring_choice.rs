//! Ring protocol with per-hop choices and recursive session types.
//!
//! Three roles (A, B, C) form a ring where A decides on each round to
//! continue (sending an `Add` value around the ring) or stop (sending
//! `Stop` to terminate). The `rec`/`continue` construct produces
//! self-referential session types that the type system enforces at
//! compile time. Execution is bounded at runtime by a configurable
//! `RING_MAX_ROUNDS` limit (default 5).
//!
//! ```tell
//! protocol RingChoice =
//!   roles A, B, C
//!   rec ring_loop
//!     choice A at
//!       | Add =>
//!         A -> B : Add(i32)
//!         B -> C : Add(i32)
//!         C -> A : Add(i32)
//!         continue ring_loop
//!       | Stop =>
//!         A -> B : Stop
//!         B -> C : Stop
//! ```
//!
//! Uses the `choreography!` macro to derive session types, roles, messages,
//! and channel wiring from the global protocol specification.
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
#![allow(missing_docs)]

use futures::{executor, try_join};
use std::{error::Error, result};
use telltale::try_session;
use telltale_macros::choreography;

type Result<T> = result::Result<T, Box<dyn Error>>;

/// Maximum rounds for demonstration purposes.
/// Set `RING_MAX_ROUNDS` environment variable to override (default 5).
fn max_rounds() -> usize {
    std::env::var("RING_MAX_ROUNDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(5)
}

choreography! {
    protocol RingChoice =
      roles A, B, C
      rec ring_loop
        choice A at
          | Add =>
            A -> B : Add(i32)
            B -> C : Add(i32)
            C -> A : Add(i32)
            continue ring_loop
          | Stop =>
            A -> B : Stop
            B -> C : Stop
}

// ---------------------------------------------------------------------------
// Endpoint implementations
// ---------------------------------------------------------------------------

async fn ring_a(role: &mut A, mut input: i32) -> Result<()> {
    try_session(role, |mut s: ASession<'_, _>| async {
        let max = max_rounds();
        for round in 0..max {
            println!("A (round {round}): {input}");
            let x = input % 100; // keep values small to prevent overflow
            let recv_s = s.select(Add(x)).await?;
            let (Add(y), next) = recv_s.receive().await?;
            input = x + y;
            s = next;
        }
        println!("A: completed {max} rounds, final value: {input}");

        // Terminate the ring
        let end = s.select(Stop).await?;
        Ok(((), end))
    })
    .await
}

async fn ring_b(role: &mut B, mut input: i32) -> Result<()> {
    try_session(role, |mut s: BSession<'_, _>| async {
        loop {
            match s.branch().await? {
                BChoice1::Add(Add(y), send_s) => {
                    println!("B: received {y} from A, forwarding {input}");
                    let x = input % 100;
                    let next = send_s.send(Add(x)).await?;
                    input = y + x;
                    s = next;
                }
                BChoice1::Stop(Stop, send_s) => {
                    println!("B: received Stop, forwarding");
                    let end = send_s.send(Stop).await?;
                    return Ok(((), end));
                }
            }
        }
    })
    .await
}

async fn ring_c(role: &mut C, mut input: i32) -> Result<()> {
    try_session(role, |mut s: CSession<'_, _>| async {
        loop {
            match s.branch().await? {
                CChoice1::Add(Add(y), send_s) => {
                    println!("C: received {y} from B, forwarding {input}");
                    let x = input % 100;
                    let next = send_s.send(Add(x)).await?;
                    input = y + x;
                    s = next;
                }
                CChoice1::Stop(Stop, end) => {
                    println!("C: received Stop");
                    return Ok(((), end));
                }
            }
        }
    })
    .await
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

fn main() {
    let Roles(mut a, mut b, mut c) = Roles::default();
    executor::block_on(async {
        try_join!(ring_a(&mut a, -1), ring_b(&mut b, 0), ring_c(&mut c, 1)).unwrap();
    });
    println!("\nRing protocol completed after {} rounds", max_rounds());
}
