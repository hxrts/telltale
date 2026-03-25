//! Ring protocol with per-hop choices and recursive session types.
//!
//! This is a projection-surface example: `tell!` owns the recursive branch
//! structure, while Rust supplies the initiator's runtime round bound and the
//! local arithmetic performed at each hop.

use futures::{executor, try_join};
use std::{error::Error, result};
use telltale::{tell, try_session};

type Result<T> = result::Result<T, Box<dyn Error>>;

/// Maximum rounds for demonstration purposes.
/// Set `RING_MAX_ROUNDS` environment variable to override (default 5).
fn max_rounds() -> usize {
    std::env::var("RING_MAX_ROUNDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(5)
}

tell! {
    -- // A controls whether the ring performs another add round or stops.
    protocol RingChoice =
      roles A, B, C
      -- // Recursive loop allows repeated circulation of accumulated values.
      rec ring_loop
        choice A at
          -- // Send one value around the ring and continue with the next round.
          | Add =>
            A -> B : Add(i32)
            B -> C : Add(i32)
            C -> A : Add(i32)
            continue ring_loop
          -- // Propagate the stop signal to terminate the ring.
          | Stop =>
            A -> B : Stop
            B -> C : Stop
}

use RingChoice::sessions::*;

// ---------------------------------------------------------------------------
// Endpoint implementations
// ---------------------------------------------------------------------------

async fn ring_a(role: &mut A, mut input: i32, rounds: usize) -> Result<()> {
    try_session(role, |mut s: ASession<'_, _>| async {
        for round in 0..rounds {
            println!("A (round {round}): {input}");
            let x = input % 100; // keep values small to prevent overflow
            let recv_s = s.select(Add(x)).await?;
            let (Add(y), next) = recv_s.receive().await?;
            input = x + y;
            s = next;
        }
        println!("A: completed {rounds} rounds, final value: {input}");

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

fn main() -> Result<()> {
    let Roles(mut a, mut b, mut c) = Roles::default();
    let rounds = max_rounds();
    executor::block_on(async {
        try_join!(
            ring_a(&mut a, -1, rounds),
            ring_b(&mut b, 0),
            ring_c(&mut c, 1)
        )
    })?;
    println!("\nRing protocol completed after {rounds} rounds");
    Ok(())
}
