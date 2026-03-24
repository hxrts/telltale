//! Alternating bit protocol using the `tell!` macro.
//!
//! The alternating bit protocol is a simple reliable-transfer scheme:
//!   - Sender transmits data frames tagged with alternating bits (D0, D1).
//!   - Receiver acknowledges with the matching bit on success or the wrong
//!     bit to signal a mismatch.
//!
//! The original protocol uses retransmission loops (infinite recursive
//! session types) which cannot be expressed in the projected session surface.
//! This version models a single pass through both frames: S sends D0,
//! R decides success (Ack) or mismatch (Nack); on success, S sends D1
//! and R decides again. Ack carries the received value back as
//! confirmation; Nack signals the bit mismatch.
use futures::{executor, try_join};
use std::{error::Error, result};
use telltale::{tell, try_session};

type Result<T> = result::Result<T, Box<dyn Error>>;

#[derive(Clone, Copy, Debug)]
enum AckPolicy {
    AckBoth,
    NackFirst,
    NackSecond,
}

fn receiver_policy() -> AckPolicy {
    match std::env::var("ALT_BIT_POLICY").ok().as_deref() {
        Some("nack-first") => AckPolicy::NackFirst,
        Some("nack-second") => AckPolicy::NackSecond,
        _ => AckPolicy::AckBoth,
    }
}

tell! {
    -- // Sender transmits frame 0, then the receiver decides whether to continue.
    protocol AlternatingBit =
      roles S, R
      S -> R : D0(i32)
      choice R at
        -- // Acknowledge frame 0, exchange frame 1, then decide again.
        | Ack0 =>
          R -> S : Ack(i32)
          S -> R : D1(i32)
          choice R at
            -- // Accept the second frame and complete the transfer.
            | Ack1 =>
              R -> S : Ack(i32)
            -- // Reject the second frame while still ending the session cleanly.
            | Nack1 =>
              R -> S : Nack(i32)
        -- // Reject the first frame immediately.
        | Nack0 =>
          R -> S : Nack(i32)
}

use AlternatingBit::sessions::*;

// ---------------------------------------------------------------------------
// Sender
// ---------------------------------------------------------------------------

async fn sender(role: &mut S, input: (i32, i32)) -> Result<()> {
    try_session(role, |s: SSession<'_, _>| async {
        // Send first frame with bit 0
        let s = s.send(D0(input.0)).await?;
        println!("S: sent D0({})", input.0);

        // Wait for receiver's decision on frame 0
        match s.branch().await? {
            SChoice1::Ack0(_, s) => {
                let (Ack(v), s) = s.receive().await?;
                println!("S: received Ack({v}) for bit 0");

                // Send second frame with bit 1
                let s = s.send(D1(input.1)).await?;
                println!("S: sent D1({})", input.1);

                // Wait for receiver's decision on frame 1
                match s.branch().await? {
                    SChoice2::Ack1(_, s) => {
                        let (Ack(v), s) = s.receive().await?;
                        println!("S: received Ack({v}) for bit 1 -- transfer complete");
                        Ok(((), s))
                    }
                    SChoice2::Nack1(_, s) => {
                        let (Nack(v), s) = s.receive().await?;
                        println!("S: received Nack({v}) -- bit mismatch on frame 1");
                        Ok(((), s))
                    }
                }
            }
            SChoice1::Nack0(_, s) => {
                let (Nack(v), s) = s.receive().await?;
                println!("S: received Nack({v}) -- bit mismatch on frame 0");
                Ok(((), s))
            }
        }
    })
    .await
}

// ---------------------------------------------------------------------------
// Receiver
// ---------------------------------------------------------------------------

async fn receiver(role: &mut R) -> Result<(i32, i32)> {
    try_session(role, |s: RSession<'_, _>| async {
        // Receive first frame (expecting bit 0)
        let (D0(x), s) = s.receive().await?;
        println!("R: received D0({x})");

        match receiver_policy() {
            AckPolicy::NackFirst => {
                let s = s.select(Nack0).await?;
                let end = s.send(Nack(x)).await?;
                println!("R: sent Nack({x}) for bit 0");
                Ok(((x, 0), end))
            }
            AckPolicy::AckBoth | AckPolicy::NackSecond => {
                let s = s.select(Ack0).await?;
                let s = s.send(Ack(x)).await?;
                println!("R: sent Ack({x}) for bit 0");

                // Receive second frame (expecting bit 1)
                let (D1(y), s) = s.receive().await?;
                println!("R: received D1({y})");

                match receiver_policy() {
                    AckPolicy::AckBoth => {
                        let s = s.select(Ack1).await?;
                        let s = s.send(Ack(y)).await?;
                        println!("R: sent Ack({y}) for bit 1 -- transfer complete");
                        Ok(((x, y), s))
                    }
                    AckPolicy::NackSecond => {
                        let s = s.select(Nack1).await?;
                        let s = s.send(Nack(y)).await?;
                        println!("R: sent Nack({y}) for bit 1");
                        Ok(((x, y), s))
                    }
                    AckPolicy::NackFirst => unreachable!("handled above"),
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
    let Roles(mut s, mut r) = Roles::default();

    let input = (1, 2);
    println!("input = {input:?}");

    let ((), output) = executor::block_on(async { try_join!(sender(&mut s, input), receiver(&mut r)) })?;
    println!("output = {output:?}");
    match receiver_policy() {
        AckPolicy::AckBoth => assert_eq!(input, output),
        AckPolicy::NackFirst => assert_eq!(output.0, input.0),
        AckPolicy::NackSecond => assert_eq!(output, input),
    }
    Ok(())
}
