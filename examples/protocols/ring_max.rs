//! Five-node ring computing distributed maximum with broadcast announcement.
//!
//! Each node holds a local value. The ring forwards the running maximum around
//! the cycle. After the initiator receives the global max, it broadcasts the
//! result to all participants. This is a projection-surface example: `tell!`
//! owns the linear topology and the broadcast, while Rust provides each node's
//! local value and pure `max` computation.

use futures::{executor, try_join};
use std::{cmp, error::Error, result};
use telltale::{tell, try_session};

type Result<T> = result::Result<T, Box<dyn Error>>;

tell! {
    -- // The running maximum is forwarded around the five-node ring.
    -- // After A determines the global max, it broadcasts the result
    -- // to all participants.
    protocol RingMax =
      roles A, B, C, D, E
      A -> B : Value(i32)
      B -> C : Value(i32)
      C -> D : Value(i32)
      D -> E : Value(i32)
      E -> A : Value(i32)
      A ->* : Winner(i32)
}

use RingMax::sessions::*;

/// A initiates the ring by sending its local value, receives the global max,
/// then broadcasts the winner to all participants.
async fn node_a(role: &mut A, local: i32) -> Result<i32> {
    try_session(role, |s: ASession<'_, _>| async {
        let s = s.send(Value(local)).await?;
        let (Value(global_max), s) = s.receive().await?;
        let s = s.send(Winner(global_max)).await?;
        let s = s.send(Winner(global_max)).await?;
        let s = s.send(Winner(global_max)).await?;
        let s = s.send(Winner(global_max)).await?;
        Ok((global_max, s))
    })
    .await
}

/// B receives from A, computes max, and forwards to C. Then receives the
/// broadcast result from A.
async fn node_b(role: &mut B, local: i32) -> Result<i32> {
    try_session(role, |s: BSession<'_, _>| async {
        let (Value(received), s) = s.receive().await?;
        let s = s.send(Value(cmp::max(local, received))).await?;
        let (Winner(result), s) = s.receive().await?;
        Ok((result, s))
    })
    .await
}

/// C receives from B, computes max, and forwards to D. Then receives the
/// broadcast result from A.
async fn node_c(role: &mut C, local: i32) -> Result<i32> {
    try_session(role, |s: CSession<'_, _>| async {
        let (Value(received), s) = s.receive().await?;
        let s = s.send(Value(cmp::max(local, received))).await?;
        let (Winner(result), s) = s.receive().await?;
        Ok((result, s))
    })
    .await
}

/// D receives from C, computes max, and forwards to E. Then receives the
/// broadcast result from A.
async fn node_d(role: &mut D, local: i32) -> Result<i32> {
    try_session(role, |s: DSession<'_, _>| async {
        let (Value(received), s) = s.receive().await?;
        let s = s.send(Value(cmp::max(local, received))).await?;
        let (Winner(result), s) = s.receive().await?;
        Ok((result, s))
    })
    .await
}

/// E receives from D, computes max, and sends the final value back to A.
/// Then receives the broadcast result from A.
async fn node_e(role: &mut E, local: i32) -> Result<i32> {
    try_session(role, |s: ESession<'_, _>| async {
        let (Value(received), s) = s.receive().await?;
        let s = s.send(Value(cmp::max(local, received))).await?;
        let (Winner(result), s) = s.receive().await?;
        Ok((result, s))
    })
    .await
}

fn main() -> Result<()> {
    let Roles(mut a, mut b, mut c, mut d, mut e) = Roles::default();

    let (max_a, max_b, max_c, max_d, max_e) = executor::block_on(async {
        try_join!(
            node_a(&mut a, 3),
            node_b(&mut b, 12),
            node_c(&mut c, 7),
            node_d(&mut d, 15),
            node_e(&mut e, 9),
        )
    })?;

    println!("Global maximum: {max_a}");
    println!(
        "All nodes agree: {}",
        max_a == max_b && max_b == max_c && max_c == max_d && max_d == max_e
    );
    assert_eq!(max_a, 15);
    assert!(max_a == max_b && max_b == max_c && max_c == max_d && max_d == max_e);
    Ok(())
}
