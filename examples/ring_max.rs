//! Seven-node ring computing distributed maximum via the `choreography!` macro.
//!
//! Each node holds a local value. The ring forwards the running maximum around
//! the full cycle so that the initiator receives the global max.
//!
//! DSL equivalent (`*.tell`):
//!
//! ```tell
//! protocol RingMax {
//!     roles A, B, C, D, E, F, G;
//!     A -> B: Value(i32);
//!     B -> C: Value(i32);
//!     C -> D: Value(i32);
//!     D -> E: Value(i32);
//!     E -> F: Value(i32);
//!     F -> G: Value(i32);
//!     G -> A: Value(i32);
//! }
//! ```
//!
//! This protocol is purely linear (no branching or recursion), so the
//! `choreography!` macro can express it directly.
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
#![allow(missing_docs)]

use futures::{executor, try_join};
use std::{cmp, error::Error, result};
use telltale::try_session;
use telltale_macros::choreography;

type Result<T> = result::Result<T, Box<dyn Error>>;

choreography! {
    protocol RingMax {
        roles A, B, C, D, E, F, G;
        A -> B: Value(i32);
        B -> C: Value(i32);
        C -> D: Value(i32);
        D -> E: Value(i32);
        E -> F: Value(i32);
        F -> G: Value(i32);
        G -> A: Value(i32);
    }
}

/// A initiates the ring by sending its local value and receives the global max.
async fn node_a(role: &mut A, local: i32) -> Result<i32> {
    try_session(role, |s: ASession<'_, _>| async {
        let s = s.send(Value(local)).await?;
        let (Value(global_max), s) = s.receive().await?;
        Ok((global_max, s))
    })
    .await
}

/// B receives from A, computes max, and forwards to C.
async fn node_b(role: &mut B, local: i32) -> Result<()> {
    try_session(role, |s: BSession<'_, _>| async {
        let (Value(received), s) = s.receive().await?;
        let s = s.send(Value(cmp::max(local, received))).await?;
        Ok(((), s))
    })
    .await
}

/// C receives from B, computes max, and forwards to D.
async fn node_c(role: &mut C, local: i32) -> Result<()> {
    try_session(role, |s: CSession<'_, _>| async {
        let (Value(received), s) = s.receive().await?;
        let s = s.send(Value(cmp::max(local, received))).await?;
        Ok(((), s))
    })
    .await
}

/// D receives from C, computes max, and forwards to E.
async fn node_d(role: &mut D, local: i32) -> Result<()> {
    try_session(role, |s: DSession<'_, _>| async {
        let (Value(received), s) = s.receive().await?;
        let s = s.send(Value(cmp::max(local, received))).await?;
        Ok(((), s))
    })
    .await
}

/// E receives from D, computes max, and forwards to F.
async fn node_e(role: &mut E, local: i32) -> Result<()> {
    try_session(role, |s: ESession<'_, _>| async {
        let (Value(received), s) = s.receive().await?;
        let s = s.send(Value(cmp::max(local, received))).await?;
        Ok(((), s))
    })
    .await
}

/// F receives from E, computes max, and forwards to G.
async fn node_f(role: &mut F, local: i32) -> Result<()> {
    try_session(role, |s: FSession<'_, _>| async {
        let (Value(received), s) = s.receive().await?;
        let s = s.send(Value(cmp::max(local, received))).await?;
        Ok(((), s))
    })
    .await
}

/// G receives from F, computes max, and sends the final result back to A.
async fn node_g(role: &mut G, local: i32) -> Result<()> {
    try_session(role, |s: GSession<'_, _>| async {
        let (Value(received), s) = s.receive().await?;
        let s = s.send(Value(cmp::max(local, received))).await?;
        Ok(((), s))
    })
    .await
}

fn main() {
    let Roles(mut a, mut b, mut c, mut d, mut e, mut f, mut g) = Roles::default();

    let global_max = executor::block_on(async {
        let (result_a, (), (), (), (), (), ()) = try_join!(
            node_a(&mut a, 10),
            node_b(&mut b, 15),
            node_c(&mut c, 15),
            node_d(&mut d, 15),
            node_e(&mut e, 15),
            node_f(&mut f, 15),
            node_g(&mut g, 15),
        )
        .unwrap();
        result_a
    });

    println!("Global maximum: {global_max}");
    assert_eq!(global_max, 15);
}
