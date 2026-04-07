//! Three-party adder: A and B each contribute a number, C computes the sum.
//!
//! This is a projection-surface example: `tell!` owns the exchange pattern,
//! while Rust provides each participant's local addend and C's pure summation.

use futures::{executor, try_join};
use std::{error::Error, result};
use telltale::{tell, try_session};

type Result<T> = result::Result<T, Box<dyn Error>>;

tell! {
    -- // A and B exchange inputs, then both send them to C for summation.
    protocol Adder =
      roles A, B, C
      -- // A and B share their local addends with each other.
      A -> B : Add of i32
      B -> A : Add of i32
      -- // Both addends are delivered to C for computation.
      A -> C : Add of i32
      B -> C : Add of i32
      -- // C sends the resulting sum back to both participants.
      C -> A : Sum of i32
      C -> B : Sum of i32
}

use Adder::sessions::*;

async fn adder_a(role: &mut A, local: i32, expected: i32) -> Result<()> {
    try_session(role, |s: ASession<'_, _>| async {
        let s = s.send(Add(local)).await?;
        let (Add(y), s) = s.receive().await?;
        let s = s.send(Add(y)).await?;
        let (Sum(z), s) = s.receive().await?;
        println!("{local} + {y} = {z}");
        assert_eq!(z, expected);
        Ok(((), s))
    })
    .await
}

async fn adder_b(role: &mut B, local: i32, expected: i32) -> Result<()> {
    try_session(role, |s: BSession<'_, _>| async {
        let (Add(y), s) = s.receive().await?;
        let s = s.send(Add(local)).await?;
        let s = s.send(Add(y)).await?;
        let (Sum(z), s) = s.receive().await?;
        println!("{local} + {y} = {z}");
        assert_eq!(z, expected);
        Ok(((), s))
    })
    .await
}

async fn adder_c(role: &mut C) -> Result<()> {
    try_session(role, |s: CSession<'_, _>| async {
        let (Add(x), s) = s.receive().await?;
        let (Add(y), s) = s.receive().await?;
        let z = x + y;
        let s = s.send(Sum(z)).await?;
        Ok(((), s.send(Sum(z)).await?))
    })
    .await
}

fn main() -> Result<()> {
    let Roles(mut a, mut b, mut c) = Roles::default();
    let a_input = 2;
    let b_input = 3;
    let expected = a_input + b_input;
    executor::block_on(async {
        try_join!(
            adder_a(&mut a, a_input, expected),
            adder_b(&mut b, b_input, expected),
            adder_c(&mut c),
        )
    })?;
    Ok(())
}
