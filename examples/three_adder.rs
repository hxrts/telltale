//! Three-party adder: A and B each contribute a number, C computes the sum.
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
#![allow(missing_docs)]

use futures::{executor, try_join};
use std::{error::Error, result};
use telltale::try_session;
use telltale_macros::choreography;

type Result<T> = result::Result<T, Box<dyn Error>>;

choreography! {
    protocol Adder {
        roles A, B, C;
        A -> B: Add(i32);
        B -> A: Add(i32);
        A -> C: Add(i32);
        B -> C: Add(i32);
        C -> A: Sum(i32);
        C -> B: Sum(i32);
    }
}

async fn adder_a(role: &mut A) -> Result<()> {
    try_session(role, |s: ASession<'_, _>| async {
        let x = 2;
        let s = s.send(Add(x)).await?;
        let (Add(y), s) = s.receive().await?;
        let s = s.send(Add(y)).await?;
        let (Sum(z), s) = s.receive().await?;
        println!("{x} + {y} = {z}");
        assert_eq!(z, 5);
        Ok(((), s))
    })
    .await
}

async fn adder_b(role: &mut B) -> Result<()> {
    try_session(role, |s: BSession<'_, _>| async {
        let (Add(y), s) = s.receive().await?;
        let x = 3;
        let s = s.send(Add(x)).await?;
        let s = s.send(Add(y)).await?;
        let (Sum(z), s) = s.receive().await?;
        println!("{x} + {y} = {z}");
        assert_eq!(z, 5);
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

fn main() {
    let Roles(mut a, mut b, mut c) = Roles::default();
    executor::block_on(async {
        try_join!(adder_a(&mut a), adder_b(&mut b), adder_c(&mut c)).unwrap();
    });
}
