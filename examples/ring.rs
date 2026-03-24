//! Ring topology example demonstrating circular communication.
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
#![allow(missing_docs)]

use futures::{executor, try_join};
use std::{error::Error, result};
use telltale::try_session;
use telltale_macros::choreography;

type Result<T> = result::Result<T, Box<dyn Error>>;

choreography! {
    protocol Ring =
      roles A, B, C
      A -> B : Value(i32)
      B -> C : Value(i32)
      C -> A : Value(i32)
}

async fn ring_a(role: &mut A, input: i32) -> Result<i32> {
    let x = input;
    try_session(role, |s: ASession<'_, _>| async {
        let s = s.send(Value(x)).await?;
        let (Value(y), s) = s.receive().await?;
        Ok((x + y, s))
    })
    .await
}

async fn ring_b(role: &mut B, input: i32) -> Result<i32> {
    let x = input;
    try_session(role, |s: BSession<'_, _>| async {
        let (Value(y), s) = s.receive().await?;
        let s = s.send(Value(x)).await?;
        Ok((x + y, s))
    })
    .await
}

async fn ring_c(role: &mut C, input: i32) -> Result<i32> {
    let x = input;
    try_session(role, |s: CSession<'_, _>| async {
        let (Value(y), s) = s.receive().await?;
        let s = s.send(Value(x)).await?;
        Ok((x + y, s))
    })
    .await
}

fn main() {
    let Roles(mut a, mut b, mut c) = Roles::default();

    let input = (1, 2, 3);
    println!("input = {input:?}");

    let output = executor::block_on(async {
        try_join!(
            ring_a(&mut a, input.0),
            ring_b(&mut b, input.1),
            ring_c(&mut c, input.2),
        )
        .unwrap()
    });
    println!("output = {output:?}");
}
