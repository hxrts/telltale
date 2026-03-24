//! Double buffering example demonstrating concurrent data transfer.
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
#![allow(missing_docs)]

use futures::{
    executor::{self, ThreadPool},
    try_join, FutureExt,
};
use std::{error::Error, future::Future, marker, result};
use telltale::try_session;
use telltale_macros::choreography;

type Result<T> = result::Result<T, Box<dyn Error + marker::Send + Sync>>;

choreography! {
    protocol DoubleBuffering {
        roles S, K, T;
        K -> S: Ready;
        S -> K: Copy(i32);
        T -> K: Ready;
        K -> T: Copy(i32);
        K -> S: Ready;
        S -> K: Copy(i32);
        T -> K: Ready;
        K -> T: Copy(i32);
    }
}

async fn source(role: &mut S, input: (i32, i32)) -> Result<()> {
    try_session(role, |s: SSession<'_, _>| async {
        let (Ready, s) = s.receive().await?;
        let s = s.send(Copy(input.0)).await?;

        let (Ready, s) = s.receive().await?;
        let s = s.send(Copy(input.1)).await?;

        Ok(((), s))
    })
    .await
}

async fn kernel(role: &mut K) -> Result<()> {
    try_session(role, |s: KSession<'_, _>| async {
        let s = s.send(Ready).await?;
        let (Copy(x), s) = s.receive().await?;
        let (Ready, s) = s.receive().await?;
        let s = s.send(Copy(x)).await?;

        let s = s.send(Ready).await?;
        let (Copy(y), s) = s.receive().await?;
        let (Ready, s) = s.receive().await?;
        let s = s.send(Copy(y)).await?;

        Ok(((), s))
    })
    .await
}

async fn sink(role: &mut T) -> Result<(i32, i32)> {
    try_session(role, |s: TSession<'_, _>| async {
        let s = s.send(Ready).await?;
        let (Copy(x), s) = s.receive().await?;

        let s = s.send(Ready).await?;
        let (Copy(y), s) = s.receive().await?;

        Ok(((x, y), s))
    })
    .await
}

async fn spawn<F: Future + marker::Send + 'static>(pool: &ThreadPool, future: F) -> F::Output
where
    F::Output: marker::Send,
{
    let (future, handle) = future.remote_handle();
    pool.spawn_ok(future);
    handle.await
}

fn main() {
    let Roles(mut s, mut k, mut t) = Roles::default();
    let pool = ThreadPool::new().unwrap();

    let input = (1, 2);
    println!("input = {input:?}");

    let ((), (), output) = executor::block_on(async {
        try_join!(
            spawn(&pool, async move { source(&mut s, input).await }),
            spawn(&pool, async move { kernel(&mut k).await }),
            spawn(&pool, async move { sink(&mut t).await }),
        )
        .unwrap()
    });

    println!("output = {output:?}");
    assert_eq!(input, output);
}
