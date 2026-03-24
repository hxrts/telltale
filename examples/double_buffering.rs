//! Double buffering example demonstrating concurrent data transfer.

use futures::{
    executor::{self, ThreadPool},
    try_join, FutureExt,
};
use std::{error::Error, future::Future, marker, result};
use telltale::{tell, try_session};

type Result<T> = result::Result<T, Box<dyn Error + marker::Send + Sync>>;

tell! {
    -- // Two alternating ready/copy rounds model the double-buffer handoff.
    protocol DoubleBuffering =
      roles S, K, T
      -- // First buffer transfer from source through kernel to sink.
      K -> S : Ready
      S -> K : Copy(i32)
      T -> K : Ready
      K -> T : Copy(i32)
      -- // Second buffer transfer repeats the same pipeline.
      K -> S : Ready
      S -> K : Copy(i32)
      T -> K : Ready
      K -> T : Copy(i32)
}

use DoubleBuffering::sessions::*;

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

fn main() -> Result<()> {
    let Roles(mut s, mut k, mut t) = Roles::default();
    let pool = ThreadPool::new()?;

    let input = (1, 2);
    println!("input = {input:?}");

    let ((), (), output) = executor::block_on(async {
        try_join!(
            spawn(&pool, async move { source(&mut s, input).await }),
            spawn(&pool, async move { kernel(&mut k).await }),
            spawn(&pool, async move { sink(&mut t).await }),
        )
    })?;

    println!("output = {output:?}");
    assert_eq!(input, output);
    Ok(())
}
