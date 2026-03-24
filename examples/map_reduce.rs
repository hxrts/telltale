//! Fan-out/fan-in work distribution protocol.
//!
//! A coordinator distributes workloads to four workers, each computes a partial
//! result (doubling its input), and returns it. The coordinator collects all
//! partial results and sums them.
//!
//! DSL equivalent (`.tell` syntax):
//!
//! ```tell
//! protocol MapReduce {
//!     roles Coordinator, W1, W2, W3, W4;
//!     Coordinator -> W1: Work(i32);
//!     Coordinator -> W2: Work(i32);
//!     Coordinator -> W3: Work(i32);
//!     Coordinator -> W4: Work(i32);
//!     W1 -> Coordinator: PartialResult(i32);
//!     W2 -> Coordinator: PartialResult(i32);
//!     W3 -> Coordinator: PartialResult(i32);
//!     W4 -> Coordinator: PartialResult(i32);
//! }
//! ```
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
#![allow(missing_docs)]

use futures::{executor, try_join};
use std::{error::Error, result};
use telltale::try_session;
use telltale_macros::choreography;

type Result<T> = result::Result<T, Box<dyn Error>>;

choreography! {
    protocol MapReduce {
        roles Coordinator, W1, W2, W3, W4;
        Coordinator -> W1: Work(i32);
        Coordinator -> W2: Work(i32);
        Coordinator -> W3: Work(i32);
        Coordinator -> W4: Work(i32);
        W1 -> Coordinator: PartialResult(i32);
        W2 -> Coordinator: PartialResult(i32);
        W3 -> Coordinator: PartialResult(i32);
        W4 -> Coordinator: PartialResult(i32);
    }
}

async fn coordinator(role: &mut Coordinator) -> Result<i32> {
    try_session(role, |s: CoordinatorSession<'_, _>| async {
        // Fan out: distribute work items to all workers.
        let s = s.send(Work(10)).await?;
        let s = s.send(Work(20)).await?;
        let s = s.send(Work(30)).await?;
        let s = s.send(Work(40)).await?;

        // Fan in: collect partial results from all workers.
        let (PartialResult(r1), s) = s.receive().await?;
        let (PartialResult(r2), s) = s.receive().await?;
        let (PartialResult(r3), s) = s.receive().await?;
        let (PartialResult(r4), s) = s.receive().await?;

        let total = r1 + r2 + r3 + r4;
        Ok((total, s))
    })
    .await
}

async fn worker_1(role: &mut W1) -> Result<()> {
    try_session(role, |s: W1Session<'_, _>| async {
        let (Work(x), s) = s.receive().await?;
        let s = s.send(PartialResult(x * 2)).await?;
        Ok(((), s))
    })
    .await
}

async fn worker_2(role: &mut W2) -> Result<()> {
    try_session(role, |s: W2Session<'_, _>| async {
        let (Work(x), s) = s.receive().await?;
        let s = s.send(PartialResult(x * 2)).await?;
        Ok(((), s))
    })
    .await
}

async fn worker_3(role: &mut W3) -> Result<()> {
    try_session(role, |s: W3Session<'_, _>| async {
        let (Work(x), s) = s.receive().await?;
        let s = s.send(PartialResult(x * 2)).await?;
        Ok(((), s))
    })
    .await
}

async fn worker_4(role: &mut W4) -> Result<()> {
    try_session(role, |s: W4Session<'_, _>| async {
        let (Work(x), s) = s.receive().await?;
        let s = s.send(PartialResult(x * 2)).await?;
        Ok(((), s))
    })
    .await
}

fn main() {
    let Roles(mut coord, mut w1, mut w2, mut w3, mut w4) = Roles::default();

    let (total, _, _, _, _) = executor::block_on(async {
        try_join!(
            coordinator(&mut coord),
            worker_1(&mut w1),
            worker_2(&mut w2),
            worker_3(&mut w3),
            worker_4(&mut w4),
        )
        .unwrap()
    });

    println!("Total: {total}");
    assert_eq!(total, 200);
}
