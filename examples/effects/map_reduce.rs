//! Fan-out/fan-in work distribution protocol.
//!
//! This is an effect-boundary example: `tell!` owns the fan-out/fan-in
//! structure, while generated effect traits model work assignment and worker
//! computation.

use futures::{executor, try_join};
use std::{error::Error, result};
use telltale::{tell, try_session};

type Result<T> = result::Result<T, Box<dyn Error>>;

tell! {
    -- // Execution profile keeps the example on the proof-backed effect boundary.
    profile Replay fairness eventual admissibility replay escalation_window bounded

    -- // Work items assigned by the coordinator host.
    type alias WorkAssignment =
    {
      w1 : Int
      w2 : Int
      w3 : Int
      w4 : Int
    }

    -- // Coordinator host provides one batch of work items.
    effect CoordinatorPlan
      command assign : Session -> WorkAssignment
      {
        class : best_effort
        progress : immediate
        region : session
        agreement_use : none
        reentrancy : allow
      }

    -- // Worker host computes one partial result from one work item.
    effect WorkerCompute
      command process : Int -> Int
      {
        class : best_effort
        progress : immediate
        region : session
        agreement_use : none
        reentrancy : allow
      }

    -- // Coordinator fans work out to all workers, then collects partial results.
    protocol MapReduce uses CoordinatorPlan, WorkerCompute under Replay =
      roles Coordinator, W1, W2, W3, W4
      -- // Fan-out stage distributes one work item per worker.
      Coordinator -> W1 : Work of i32
      Coordinator -> W2 : Work of i32
      Coordinator -> W3 : Work of i32
      Coordinator -> W4 : Work of i32
      -- // Fan-in stage gathers the computed partial results.
      W1 -> Coordinator : PartialResult of i32
      W2 -> Coordinator : PartialResult of i32
      W3 -> Coordinator : PartialResult of i32
      W4 -> Coordinator : PartialResult of i32
}

use MapReduce::effects;
use MapReduce::sessions::*;

struct CoordinatorHost {
    assignment: effects::WorkAssignment,
}

#[derive(Default)]
struct WorkerHost;

impl effects::CoordinatorPlan for CoordinatorHost {
    fn assign(&mut self, _input: effects::Session) -> effects::WorkAssignment {
        self.assignment.clone()
    }
}

impl effects::WorkerCompute for WorkerHost {
    fn process(&mut self, input: i64) -> i64 {
        input * 2
    }
}

async fn coordinator(role: &mut Coordinator, host: &mut CoordinatorHost) -> Result<i32> {
    try_session(role, |s: CoordinatorSession<'_, _>| async {
        let assignment =
            effects::CoordinatorPlan::assign(host, effects::Session::new("map-reduce"));
        let s = s.send(Work(i32::try_from(assignment.w1)?)).await?;
        let s = s.send(Work(i32::try_from(assignment.w2)?)).await?;
        let s = s.send(Work(i32::try_from(assignment.w3)?)).await?;
        let s = s.send(Work(i32::try_from(assignment.w4)?)).await?;

        let (PartialResult(r1), s) = s.receive().await?;
        let (PartialResult(r2), s) = s.receive().await?;
        let (PartialResult(r3), s) = s.receive().await?;
        let (PartialResult(r4), s) = s.receive().await?;

        Ok((r1 + r2 + r3 + r4, s))
    })
    .await
}

async fn worker_1(role: &mut W1, host: &mut WorkerHost) -> Result<()> {
    try_session(role, |s: W1Session<'_, _>| async {
        let (Work(x), s) = s.receive().await?;
        let s = s
            .send(PartialResult(i32::try_from(
                effects::WorkerCompute::process(host, x.into()),
            )?))
            .await?;
        Ok(((), s))
    })
    .await
}

async fn worker_2(role: &mut W2, host: &mut WorkerHost) -> Result<()> {
    try_session(role, |s: W2Session<'_, _>| async {
        let (Work(x), s) = s.receive().await?;
        let s = s
            .send(PartialResult(i32::try_from(
                effects::WorkerCompute::process(host, x.into()),
            )?))
            .await?;
        Ok(((), s))
    })
    .await
}

async fn worker_3(role: &mut W3, host: &mut WorkerHost) -> Result<()> {
    try_session(role, |s: W3Session<'_, _>| async {
        let (Work(x), s) = s.receive().await?;
        let s = s
            .send(PartialResult(i32::try_from(
                effects::WorkerCompute::process(host, x.into()),
            )?))
            .await?;
        Ok(((), s))
    })
    .await
}

async fn worker_4(role: &mut W4, host: &mut WorkerHost) -> Result<()> {
    try_session(role, |s: W4Session<'_, _>| async {
        let (Work(x), s) = s.receive().await?;
        let s = s
            .send(PartialResult(i32::try_from(
                effects::WorkerCompute::process(host, x.into()),
            )?))
            .await?;
        Ok(((), s))
    })
    .await
}

fn main() -> Result<()> {
    let Roles(mut coord, mut w1, mut w2, mut w3, mut w4) = Roles::default();
    let mut coordinator_host = CoordinatorHost {
        assignment: effects::WorkAssignment {
            w1: 10,
            w2: 20,
            w3: 30,
            w4: 40,
        },
    };
    let mut worker_1_host = WorkerHost;
    let mut worker_2_host = WorkerHost;
    let mut worker_3_host = WorkerHost;
    let mut worker_4_host = WorkerHost;
    println!(
        "execution profiles = {:?}",
        MapReduce::proof_status::EXECUTION_PROFILES
    );
    println!(
        "session projectable = {}",
        MapReduce::proof_status::SESSION_PROJECTABLE
    );

    let (total, _, _, _, _) = executor::block_on(async {
        try_join!(
            coordinator(&mut coord, &mut coordinator_host),
            worker_1(&mut w1, &mut worker_1_host),
            worker_2(&mut w2, &mut worker_2_host),
            worker_3(&mut w3, &mut worker_3_host),
            worker_4(&mut w4, &mut worker_4_host),
        )
    })?;

    println!("Total: {total}");
    assert_eq!(total, 200);
    Ok(())
}
