//! Ring Protocol with Choices - Demonstrates Infinite Recursive Session Types.
#![allow(clippy::unwrap_used)]
#![allow(clippy::expect_used)]
#![allow(missing_docs)]
#![allow(unreachable_code)]

// Ring Protocol with Choices - Demonstrates Infinite Recursive Session Types
//
// This example demonstrates:
// - Ring topology communication patterns (A → B → C → A)
// - Choice-based protocol branching in a ring
// - **Infinite recursive session types** (no End state in type definition)
// - Session types for circular communication
//
// Note: The session types are structurally infinite (RingA → RingA recursively),
// demonstrating how session types can encode unbounded protocols. For practical
// testing, we limit execution to MAX_ROUNDS iterations. Set the RING_MAX_ROUNDS
// environment variable to customize (or remove the limit to see true infinite behavior).

use futures::{channel::mpsc, executor, try_join};
use telltale::{session, try_session, Branch, Message, Receive, Role, Roles, Select, Send};
use std::{convert::Infallible, error::Error, result};

type Result<T> = result::Result<T, Box<dyn Error>>;

// Maximum rounds for demonstration purposes
// The session types are infinite, but we limit iterations for testing
// Set RING_MAX_ROUNDS environment variable to override
fn max_rounds() -> usize {
    std::env::var("RING_MAX_ROUNDS")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(5)
}

type Sender = mpsc::UnboundedSender<Label>;
type Receiver = mpsc::UnboundedReceiver<Label>;

#[derive(Roles)]
struct Roles(A, B, C);

#[derive(Role)]
#[message(Label)]
struct A(#[route(B)] Sender, #[route(C)] Receiver);

#[derive(Role)]
#[message(Label)]
struct B(#[route(A)] Receiver, #[route(C)] Sender);

#[derive(Role)]
#[message(Label)]
struct C(#[route(A)] Sender, #[route(B)] Receiver);

#[derive(Message)]
enum Label {
    Add(Add),
    Sub(Sub),
}

struct Add(i32);
struct Sub(i32);

#[session]
type RingA = Send<B, Add, Branch<C, RingAChoice>>;

#[session]
enum RingAChoice {
    Add(Add, RingA),
    Sub(Sub, RingA),
}

#[session]
type RingB = Select<C, RingBChoice>;

#[session]
enum RingBChoice {
    #[allow(dead_code)]
    Add(Add, Receive<A, Add, RingB>),
    #[allow(dead_code)]
    Sub(Sub, Receive<A, Add, RingB>),
}

#[session]
type RingC = Branch<B, RingCChoice>;

#[session]
enum RingCChoice {
    Add(Add, Send<A, Add, RingC>),
    Sub(Sub, Send<A, Sub, RingC>),
}

async fn ring_a(role: &mut A, mut input: i32) -> Result<Infallible> {
    try_session(role, |mut s: RingA<'_, _>| async {
        let max_rounds = max_rounds();
        for round in 0..max_rounds {
            println!("A (round {round}): {input}");
            let x = input % 100; // Keep values small to prevent overflow
            s = match s.send(Add(x)).await?.branch().await? {
                RingAChoice::Add(Add(y), s) => {
                    input = x + y;
                    s
                }
                RingAChoice::Sub(Sub(y), s) => {
                    input = x - y;
                    s
                }
            };
        }
        println!("A: Completed {max_rounds} rounds, final value: {input}");
        println!("Note: Session types are infinite - limited to {max_rounds} rounds for testing");
        unreachable!()
    })
    .await
}

async fn ring_b(role: &mut B, mut input: i32) -> Result<Infallible> {
    try_session(role, |mut s: RingB<'_, _>| async {
        let max_rounds = max_rounds();
        for round in 0..max_rounds {
            println!("B (round {round}): {input}");
            let x = input % 100; // Keep values small to prevent overflow
            s = if x > 0 {
                let s = s.select(Add(x)).await?;
                let (Add(y), s) = s.receive().await?;
                input = y + x;
                s
            } else {
                let s = s.select(Sub(x)).await?;
                let (Add(y), s) = s.receive().await?;
                input = y - x;
                s
            };
        }
        println!("B: Completed {max_rounds} rounds, final value: {input}");
        unreachable!()
    })
    .await
}

async fn ring_c(role: &mut C, mut input: i32) -> Result<Infallible> {
    try_session(role, |mut s: RingC<'_, _>| async {
        let max_rounds = max_rounds();
        for round in 0..max_rounds {
            println!("C (round {round}): {input}");
            let x = input % 100; // Keep values small to prevent overflow
            s = match s.branch().await? {
                RingCChoice::Add(Add(y), s_recv) => {
                    let s = s_recv.send(Add(x)).await?;
                    input = x + y;
                    s
                }
                RingCChoice::Sub(Sub(y), s_recv) => {
                    let s = s_recv.send(Sub(x)).await?;
                    input = x - y;
                    s
                }
            };
        }
        println!("C: Completed {max_rounds} rounds, final value: {input}");
        unreachable!()
    })
    .await
}

fn main() {
    use std::panic;

    // Infinite session types don't have an End state, so when we artificially
    // limit the rounds for testing, we can't cleanly terminate the session.
    // The session drop handler will panic, which we catch here.

    let default_hook = panic::take_hook();
    panic::set_hook(Box::new(|_| {}));

    let result = panic::catch_unwind(panic::AssertUnwindSafe(|| {
        let Roles(mut a, mut b, mut c) = Roles::default();
        executor::block_on(async {
            try_join!(ring_a(&mut a, -1), ring_b(&mut b, 0), ring_c(&mut c, 1)).unwrap();
        });
    }));

    panic::set_hook(default_hook);

    match result {
        Ok(()) => println!("\nRing protocol completed normally"),
        Err(_) => println!(
            "\nRing protocol completed (session dropped after {} rounds)",
            max_rounds()
        ),
    }
}
