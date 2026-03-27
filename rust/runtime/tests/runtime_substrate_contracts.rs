#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::expect_used)]

use std::path::Path;
use std::time::Duration;

use telltale_runtime::{
    spawn, spawn_local, AsyncClock, Clock, MockClock, Rng, SeededRng, SystemClock,
};
use tokio::sync::oneshot;
use tokio::task::LocalSet;

#[tokio::test]
async fn runtime_spawn_runs_futures_to_completion() {
    let (tx, rx) = oneshot::channel();
    spawn(async move {
        tx.send("spawned").expect("send spawn result");
    });
    assert_eq!(rx.await.expect("receive spawn result"), "spawned");
}

#[tokio::test(flavor = "current_thread")]
async fn runtime_spawn_local_runs_futures_inside_local_set() {
    let local = LocalSet::new();
    let (tx, rx) = oneshot::channel();

    local
        .run_until(async move {
            spawn_local(async move {
                tx.send("local").expect("send local spawn result");
            });
            assert_eq!(rx.await.expect("receive local spawn result"), "local");
        })
        .await;
}

#[tokio::test]
async fn runtime_clock_and_deterministic_test_doubles_have_distinct_contracts() {
    let system_clock = SystemClock;
    let before = system_clock.now();
    system_clock.sleep(Duration::from_millis(1)).await;
    let after = system_clock.now();
    assert!(
        after >= before,
        "system clock must remain monotonic across sleep",
    );
    system_clock.advance(Duration::from_secs(10));
    assert!(
        system_clock.now() >= after,
        "advancing SystemClock is a no-op and must not move time backwards",
    );

    let mock = MockClock::new();
    let start = mock.now();
    mock.sleep(Duration::from_millis(7)).await;
    assert_eq!(
        mock.elapsed(start),
        Duration::from_millis(7),
        "deterministic tests should use MockClock when exact time control matters",
    );

    let mut rng_a = SeededRng::new(7);
    let mut rng_b = SeededRng::new(7);
    assert_eq!(rng_a.next_u64(), rng_b.next_u64());
    assert_eq!(rng_a.next_u64(), rng_b.next_u64());
}

#[test]
fn deterministic_assurance_suites_do_not_depend_on_system_clock_or_rng() {
    let guarded_suites = [
        "rust/runtime/tests/authority_control_flow_corpus.rs",
        "rust/runtime/tests/generated_topology_public_path.rs",
        "rust/machine/tests/ownership_contracts.rs",
        "rust/machine/src/engine/runtime_exec/semantic_state.rs",
        "rust/simulator/tests/distributed.rs",
        "rust/bridge/tests/protocol_bundle_admission_contracts.rs",
    ];

    for relative in guarded_suites {
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("..")
            .join(relative);
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("read guarded suite {}: {err}", path.display()));
        assert!(
            !source.contains("SystemClock"),
            "deterministic assurance suite {} must not use SystemClock",
            path.display(),
        );
        assert!(
            !source.contains("SystemRng"),
            "deterministic assurance suite {} must not use SystemRng",
            path.display(),
        );
    }
}
