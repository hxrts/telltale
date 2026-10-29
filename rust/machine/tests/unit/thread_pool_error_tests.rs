use super::thread_pool_build_error;
use crate::engine::ProtocolMachineError;
use rayon::ThreadPoolBuilder;
use std::error::Error;
use std::sync::{mpsc, Arc, Mutex};

#[derive(Debug)]
struct OriginalSpawnFailure(Arc<()>);

impl std::fmt::Display for OriginalSpawnFailure {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str("original worker spawn refusal")
    }
}

impl Error for OriginalSpawnFailure {}

fn original_failure(identity: &Arc<()>) -> std::io::Error {
    std::io::Error::other(OriginalSpawnFailure(Arc::clone(identity)))
}

fn assert_original_source(error: &ProtocolMachineError, identity: &Arc<()>) {
    assert!(matches!(
        error,
        ProtocolMachineError::ThreadPoolBuild { .. }
    ));
    let native = error
        .source()
        .and_then(|source| source.downcast_ref::<rayon::ThreadPoolBuildError>())
        .expect("actual Rayon constructor cause");
    let io = native
        .source()
        .and_then(|source| source.downcast_ref::<std::io::Error>())
        .expect("actual original native I/O failure");
    let original = io
        .get_ref()
        .and_then(|source| source.downcast_ref::<OriginalSpawnFailure>())
        .expect("original supplied native error, without reconstruction");
    assert!(Arc::ptr_eq(&original.0, identity));
    assert_eq!(
        error.to_string(),
        format!("thread pool build failed: {native}")
    );
}

#[test]
fn first_worker_spawn_refusal_preserves_original_native_source() {
    let identity = Arc::new(());
    let original = Arc::clone(&identity);
    let builder = ThreadPoolBuilder::new()
        .num_threads(1)
        .spawn_handler(move |_| Err(original_failure(&original)));
    let error = match builder.build().map_err(thread_pool_build_error) {
        Ok(pool) => {
            drop(pool);
            panic!("the actual supplied spawn handler must refuse");
        }
        Err(error) => error,
    };
    assert_original_source(&error, &identity);
}

#[test]
fn later_worker_spawn_refusal_preserves_source_after_original_worker_join() {
    let identity = Arc::new(());
    let original = Arc::clone(&identity);
    let workers = Arc::new(Mutex::new(Vec::new()));
    let retained_workers = Arc::clone(&workers);
    let (entered, acknowledged) = mpsc::channel();
    let (finished, disposed) = mpsc::channel();
    let mut started = false;
    let builder = ThreadPoolBuilder::new()
        .num_threads(2)
        .spawn_handler(move |thread| {
            if started {
                return Err(original_failure(&original));
            }
            started = true;
            let entered = entered.clone();
            let finished = finished.clone();
            let worker = std::thread::Builder::new().spawn(move || {
                entered.send(()).expect("acknowledge actual first worker");
                thread.run();
                finished.send(()).expect("acknowledge actual worker exit");
            })?;
            retained_workers
                .lock()
                .expect("test owns original join handles")
                .push(worker);
            acknowledged.recv().map_err(std::io::Error::other)?;
            Ok(())
        });
    let error = match builder.build().map_err(thread_pool_build_error) {
        Ok(pool) => {
            // Release even an unexpectedly successful pool before joining its
            // actual workers, otherwise the fixture would wait on a live pool.
            drop(pool);
            None
        }
        Err(error) => Some(error),
    };
    // The test owns the real native handles independently of the constructor.
    // Join before assertions; a constructor Err alone acknowledges no teardown.
    let joined = std::mem::take(&mut *workers.lock().expect("original worker handles"))
        .into_iter()
        .map(std::thread::JoinHandle::join)
        .collect::<Vec<_>>();
    let exits = disposed.try_iter().count();
    assert_eq!(joined.len(), 1, "one real worker existed before refusal");
    assert!(joined.into_iter().all(|result| result.is_ok()));
    assert_eq!(
        exits, 1,
        "actual worker termination was independently observed"
    );
    let error = error.expect("the actual second spawn must refuse");
    assert_original_source(&error, &identity);
}
