// Native worker lifetime is separate from session/protocol terminal state.
use std::any::Any;
use std::collections::VecDeque;
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;

/// An original native panic payload, retained without reconstruction.
/// Its typed occurrence distinguishes worker panic from join-operation unwind;
/// the latter does not establish that the original worker terminated.
pub struct NativeWorkerPanic {
    payload: Mutex<Box<dyn Any + Send>>,
}
impl std::fmt::Debug for NativeWorkerPanic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("NativeWorkerPanic { original_payload: retained }")
    }
}
impl NativeWorkerPanic {
    /// Nonconsuming observation of the actual original native panic payload.
    ///
    /// # Panics
    ///
    /// Propagates observer callback panics; the original payload remains retained
    /// and later nonblocking observations recover the poisoned guard.
    #[must_use = "the payload observation must be handled"]
    pub fn with_payload<T: Any, R>(&self, observe: impl FnOnce(&T) -> R) -> Option<R> {
        let payload = match self.payload.try_lock() {
            Ok(payload) => payload,
            Err(std::sync::TryLockError::Poisoned(poison)) => poison.into_inner(),
            Err(std::sync::TryLockError::WouldBlock) => return None,
        };
        payload.downcast_ref::<T>().map(observe)
    }
}

/// Issued only after every actual original native worker handle was joined.
/// This acknowledges worker termination, not successful protocol completion.
#[derive(Debug)]
pub struct NativeWorkerPoolDisposal {
    joined: usize,
    panics: Vec<Arc<NativeWorkerPanic>>,
}
impl NativeWorkerPoolDisposal {
    /// Number of original native handles whose join completed.
    #[must_use]
    pub fn joined_workers(&self) -> usize {
        self.joined
    }
    /// Actual native panic payloads retained independently of termination ACK.
    #[must_use]
    pub fn worker_panics(&self) -> &[Arc<NativeWorkerPanic>] {
        &self.panics
    }
}

pub(super) struct OwnedNativeWorkerPool {
    pool: rayon::ThreadPool,
    workers: Vec<JoinHandle<()>>,
}
impl OwnedNativeWorkerPool {
    pub(super) fn install<OP, R>(&self, op: OP) -> R
    where
        OP: FnOnce() -> R + Send,
        R: Send,
    {
        self.pool.install(op)
    }
    pub(super) fn is_original_worker(&self) -> bool {
        let actual = std::thread::current().id();
        self.workers
            .iter()
            .any(|worker| worker.thread().id() == actual)
    }
    pub(super) fn shutdown(
        self,
    ) -> Result<NativeWorkerPoolDisposal, Box<NativeWorkerPoolSettlement>> {
        self.shutdown_with_join(JoinHandle::join)
    }

    fn shutdown_with_join(
        self,
        join: impl FnMut(JoinHandle<()>) -> std::thread::Result<()>,
    ) -> Result<NativeWorkerPoolDisposal, Box<NativeWorkerPoolSettlement>> {
        let Self { pool, workers } = self;
        // Dropping Rayon requests termination. Only original joins acknowledge it.
        drop(pool);
        let settlement = Box::new(NativeWorkerPoolSettlement::new(workers));
        if settlement.settle_with_join(join).is_err() {
            return Err(settlement);
        }
        settlement.into_disposal()
    }
}
#[cfg(all(test, not(target_arch = "wasm32")))]
fn join_original_workers(
    workers: Vec<JoinHandle<()>>,
) -> Result<NativeWorkerPoolDisposal, Box<NativeWorkerPoolSettlement>> {
    Box::new(NativeWorkerPoolSettlement::new(workers)).into_disposal()
}

struct NativeWorkerSettlementState {
    pending: VecDeque<JoinHandle<()>>,
    joining: Option<std::thread::ThreadId>,
    settling: bool,
    joined: usize,
    panics: Vec<Arc<NativeWorkerPanic>>,
    join_panics: Vec<NativeWorkerJoinPanic>,
    causes: Vec<NativeWorkerPoolSettlementCause>,
}

struct NativeWorkerJoinPanic {
    original_thread: std::thread::ThreadId,
    cause: Arc<NativeWorkerPanic>,
}

/// Actual cause occurrences in native join chronology, without deduplication.
#[derive(Debug, Clone)]
pub enum NativeWorkerPoolSettlementCause {
    /// The worker itself panicked and its native join completed.
    WorkerPanic(Arc<NativeWorkerPanic>),
    /// The join operation unwound and its consumed handle remains unproven.
    JoinOperationPanic(Arc<NativeWorkerPanic>),
}

/// Observation of actual settlement progress, never a whole-pool acknowledgment.
#[derive(Debug)]
pub struct NativeWorkerPoolSettlementProgress {
    /// Original handles still resident and not yet consumed by a join.
    pub pending_workers: usize,
    /// A real join is currently in progress on another owning caller.
    pub join_in_progress: bool,
    /// Consumed original handles whose native settlement remains unproven.
    pub unproven_workers: usize,
    /// Actual native joins that returned, including worker panic results.
    pub joined_workers: usize,
    /// Original worker panic payloads from completed joins.
    pub worker_panics: Vec<Arc<NativeWorkerPanic>>,
    /// Original join-operation panic payloads; each leaves a consumed handle unproven.
    pub join_operation_panics: Vec<Arc<NativeWorkerPanic>>,
    /// Actual cross-kind cause ordering, including late retry causes.
    pub causes: Vec<NativeWorkerPoolSettlementCause>,
}

/// Original native worker custody retained when a join operation unwinds.
/// A consumed handle cannot be reconstructed or presumed settled after unwind.
pub struct NativeWorkerPoolSettlement {
    state: Mutex<NativeWorkerSettlementState>,
    disposal: std::sync::OnceLock<NativeWorkerPoolDisposal>,
}

impl std::fmt::Debug for NativeWorkerPoolSettlement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativeWorkerPoolSettlement")
            .field("acknowledged", &self.disposal.get().is_some())
            .finish_non_exhaustive()
    }
}

impl NativeWorkerPoolSettlement {
    fn new(workers: Vec<JoinHandle<()>>) -> Self {
        Self {
            state: Mutex::new(NativeWorkerSettlementState {
                pending: workers.into(),
                joining: None,
                settling: false,
                joined: 0,
                panics: Vec::new(),
                join_panics: Vec::new(),
                causes: Vec::new(),
            }),
            disposal: std::sync::OnceLock::new(),
        }
    }

    /// Settle remaining original workers, preserving an earlier join refusal.
    ///
    /// A join-operation panic retains its exact payload and leaves the consumed
    /// handle's settlement permanently unproven. Later calls can join untouched
    /// originals but cannot issue a whole-pool receipt after that uncertainty.
    /// This blocks and is not a cancellation-safe asynchronous operation.
    ///
    /// # Errors
    ///
    /// Returns this same custodian before consuming a handle when called by an
    /// actual original worker or while another settler is active. Also returns
    /// it after a join-operation panic, including on later retries that settle
    /// every remaining original worker but cannot prove the consumed handle.
    pub fn settle_original_workers(&self) -> Result<&NativeWorkerPoolDisposal, &Self> {
        self.settle_with_join(JoinHandle::join)
    }

    fn settle_with_join(
        &self,
        mut join: impl FnMut(JoinHandle<()>) -> std::thread::Result<()>,
    ) -> Result<&NativeWorkerPoolDisposal, &Self> {
        let mut state = self
            .state
            .lock()
            .unwrap_or_else(|poison| poison.into_inner());
        if let Some(receipt) = self.disposal.get() {
            return Ok(receipt);
        }
        let actual = std::thread::current().id();
        if state.settling
            || state.joining == Some(actual)
            || state
                .join_panics
                .iter()
                .any(|panic| panic.original_thread == actual)
            || state
                .pending
                .iter()
                .any(|worker| worker.thread().id() == actual)
        {
            return Err(self);
        }
        state.settling = true;
        drop(state);
        loop {
            let mut state = self
                .state
                .lock()
                .unwrap_or_else(|poison| poison.into_inner());
            let Some(worker) = state.pending.pop_front() else {
                state.settling = false;
                if !state.join_panics.is_empty() {
                    return Err(self);
                }
                let receipt = NativeWorkerPoolDisposal {
                    joined: state.joined,
                    panics: state.panics.clone(),
                };
                // Serialized by the same resident owner flag. No fallible
                // initializer removes original handles before joining them.
                return Ok(self.disposal.get_or_init(|| receipt));
            };
            let original_thread = worker.thread().id();
            state.joining = Some(original_thread);
            drop(state);
            // Only this handle crosses the actual consuming std join boundary.
            // Every untouched handle and prior cause remains in resident state.
            // No resident mutex is held across join or a worker's callback.
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| join(worker)));
            let mut state = self
                .state
                .lock()
                .unwrap_or_else(|poison| poison.into_inner());
            state.joining = None;
            match result {
                Ok(result) => {
                    state.joined += 1;
                    if let Err(payload) = result {
                        let cause = Arc::new(NativeWorkerPanic {
                            payload: Mutex::new(payload),
                        });
                        state
                            .causes
                            .push(NativeWorkerPoolSettlementCause::WorkerPanic(Arc::clone(
                                &cause,
                            )));
                        state.panics.push(cause);
                    }
                }
                Err(payload) => {
                    let cause = Arc::new(NativeWorkerPanic {
                        payload: Mutex::new(payload),
                    });
                    state
                        .causes
                        .push(NativeWorkerPoolSettlementCause::JoinOperationPanic(
                            Arc::clone(&cause),
                        ));
                    state.join_panics.push(NativeWorkerJoinPanic {
                        original_thread,
                        cause,
                    });
                    state.settling = false;
                    return Err(self);
                }
            }
        }
    }

    fn into_disposal(self: Box<Self>) -> Result<NativeWorkerPoolDisposal, Box<Self>> {
        if self.settle_original_workers().is_err() {
            return Err(self);
        }
        Ok(self
            .disposal
            .into_inner()
            .expect("successful settlement published receipt"))
    }

    /// Observe actual progress and original causes without running a callback
    /// under the resident lock or reconstructing a settlement receipt.
    #[must_use]
    pub fn progress(&self) -> NativeWorkerPoolSettlementProgress {
        let state = self
            .state
            .lock()
            .unwrap_or_else(|poison| poison.into_inner());
        NativeWorkerPoolSettlementProgress {
            pending_workers: state.pending.len(),
            join_in_progress: state.joining.is_some(),
            unproven_workers: state.join_panics.len(),
            joined_workers: state.joined,
            worker_panics: state.panics.clone(),
            join_operation_panics: state
                .join_panics
                .iter()
                .map(|panic| Arc::clone(&panic.cause))
                .collect(),
            causes: state.causes.clone(),
        }
    }
}

/// Refused teardown retains either the untouched machine or its native custodian.
pub enum NativeWorkerPoolShutdownFailure {
    /// Called from an actual original worker; no teardown was requested.
    OriginalWorker(Box<super::ThreadedProtocolMachine>),
    /// A native join operation unwound; untouched workers remain owned here.
    Unproven(Box<NativeWorkerPoolSettlement>),
}

impl std::fmt::Debug for NativeWorkerPoolShutdownFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::OriginalWorker(_) => f.write_str("OriginalWorker { original_machine: retained }"),
            Self::Unproven(settlement) => f.debug_tuple("Unproven").field(settlement).finish(),
        }
    }
}

/// Failed construction may have started native workers. The error owns their
/// real join handles until an explicit cleanup call joins them.
pub struct NativeWorkerPoolBuildFailure {
    source: rayon::ThreadPoolBuildError,
    settlement: NativeWorkerPoolSettlement,
}
impl std::fmt::Debug for NativeWorkerPoolBuildFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NativeWorkerPoolBuildFailure")
            .field("source", &self.source)
            .field("settlement", &self.settlement)
            .finish()
    }
}
impl std::fmt::Display for NativeWorkerPoolBuildFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self.source, f)
    }
}
impl std::error::Error for NativeWorkerPoolBuildFailure {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.source)
    }
}
impl NativeWorkerPoolBuildFailure {
    /// Join the actual partially started workers. Observation alone never ACKs.
    ///
    /// # Errors
    ///
    /// Returns the resident original custodian before consuming a handle for
    /// actual-worker or concurrent-settler refusal, or after native join unwind.
    /// Retry retains untouched handles and original causes without ACKing a
    /// consumed handle whose settlement is unproven.
    pub fn settle_original_workers(
        &self,
    ) -> Result<&NativeWorkerPoolDisposal, &NativeWorkerPoolSettlement> {
        self.settlement.settle_original_workers()
    }
}

pub(super) fn build_owned_native_pool(
    workers: usize,
) -> Result<OwnedNativeWorkerPool, NativeWorkerPoolBuildFailure> {
    build_owned_native_pool_with_spawn(workers, spawn_original_worker)
}

fn spawn_original_worker(thread: rayon::ThreadBuilder) -> std::io::Result<JoinHandle<()>> {
    let mut builder = std::thread::Builder::new();
    if let Some(name) = thread.name() {
        builder = builder.name(name.to_owned());
    }
    if let Some(size) = thread.stack_size() {
        builder = builder.stack_size(size);
    }
    builder.spawn(move || thread.run())
}

fn build_owned_native_pool_with_spawn(
    workers: usize,
    mut spawn: impl FnMut(rayon::ThreadBuilder) -> std::io::Result<JoinHandle<()>>,
) -> Result<OwnedNativeWorkerPool, NativeWorkerPoolBuildFailure> {
    let handles = Arc::new(Mutex::new(Vec::new()));
    let retained = Arc::clone(&handles);
    let result = rayon::ThreadPoolBuilder::new()
        .num_threads(workers)
        .spawn_handler(move |thread| {
            let handle = spawn(thread)?;
            retained
                .lock()
                .unwrap_or_else(|poison| poison.into_inner())
                .push(handle);
            Ok(())
        })
        .build();
    let original =
        std::mem::take(&mut *handles.lock().unwrap_or_else(|poison| poison.into_inner()));
    match result {
        Ok(pool) => Ok(OwnedNativeWorkerPool {
            pool,
            workers: original,
        }),
        Err(source) => Err(NativeWorkerPoolBuildFailure {
            source,
            settlement: NativeWorkerPoolSettlement::new(original),
        }),
    }
}

#[cfg(all(test, not(target_arch = "wasm32")))]
mod tests {
    use super::*;
    use std::cell::RefCell;
    use std::sync::atomic::{AtomicUsize, Ordering};

    #[derive(Debug)]
    struct SpawnRefusal(Arc<()>);
    impl std::fmt::Display for SpawnRefusal {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            f.write_str("actual native spawn refusal")
        }
    }
    impl std::error::Error for SpawnRefusal {}

    fn assert_native_refusal(error: &NativeWorkerPoolBuildFailure, identity: &Arc<()>) {
        use std::error::Error;
        let rayon = error
            .source()
            .and_then(|e| e.downcast_ref::<rayon::ThreadPoolBuildError>())
            .expect("actual Rayon constructor source");
        let io = rayon
            .source()
            .and_then(|e| e.downcast_ref::<std::io::Error>())
            .expect("actual original I/O error");
        let actual = io
            .get_ref()
            .and_then(|e| e.downcast_ref::<SpawnRefusal>())
            .expect("original native refusal allocation");
        assert!(Arc::ptr_eq(&actual.0, identity));
    }

    #[test]
    fn first_worker_refusal_retains_actual_source_and_zero_worker_settlement() {
        let identity = Arc::new(());
        let refusal = Arc::clone(&identity);
        let result = build_owned_native_pool_with_spawn(1, move |_| {
            Err(std::io::Error::other(SpawnRefusal(Arc::clone(&refusal))))
        });
        let error = match result {
            Ok(pool) => {
                pool.shutdown().expect("settle unexpected successful pool");
                panic!("actual spawn handler must refuse");
            }
            Err(error) => error,
        };
        let receipt = error
            .settle_original_workers()
            .expect("actual original worker settlement");
        assert_eq!(receipt.joined_workers(), 0);
        assert!(receipt.worker_panics().is_empty());
        assert!(std::ptr::eq(
            receipt,
            error
                .settle_original_workers()
                .expect("same actual receipt")
        ));
        assert_native_refusal(&error, &identity);
    }

    #[test]
    fn partial_worker_refusal_retains_actual_worker_until_explicit_original_join() {
        let identity = Arc::new(());
        let refusal = Arc::clone(&identity);
        let exits = Arc::new(AtomicUsize::new(0));
        let actual_exits = Arc::clone(&exits);
        let (entered, observed) = std::sync::mpsc::sync_channel(1);
        let mut started = false;
        let result = build_owned_native_pool_with_spawn(2, move |thread| {
            if started {
                return Err(std::io::Error::other(SpawnRefusal(Arc::clone(&refusal))));
            }
            started = true;
            let entered = entered.clone();
            let exits = Arc::clone(&actual_exits);
            let handle = std::thread::spawn(move || {
                entered
                    .send(())
                    .expect("acknowledge actual first native worker");
                thread.run();
                exits.fetch_add(1, Ordering::SeqCst);
            });
            observed.recv().map_err(std::io::Error::other)?;
            Ok(handle)
        });
        let error = match result {
            Ok(pool) => {
                pool.shutdown().expect("settle unexpected successful pool");
                panic!("actual second spawn must refuse");
            }
            Err(error) => error,
        };
        let before_ack = error.settlement.disposal.get().is_none();
        let receipt = error
            .settle_original_workers()
            .expect("actual original worker settlement");
        assert!(
            before_ack,
            "constructor refusal alone never acknowledges termination"
        );
        assert_eq!(receipt.joined_workers(), 1);
        assert!(receipt.worker_panics().is_empty());
        assert_eq!(exits.load(Ordering::SeqCst), 1);
        assert!(std::ptr::eq(
            receipt,
            error
                .settle_original_workers()
                .expect("same actual receipt")
        ));
        assert_native_refusal(&error, &identity);
    }

    struct ExitMarker(Arc<AtomicUsize>);
    impl Drop for ExitMarker {
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }
    thread_local! { static ORIGINAL_EXIT: RefCell<Option<ExitMarker>> = const { RefCell::new(None) }; }

    #[test]
    fn normal_pool_shutdown_joins_every_original_worker_before_acknowledgment() {
        let pool = build_owned_native_pool(2).expect("actual native pool");
        let exited = Arc::new(AtomicUsize::new(0));
        pool.pool.broadcast(|_| {
            ORIGINAL_EXIT.with(|slot| {
                *slot.borrow_mut() = Some(ExitMarker(Arc::clone(&exited)));
            })
        });
        let before = exited.load(Ordering::SeqCst);
        let receipt = pool.shutdown().expect("actual original worker joins");
        assert_eq!(before, 0, "original workers remained live before shutdown");
        assert_eq!(receipt.joined_workers(), 2);
        assert!(receipt.worker_panics().is_empty());
        assert_eq!(
            exited.load(Ordering::SeqCst),
            2,
            "native TLS destructors completed before actual join ACK"
        );
    }

    #[test]
    fn original_worker_panic_payload_survives_acknowledged_join() {
        let identity = Arc::new(());
        let actual = Arc::clone(&identity);
        let (entered, observed) = std::sync::mpsc::sync_channel(1);
        let release = Arc::new((Mutex::new(false), std::sync::Condvar::new()));
        let original_release = Arc::clone(&release);
        let worker = std::thread::spawn(move || {
            let (gate, wake) = original_release.as_ref();
            let mut released = gate.lock().expect("original native release gate");
            entered.send(()).expect("actual native worker entered");
            while !*released {
                released = wake.wait(released).expect("actual native worker wait");
            }
            drop(released);
            std::panic::panic_any(actual);
        });
        observed.recv().expect("actual native worker entered");
        let (gate, wake) = release.as_ref();
        // Entry is signalled while holding this mutex. Reacquiring it proves
        // the worker reached its real condition-variable wait before release.
        let mut released = gate.lock().expect("observe original pending worker");
        let was_pending = !*released;
        *released = true;
        wake.notify_one();
        drop(released);
        let receipt = join_original_workers(vec![worker]).expect("actual native join");
        // Release and join before assertions so a failed proof cannot strand
        // the actual original worker at the test gate.
        assert!(
            was_pending,
            "native worker was pending before fault release"
        );
        assert_eq!(receipt.joined_workers(), 1);
        let original = receipt
            .worker_panics()
            .first()
            .expect("actual native panic");
        for _ in 0..2 {
            assert_eq!(
                original.with_payload::<Arc<()>, _>(|payload| Arc::ptr_eq(payload, &identity)),
                Some(true)
            );
        }
        let observer_panicked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            assert!(original
                .with_payload::<Arc<()>, ()>(|_| panic!("observer callback panic"))
                .is_some());
        }))
        .is_err();
        assert!(observer_panicked);
        assert_eq!(
            original.with_payload::<Arc<()>, _>(|payload| Arc::ptr_eq(payload, &identity)),
            Some(true),
            "a poisoned observer lock cannot hide the actual original native payload"
        );
    }

    #[test]
    fn shutdown_from_actual_original_worker_returns_untouched_machine_for_external_retry() {
        let machine = super::super::ThreadedProtocolMachine::try_with_workers(
            crate::engine::ProtocolMachineConfig::default(),
            1,
        )
        .expect("actual private pool");
        let (handoff, admitted) =
            std::sync::mpsc::sync_channel::<super::super::ThreadedProtocolMachine>(1);
        let (returned, observed) = std::sync::mpsc::sync_channel(1);
        machine.pool.pool.spawn(move || {
            let original = admitted
                .recv()
                .expect("actual machine transferred to its worker");
            match original.shutdown_worker_pool() {
                Err(NativeWorkerPoolShutdownFailure::OriginalWorker(original)) => assert!(
                    returned.send(Some(original)).is_ok(),
                    "return actual unmodified owner"
                ),
                Ok(_) => assert!(
                    returned.send(None).is_ok(),
                    "record unexpected worker acceptance"
                ),
                Err(NativeWorkerPoolShutdownFailure::Unproven(_)) => {
                    panic!("actual-worker preflight must precede joining")
                }
            }
        });
        assert!(
            handoff.send(machine).is_ok(),
            "actual private pool accepts its original owner"
        );
        let original = observed
            .recv()
            .expect("actual worker reports refusal")
            .expect("self-join must return original machine");
        let receipt = match (*original).shutdown_worker_pool() {
            Ok(receipt) => receipt,
            Err(_) => panic!("external same-original retry can join"),
        };
        assert_eq!(receipt.joined_workers(), 1);
        assert!(receipt.worker_panics().is_empty());
    }

    #[test]
    fn machine_shutdown_consumes_actual_private_pool_and_issues_join_receipt() {
        let machine = super::super::ThreadedProtocolMachine::try_with_workers(
            crate::engine::ProtocolMachineConfig::default(),
            2,
        )
        .expect("actual machine and native pool");
        let receipt = match machine.shutdown_worker_pool() {
            Ok(receipt) => receipt,
            Err(_) => panic!("external owner cannot be its original worker"),
        };
        assert_eq!(receipt.joined_workers(), 2);
        assert!(receipt.worker_panics().is_empty());
    }

    #[test]
    fn normal_pool_join_unwind_retains_untouched_handles_without_acknowledgment() {
        let pool = build_owned_native_pool(2).expect("actual native pool");
        let identity = Arc::new(());
        let original = Arc::clone(&identity);
        let mut inject = true;
        let settlement = pool
            .shutdown_with_join(move |worker| {
                let result = worker.join();
                if inject {
                    inject = false;
                    // Exact consuming join boundary; this is NOT an OS refusal.
                    // The custodian cannot infer the consumed handle's settlement.
                    std::panic::panic_any(Arc::clone(&original));
                }
                result
            })
            .expect_err("injected join-operation unwind retains custody");
        let before = settlement.progress();
        let retry_refused = settlement.settle_original_workers().is_err();
        let after = settlement.progress();
        assert_eq!(before.pending_workers, 1);
        assert_eq!(before.joined_workers, 0);
        assert!(
            retry_refused,
            "uncertain consumed handle prevents whole-pool ACK"
        );
        assert_eq!(after.pending_workers, 0);
        assert_eq!(after.joined_workers, 1);
        assert!(after.worker_panics.is_empty());
        assert!(settlement.disposal.get().is_none());
        assert_eq!(after.join_operation_panics.len(), 1);
        assert!(Arc::ptr_eq(
            &before.join_operation_panics[0],
            &after.join_operation_panics[0]
        ));
        assert_eq!(
            after.join_operation_panics[0]
                .with_payload::<Arc<()>, _>(|payload| Arc::ptr_eq(payload, &identity)),
            Some(true)
        );
    }

    struct ReleasePendingWorker(Arc<(Mutex<bool>, std::sync::Condvar)>);
    impl ReleasePendingWorker {
        fn release(&self) {
            let (gate, wake) = self.0.as_ref();
            *gate.lock().unwrap_or_else(|poison| poison.into_inner()) = true;
            wake.notify_all();
        }
    }
    impl Drop for ReleasePendingWorker {
        fn drop(&mut self) {
            self.release();
        }
    }

    fn partial_refusal_with_pending_worker(
        native_refusal: Arc<()>,
        worker_panic: Arc<()>,
        late_panic: Arc<()>,
        gate: Arc<(Mutex<bool>, std::sync::Condvar)>,
        entered: std::sync::mpsc::SyncSender<()>,
        exited: Arc<AtomicUsize>,
    ) -> NativeWorkerPoolBuildFailure {
        let gate_for_refusal = Arc::clone(&gate);
        let mut ordinal = 0;
        let result = build_owned_native_pool_with_spawn(4, move |thread| {
            ordinal += 1;
            let actual_ordinal = ordinal;
            if actual_ordinal == 4 {
                return Err(std::io::Error::other(SpawnRefusal(Arc::clone(
                    &native_refusal,
                ))));
            }
            let worker_panic = Arc::clone(&worker_panic);
            let late_panic = Arc::clone(&late_panic);
            let gate = Arc::clone(&gate);
            let entered = entered.clone();
            let exited = Arc::clone(&exited);
            std::thread::Builder::new().spawn(move || {
                thread.run();
                if actual_ordinal == 1 {
                    std::panic::panic_any(worker_panic);
                }
                if actual_ordinal == 3 {
                    let (lock, wake) = gate.as_ref();
                    let mut released = lock.lock().expect("original pending worker gate");
                    entered.send(()).expect("actual post-Rayon worker pending");
                    while !*released {
                        released = wake.wait(released).expect("original pending wait");
                    }
                    exited.fetch_add(1, Ordering::SeqCst);
                    drop(released);
                    std::panic::panic_any(late_panic);
                }
            })
        });
        match result {
            Err(failure) => failure,
            Ok(pool) => {
                let (lock, wake) = gate_for_refusal.as_ref();
                *lock.lock().expect("release unexpected successful pool") = true;
                wake.notify_all();
                pool.shutdown().expect("settle unexpected successful pool");
                panic!("actual fourth spawn must refuse");
            }
        }
    }

    #[test]
    fn failed_constructor_join_unwind_retains_prior_causes_and_pending_original_retry() {
        let native_identity = Arc::new(());
        let native_refusal = Arc::clone(&native_identity);
        let worker_identity = Arc::new(());
        let worker_panic = Arc::clone(&worker_identity);
        let late_identity = Arc::new(());
        let late_panic = Arc::clone(&late_identity);
        let join_identity = Arc::new(());
        let join_panic = Arc::clone(&join_identity);
        let gate = Arc::new((Mutex::new(false), std::sync::Condvar::new()));
        let release = ReleasePendingWorker(Arc::clone(&gate));
        let (entered, observed) = std::sync::mpsc::sync_channel(1);
        let exited = Arc::new(AtomicUsize::new(0));
        let failure = partial_refusal_with_pending_worker(
            native_refusal,
            worker_panic,
            late_panic,
            Arc::clone(&release.0),
            entered,
            Arc::clone(&exited),
        );
        observed
            .recv()
            .expect("actual third worker entered pending gate");
        let mut joins = 0;
        let refused = failure
            .settlement
            .settle_with_join(move |worker| {
                joins += 1;
                let actual = worker.join();
                if joins == 2 {
                    std::panic::panic_any(Arc::clone(&join_panic));
                }
                actual
            })
            .is_err();
        let before = failure.settlement.progress();
        // Reacquisition after the worker's send proves its actual Condvar wait.
        let (lock, wake) = release.0.as_ref();
        let mut released = lock.lock().expect("observe original pending worker");
        let was_pending = !*released;
        *released = true;
        wake.notify_all();
        drop(released);
        let retry_refused = failure.settle_original_workers().is_err();
        let after = failure.settlement.progress();
        // All reachable original handles have been settled before assertions.
        assert!(refused && retry_refused && was_pending);
        assert_eq!(before.pending_workers, 1);
        assert_eq!(before.joined_workers, 1);
        assert_eq!(after.pending_workers, 0);
        assert_eq!(after.joined_workers, 2);
        assert_eq!(exited.load(Ordering::SeqCst), 1);
        assert_eq!(after.worker_panics.len(), 2);
        assert_eq!(after.join_operation_panics.len(), 1);
        assert!(Arc::ptr_eq(
            &before.worker_panics[0],
            &after.worker_panics[0]
        ));
        assert_eq!(
            after.worker_panics[0]
                .with_payload::<Arc<()>, _>(|payload| Arc::ptr_eq(payload, &worker_identity)),
            Some(true)
        );
        assert_eq!(
            after.worker_panics[1]
                .with_payload::<Arc<()>, _>(|payload| Arc::ptr_eq(payload, &late_identity)),
            Some(true)
        );
        assert_eq!(
            after.join_operation_panics[0]
                .with_payload::<Arc<()>, _>(|payload| Arc::ptr_eq(payload, &join_identity)),
            Some(true)
        );
        assert!(failure.settlement.disposal.get().is_none());
        assert!(matches!(
            after.causes.as_slice(),
            [
                NativeWorkerPoolSettlementCause::WorkerPanic(_),
                NativeWorkerPoolSettlementCause::JoinOperationPanic(_),
                NativeWorkerPoolSettlementCause::WorkerPanic(_)
            ]
        ));
        assert_native_refusal(&failure, &native_identity);
    }

    #[test]
    fn resident_settlement_refuses_actual_original_worker_before_consuming_handles() {
        let (handoff, admitted) =
            std::sync::mpsc::sync_channel::<Arc<NativeWorkerPoolSettlement>>(1);
        let (reported, observed) = std::sync::mpsc::sync_channel(1);
        let worker = std::thread::spawn(move || {
            let original = admitted.recv().expect("actual resident custodian handoff");
            let refused = original.settle_original_workers().is_err();
            let pending = original.progress().pending_workers;
            reported
                .send((refused, pending))
                .expect("report original-worker refusal");
        });
        let original = Arc::new(NativeWorkerPoolSettlement::new(vec![worker]));
        let sent = handoff.send(Arc::clone(&original));
        let outcome = observed.recv();
        let receipt = original
            .settle_original_workers()
            .expect("external same-original join");
        assert!(sent.is_ok());
        assert_eq!(outcome.expect("actual worker reports"), (true, 1));
        assert_eq!(receipt.joined_workers(), 1);
    }

    #[test]
    fn pending_join_allows_original_worker_observation_and_reentrant_refusal() {
        let (handoff, admitted) =
            std::sync::mpsc::sync_channel::<Arc<NativeWorkerPoolSettlement>>(1);
        let (join_entered, join_observed) = std::sync::mpsc::sync_channel(1);
        let (reported, observed) = std::sync::mpsc::sync_channel(1);
        let worker = std::thread::spawn(move || {
            let original = admitted.recv().expect("same custodian");
            join_observed.recv().expect("actual join boundary admitted");
            let progress = original.progress();
            let refused = original.settle_original_workers().is_err();
            reported
                .send((progress.join_in_progress, refused))
                .expect("worker reports without resident lock deadlock");
        });
        let original = Arc::new(NativeWorkerPoolSettlement::new(vec![worker]));
        let sent = handoff.send(Arc::clone(&original));
        let receipt = original
            .settle_with_join(|worker| {
                join_entered.send(()).expect("publish actual join entry");
                worker.join()
            })
            .expect("real original join completes after worker observation");
        assert!(sent.is_ok());
        assert_eq!(
            observed.recv().expect("actual worker observation"),
            (true, true)
        );
        assert_eq!(receipt.joined_workers(), 1);
    }

    #[test]
    fn unproven_consumed_original_worker_is_refused_before_untouched_retry() {
        let (handoff, admitted) =
            std::sync::mpsc::sync_channel::<Arc<NativeWorkerPoolSettlement>>(1);
        let (attempt, attempt_observed) = std::sync::mpsc::sync_channel(1);
        let (reported, observed) = std::sync::mpsc::sync_channel(1);
        let gate = Arc::new((Mutex::new(false), std::sync::Condvar::new()));
        let release = ReleasePendingWorker(Arc::clone(&gate));
        let consumed = std::thread::spawn(move || {
            let original = admitted.recv().expect("same original settlement custody");
            attempt_observed
                .recv()
                .expect("original join operation unwound");
            let refused = original.settle_original_workers().is_err();
            let progress = original.progress();
            let (lock, wake) = gate.as_ref();
            let mut released = lock.lock().expect("original consumed worker gate");
            reported
                .send((refused, progress.pending_workers, progress.joined_workers))
                .expect("original worker retry observed");
            while !*released {
                released = wake.wait(released).expect("actual consumed worker wait");
            }
        });
        let untouched = std::thread::spawn(|| ());
        let original = Arc::new(NativeWorkerPoolSettlement::new(vec![consumed, untouched]));
        let handed = handoff.send(Arc::clone(&original));
        let (retained, cleanup) = std::sync::mpsc::sync_channel(1);
        let identity = Arc::new(());
        let injected = Arc::clone(&identity);
        let refused = original
            .settle_with_join(move |worker| {
                // Test-only cleanup retains the SAME real handle before injected
                // unwind. Production cannot recover std's consumed native handle.
                retained
                    .send(worker)
                    .expect("retain actual handle for fixture cleanup");
                std::panic::panic_any(Arc::clone(&injected));
            })
            .is_err();
        let signalled = attempt.send(());
        let worker_outcome = observed.recv();
        let consumed_was_pending = {
            let (lock, _) = release.0.as_ref();
            !*lock.lock().expect("observe actual consumed-worker wait")
        };
        let retry_refused = original.settle_original_workers().is_err();
        let after = original.progress();
        // Release and actually join the test-owned consumed worker before any
        // assertions. Its foreign test cleanup cannot mint a production ACK.
        release.release();
        let consumed_join = cleanup
            .recv()
            .expect("same original consumed handle")
            .join();
        assert!(
            handed.is_ok() && signalled.is_ok() && refused && retry_refused && consumed_was_pending
        );
        assert_eq!(worker_outcome.expect("actual worker retry"), (true, 1, 0));
        assert!(consumed_join.is_ok());
        assert_eq!(after.pending_workers, 0);
        assert_eq!(after.joined_workers, 1);
        assert_eq!(after.unproven_workers, 1);
        assert!(original.disposal.get().is_none());
        assert_eq!(
            after.join_operation_panics[0]
                .with_payload::<Arc<()>, _>(|payload| Arc::ptr_eq(payload, &identity)),
            Some(true)
        );
    }
}
