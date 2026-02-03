//! Threaded VM backend (feature-gated).
//!
//! Executes one coroutine per session per round in parallel, preserving
//! per-session trace equivalence with the cooperative VM.

use rayon::prelude::*;
use rayon::{ThreadPool, ThreadPoolBuilder};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, RwLock};

use telltale_types::LocalTypeR;

use crate::buffer::{BoundedBuffer, BufferConfig, EnqueueResult};
use crate::clock::SimClock;
use crate::coroutine::{BlockReason, CoroStatus, Coroutine, Fault, Value};
use crate::effect::{EffectHandler, SendDecision};
use crate::instr::{Endpoint, Instr, PC};
use crate::loader::CodeImage;
use crate::scheduler::Scheduler;
use crate::session::{
    unfold_if_var_with_scope, unfold_mu, Edge, SessionId, SessionState, SessionStatus, TypeEntry,
};
use crate::vm::{ObsEvent, StepResult, VMConfig, VMError};

/// Threaded VM runtime. Uses OS threads for coroutine execution.
pub struct ThreadedVM {
    config: VMConfig,
    coroutines: Vec<Arc<Mutex<Coroutine>>>,
    sessions: ThreadedSessionStore,
    scheduler: Scheduler,
    trace: Vec<ObsEvent>,
    clock: SimClock,
    next_coro_id: usize,
    pool: ThreadPool,
    workers: usize,
}

/// Session-scoped locks for concurrent execution.
#[derive(Debug, Default)]
pub struct SessionLock {
    locks: BTreeMap<SessionId, Mutex<()>>,
}

impl SessionLock {
    /// Create an empty lock table.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Ensure a lock exists for a session.
    pub fn ensure(&mut self, sid: SessionId) {
        self.locks.entry(sid).or_insert_with(|| Mutex::new(()));
    }
}

#[derive(Debug, Default)]
struct ThreadedSessionStore {
    sessions: RwLock<BTreeMap<SessionId, Arc<Mutex<SessionState>>>>,
    next_id: AtomicUsize,
}

impl ThreadedSessionStore {
    fn new() -> Self {
        Self::default()
    }

    fn open(
        &self,
        roles: Vec<String>,
        buffer_config: &BufferConfig,
        initial_types: &BTreeMap<String, LocalTypeR>,
    ) -> SessionId {
        let sid = self.next_id.fetch_add(1, Ordering::SeqCst);

        let mut local_types = BTreeMap::new();
        for role in &roles {
            if let Some(lt) = initial_types.get(role) {
                let ep = Endpoint {
                    sid,
                    role: role.clone(),
                };
                local_types.insert(
                    ep,
                    TypeEntry {
                        current: unfold_mu(lt),
                        original: lt.clone(),
                    },
                );
            }
        }

        let mut buffers = BTreeMap::new();
        for from in &roles {
            for to in &roles {
                if from != to {
                    let edge = Edge {
                        from: from.clone(),
                        to: to.clone(),
                    };
                    buffers.insert(edge, BoundedBuffer::new(buffer_config));
                }
            }
        }

        let state = SessionState {
            sid,
            roles,
            local_types,
            buffers,
            status: SessionStatus::Active,
            epoch: 0,
        };

        let mut sessions = self.sessions.write().expect("session store lock poisoned");
        sessions.insert(sid, Arc::new(Mutex::new(state)));
        sid
    }

    fn get(&self, sid: SessionId) -> Option<Arc<Mutex<SessionState>>> {
        self.sessions
            .read()
            .expect("session store lock poisoned")
            .get(&sid)
            .cloned()
    }

    fn active_count(&self) -> usize {
        let sessions = self.sessions.read().expect("session store lock poisoned");
        sessions
            .values()
            .filter(|session| {
                session.lock().expect("session lock poisoned").status == SessionStatus::Active
            })
            .count()
    }
}

struct Picked {
    coro_id: usize,
    coro: Arc<Mutex<Coroutine>>,
    session: Arc<Mutex<SessionState>>,
}

/// How to update the coroutine after an instruction.
enum CoroUpdate {
    /// Advance PC by 1, status = Ready.
    AdvancePc,
    /// Set PC to target (for Jmp), status = Ready.
    SetPc(PC),
    /// Block with given reason. PC unchanged.
    Block(BlockReason),
    /// Halt (Done). PC unchanged.
    Halt,
    /// Advance PC by 1, write a value to a register, status = Ready.
    AdvancePcWriteReg { reg: u16, val: Value },
}

/// Type update action for commit.
enum TypeUpdate {
    /// Advance to a new local type.
    Advance(LocalTypeR),
    /// Advance to a new local type and update the original (for Mu unfolding).
    AdvanceWithOriginal(LocalTypeR, LocalTypeR),
    /// Remove the type entry (endpoint completed).
    Remove,
}

/// Resolve a continuation and build the appropriate `TypeUpdate`.
fn resolve_type_update(
    cont: &LocalTypeR,
    original: &LocalTypeR,
    ep: &Endpoint,
) -> (LocalTypeR, Option<(Endpoint, TypeUpdate)>) {
    let (resolved, new_scope) = unfold_if_var_with_scope(cont, original);
    let update = if let Some(mu) = new_scope {
        Some((
            ep.clone(),
            TypeUpdate::AdvanceWithOriginal(resolved.clone(), mu),
        ))
    } else {
        Some((ep.clone(), TypeUpdate::Advance(resolved.clone())))
    };
    (resolved, update)
}

/// Atomic result of executing one instruction.
struct StepPack {
    /// How to update the coroutine.
    coro_update: CoroUpdate,
    /// Type advancement, if any. `None` means no type change (e.g., block, control flow).
    type_update: Option<(Endpoint, TypeUpdate)>,
    /// Observable events to emit.
    events: Vec<ObsEvent>,
}

/// Internal outcome after committing a `StepPack`.
enum ExecOutcome {
    /// Instruction completed, coroutine continues.
    Continue,
    /// Coroutine blocked on a resource.
    Blocked(BlockReason),
    /// Coroutine halted normally.
    Halted,
}

impl ThreadedVM {
    /// Create with thread pool sized to available OS parallelism.
    #[must_use]
    pub fn auto(config: VMConfig) -> Self {
        let workers = std::thread::available_parallelism()
            .map(|n| n.get())
            .unwrap_or(1);
        Self::with_workers(config, workers)
    }

    /// Create with explicit worker count.
    ///
    /// # Panics
    ///
    /// Panics if the thread pool cannot be created.
    #[must_use]
    pub fn with_workers(config: VMConfig, workers: usize) -> Self {
        let worker_count = workers.max(1);
        let pool = ThreadPoolBuilder::new()
            .num_threads(worker_count)
            .build()
            .expect("thread pool build failed");
        let tick_duration = config.tick_duration;
        let scheduler = Scheduler::new(config.sched_policy.clone());
        Self {
            config,
            coroutines: Vec::new(),
            sessions: ThreadedSessionStore::new(),
            scheduler,
            trace: Vec::new(),
            clock: SimClock::new(tick_duration),
            next_coro_id: 0,
            pool,
            workers: worker_count,
        }
    }

    /// Load a choreography into the VM.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if session or coroutine limits are exceeded.
    pub fn load_choreography(&mut self, image: &CodeImage) -> Result<SessionId, VMError> {
        if self.sessions.active_count() >= self.config.max_sessions {
            return Err(VMError::TooManySessions {
                max: self.config.max_sessions,
            });
        }

        let roles = image.roles();
        let sid = self.sessions.open(
            roles.clone(),
            &self.config.buffer_config,
            &image.local_types,
        );

        self.trace.push(ObsEvent::Opened {
            tick: self.clock.tick,
            session: sid,
            roles: roles.clone(),
        });

        for role in &roles {
            if self.coroutines.len() >= self.config.max_coroutines {
                return Err(VMError::TooManyCoroutines {
                    max: self.config.max_coroutines,
                });
            }

            let program = image.programs.get(role).cloned().unwrap_or_default();
            let coro_id = self.next_coro_id;
            self.next_coro_id += 1;

            let ep = Endpoint {
                sid,
                role: role.clone(),
            };
            let mut coro = Coroutine::new(
                coro_id,
                program,
                sid,
                role.clone(),
                self.config.num_registers,
            );
            coro.owned_endpoints.push(ep);

            self.scheduler.add_ready(coro_id);
            self.coroutines.push(Arc::new(Mutex::new(coro)));
        }

        Ok(sid)
    }

    /// Execute one scheduler round: advance up to `n` ready coroutines.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if any coroutine faults.
    pub fn step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, VMError> {
        if n == 0 {
            return Err(VMError::InvalidConcurrency { n });
        }
        self.clock.advance();
        let tick = self.clock.tick;
        if self.all_done() {
            return Ok(StepResult::AllDone);
        }

        self.try_unblock_receivers();

        let mut progressed = false;
        let mut remaining = n;

        // Run in parallel waves. Each wave schedules at most one coroutine per session,
        // but a session may execute again in a later wave within the same round.
        while remaining > 0 {
            let picks = self.pick_ready(remaining)?;
            if picks.is_empty() {
                break;
            }

            let results: Vec<Result<StepPack, Fault>> = self.pool.install(|| {
                picks
                    .par_iter()
                    .map(|pick| {
                        exec_instr(&pick.coro, &pick.session, &self.sessions, handler, tick)
                    })
                    .collect()
            });

            for (pick, result) in picks.iter().zip(results.into_iter()) {
                match result {
                    Ok(pack) => {
                        progressed = true;
                        match self.commit_pack(&pick.coro, &pick.session, pack) {
                            Ok(outcome) => match outcome {
                                ExecOutcome::Continue => {
                                    self.scheduler.reschedule(pick.coro_id);
                                }
                                ExecOutcome::Blocked(reason) => {
                                    self.scheduler.mark_blocked(pick.coro_id, reason);
                                }
                                ExecOutcome::Halted => {
                                    self.scheduler.mark_done(pick.coro_id);
                                    self.trace.push(ObsEvent::Halted {
                                        tick,
                                        coro_id: pick.coro_id,
                                    });
                                }
                            },
                            Err(fault) => {
                                self.trace.push(ObsEvent::Faulted {
                                    tick,
                                    coro_id: pick.coro_id,
                                    fault: fault.clone(),
                                });
                                let mut coro = pick.coro.lock().expect("coroutine lock poisoned");
                                coro.status = CoroStatus::Faulted(fault.clone());
                                self.scheduler.mark_done(pick.coro_id);
                                return Err(VMError::Fault {
                                    coro_id: pick.coro_id,
                                    fault,
                                });
                            }
                        }
                    }
                    Err(fault) => {
                        self.trace.push(ObsEvent::Faulted {
                            tick,
                            coro_id: pick.coro_id,
                            fault: fault.clone(),
                        });
                        let mut coro = pick.coro.lock().expect("coroutine lock poisoned");
                        coro.status = CoroStatus::Faulted(fault.clone());
                        self.scheduler.mark_done(pick.coro_id);
                        return Err(VMError::Fault {
                            coro_id: pick.coro_id,
                            fault,
                        });
                    }
                }
            }

            remaining = remaining.saturating_sub(picks.len());
        }

        if self.all_done() {
            Ok(StepResult::AllDone)
        } else if progressed {
            Ok(StepResult::Continue)
        } else {
            Ok(StepResult::Stuck)
        }
    }

    /// Run the VM until completion, using the configured worker count.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if any coroutine faults.
    pub fn run(&mut self, handler: &dyn EffectHandler, max_rounds: usize) -> Result<(), VMError> {
        self.run_concurrent(handler, max_rounds, self.workers.max(1))
    }

    /// Run the VM with explicit concurrency.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if any coroutine faults.
    pub fn run_concurrent(
        &mut self,
        handler: &dyn EffectHandler,
        max_rounds: usize,
        concurrency: usize,
    ) -> Result<(), VMError> {
        for _ in 0..max_rounds {
            match self.step_round(handler, concurrency)? {
                StepResult::AllDone | StepResult::Stuck => return Ok(()),
                StepResult::Continue => {}
            }
        }
        Ok(())
    }

    /// Get the observable trace.
    #[must_use]
    pub fn trace(&self) -> &[ObsEvent] {
        &self.trace
    }

    /// Access the simulation clock.
    #[must_use]
    pub fn clock(&self) -> &SimClock {
        &self.clock
    }

    fn all_done(&self) -> bool {
        self.coroutines
            .iter()
            .all(|coro| coro.lock().expect("coroutine lock poisoned").is_terminal())
    }

    fn try_unblock_receivers(&mut self) {
        let blocked_ids = self.scheduler.blocked_ids();
        for coro_id in blocked_ids {
            let reason = self.scheduler.block_reason(coro_id).cloned();
            if let Some(BlockReason::RecvWait { endpoint }) = reason {
                if let Some(session) = self.sessions.get(endpoint.sid) {
                    let session = session.lock().expect("session lock poisoned");
                    let has_msg = session.roles.iter().any(|sender| {
                        sender != &endpoint.role && session.has_message(sender, &endpoint.role)
                    });
                    if has_msg {
                        self.scheduler.unblock(coro_id);
                    }
                }
            }
        }
    }

    fn pick_ready(&mut self, n: usize) -> Result<Vec<Picked>, VMError> {
        let mut picks = Vec::new();
        let mut deferred = Vec::new();
        let mut used_sessions = BTreeSet::new();
        let attempts = self.scheduler.ready_count();

        for _ in 0..attempts {
            if picks.len() >= n {
                break;
            }

            let coro_id = match self.scheduler.schedule() {
                Some(id) => id,
                None => break,
            };
            let coro = self
                .coroutines
                .get(coro_id)
                .cloned()
                .expect("coroutine exists");
            let sid = {
                let coro_guard = coro.lock().expect("coroutine lock poisoned");
                coro_guard.session_id
            };

            if used_sessions.contains(&sid) {
                deferred.push(coro_id);
                continue;
            }

            let session = self
                .sessions
                .get(sid)
                .ok_or(VMError::SessionNotFound(sid))?;
            used_sessions.insert(sid);
            picks.push(Picked {
                coro_id,
                coro,
                session,
            });
        }

        for coro_id in deferred {
            self.scheduler.reschedule(coro_id);
        }

        Ok(picks)
    }

    fn commit_pack(
        &mut self,
        coro: &Arc<Mutex<Coroutine>>,
        session: &Arc<Mutex<SessionState>>,
        pack: StepPack,
    ) -> Result<ExecOutcome, Fault> {
        let mut coro_guard = coro.lock().expect("coroutine lock poisoned");

        match pack.coro_update {
            CoroUpdate::AdvancePc => {
                coro_guard.pc += 1;
                coro_guard.status = CoroStatus::Ready;
            }
            CoroUpdate::SetPc(pc) => {
                coro_guard.pc = pc;
                coro_guard.status = CoroStatus::Ready;
            }
            CoroUpdate::Block(ref reason) => {
                coro_guard.status = CoroStatus::Blocked(reason.clone());
            }
            CoroUpdate::Halt => {
                coro_guard.status = CoroStatus::Done;
            }
            CoroUpdate::AdvancePcWriteReg { reg, ref val } => {
                coro_guard.regs[usize::from(reg)] = val.clone();
                coro_guard.pc += 1;
                coro_guard.status = CoroStatus::Ready;
            }
        }

        if let Some((ep, update)) = pack.type_update {
            let mut session_guard = session.lock().expect("session lock poisoned");
            match update {
                TypeUpdate::Advance(lt) => {
                    if let Some(entry) = session_guard.local_types.get_mut(&ep) {
                        entry.current = lt;
                    }
                }
                TypeUpdate::AdvanceWithOriginal(lt, orig) => {
                    if let Some(entry) = session_guard.local_types.get_mut(&ep) {
                        entry.current = lt;
                        entry.original = orig;
                    }
                }
                TypeUpdate::Remove => {
                    session_guard.local_types.remove(&ep);
                }
            }
        }

        self.trace.extend(pack.events);

        match &coro_guard.status {
            CoroStatus::Ready => Ok(ExecOutcome::Continue),
            CoroStatus::Blocked(reason) => Ok(ExecOutcome::Blocked(reason.clone())),
            CoroStatus::Done => Ok(ExecOutcome::Halted),
            CoroStatus::Faulted(f) => Err(f.clone()),
        }
    }
}

fn exec_instr(
    coro: &Arc<Mutex<Coroutine>>,
    session: &Arc<Mutex<SessionState>>,
    store: &ThreadedSessionStore,
    handler: &dyn EffectHandler,
    tick: u64,
) -> Result<StepPack, Fault> {
    let mut coro_guard = coro.lock().expect("coroutine lock poisoned");
    let pc = coro_guard.pc;
    if pc >= coro_guard.program.len() {
        return Err(Fault::PcOutOfBounds);
    }
    let instr = coro_guard.program[pc].clone();
    let ep = coro_guard
        .owned_endpoints
        .first()
        .cloned()
        .ok_or(Fault::PcOutOfBounds)?;
    let role = coro_guard.role.clone();
    let sid = coro_guard.session_id;

    match instr {
        Instr::Send { val, .. } => {
            let mut session_guard = session.lock().expect("session lock poisoned");
            step_send(
                &mut coro_guard,
                &mut session_guard,
                &ep,
                &role,
                sid,
                val,
                handler,
                tick,
            )
        }
        Instr::Recv { dst, .. } => {
            let mut session_guard = session.lock().expect("session lock poisoned");
            step_recv(
                &mut coro_guard,
                &mut session_guard,
                &ep,
                &role,
                sid,
                dst,
                handler,
                tick,
            )
        }
        Instr::Halt => {
            let mut session_guard = session.lock().expect("session lock poisoned");
            step_halt(&mut session_guard, &ep, tick)
        }
        Instr::Jmp { target } => Ok(StepPack {
            coro_update: CoroUpdate::SetPc(target),
            type_update: None,
            events: vec![],
        }),
        Instr::Yield => Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![],
        }),
        Instr::Invoke { .. } => step_invoke(&mut coro_guard, &role, handler, tick),
        Instr::LoadImm { dst, val } => {
            let v = match val {
                crate::instr::ImmValue::Unit => Value::Unit,
                crate::instr::ImmValue::Int(i) => Value::Int(i),
                crate::instr::ImmValue::Real(r) => Value::Real(r),
                crate::instr::ImmValue::Bool(b) => Value::Bool(b),
                crate::instr::ImmValue::Str(s) => Value::Str(s),
            };
            Ok(StepPack {
                coro_update: CoroUpdate::AdvancePcWriteReg { reg: dst, val: v },
                type_update: None,
                events: vec![],
            })
        }
        Instr::Mov { dst, src } => {
            let v = coro_guard.regs[usize::from(src)].clone();
            Ok(StepPack {
                coro_update: CoroUpdate::AdvancePcWriteReg { reg: dst, val: v },
                type_update: None,
                events: vec![],
            })
        }
        Instr::Choose { label, target, .. } => {
            let mut session_guard = session.lock().expect("session lock poisoned");
            step_choose(
                &mut session_guard,
                &ep,
                &role,
                sid,
                &label,
                target,
                &coro_guard.regs,
                handler,
                tick,
            )
        }
        Instr::Offer { chan, ref table } => {
            let mut session_guard = session.lock().expect("session lock poisoned");
            step_offer(
                &mut coro_guard,
                &mut session_guard,
                &ep,
                &role,
                sid,
                chan,
                table,
                handler,
                tick,
            )
        }
        Instr::Close { .. } => {
            let mut session_guard = session.lock().expect("session lock poisoned");
            step_close(&mut session_guard, &ep, sid, tick)
        }
        Instr::Open {
            ref roles,
            ref endpoints,
        } => step_open(store, roles, endpoints, tick),
    }
}

fn step_send(
    coro: &mut Coroutine,
    session: &mut SessionState,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    _val_reg: u16,
    handler: &dyn EffectHandler,
    tick: u64,
) -> Result<StepPack, Fault> {
    let local_type = session
        .local_types
        .get(ep)
        .ok_or_else(|| Fault::TypeViolation {
            message: format!("{role}: no type registered"),
        })?
        .current
        .clone();

    let (partner, branches) = match &local_type {
        LocalTypeR::Send {
            partner, branches, ..
        } => (partner.clone(), branches.clone()),
        other => {
            return Err(Fault::TypeViolation {
                message: format!("{role}: expected Send, got {other:?}"),
            })
        }
    };

    let (label, _vt, continuation) = branches
        .first()
        .ok_or_else(|| Fault::TypeViolation {
            message: format!("{role}: send has no branches"),
        })?
        .clone();

    let decision = handler
        .send_decision(sid, role, &partner, &label.name, &coro.regs, None)
        .map_err(|e| Fault::InvokeFault { message: e })?;

    let enqueue = match decision {
        SendDecision::Deliver(payload) => session
            .send(role, &partner, payload)
            .map_err(|e| Fault::InvokeFault { message: e })?,
        SendDecision::Drop | SendDecision::Defer => EnqueueResult::Dropped,
    };

    match enqueue {
        EnqueueResult::Ok => {}
        EnqueueResult::WouldBlock => {
            return Ok(StepPack {
                coro_update: CoroUpdate::Block(BlockReason::SendWait {
                    endpoint: ep.clone(),
                }),
                type_update: None,
                events: vec![],
            });
        }
        EnqueueResult::Full => {
            return Err(Fault::BufferFull {
                endpoint: ep.clone(),
            });
        }
        EnqueueResult::Dropped => {}
    }

    let original = session
        .local_types
        .get(ep)
        .map(|entry| &entry.original)
        .unwrap_or(&LocalTypeR::End);
    let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update,
        events: vec![ObsEvent::Sent {
            tick,
            session: sid,
            from: role.to_string(),
            to: partner,
            label: label.name.clone(),
        }],
    })
}

fn step_recv(
    coro: &mut Coroutine,
    session: &mut SessionState,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    dst_reg: u16,
    handler: &dyn EffectHandler,
    tick: u64,
) -> Result<StepPack, Fault> {
    let local_type = session
        .local_types
        .get(ep)
        .ok_or_else(|| Fault::TypeViolation {
            message: format!("{role}: no type registered"),
        })?
        .current
        .clone();

    let (partner, branches) = match &local_type {
        LocalTypeR::Recv {
            partner, branches, ..
        } => (partner.clone(), branches.clone()),
        other => {
            return Err(Fault::TypeViolation {
                message: format!("{role}: expected Recv, got {other:?}"),
            })
        }
    };

    let (label, _vt, continuation) = branches
        .first()
        .ok_or_else(|| Fault::TypeViolation {
            message: format!("{role}: recv has no branches"),
        })?
        .clone();

    if !session.has_message(&partner, role) {
        return Ok(StepPack {
            coro_update: CoroUpdate::Block(BlockReason::RecvWait {
                endpoint: ep.clone(),
            }),
            type_update: None,
            events: vec![],
        });
    }

    let val = session
        .recv(&partner, role)
        .ok_or_else(|| Fault::ChannelClosed {
            endpoint: ep.clone(),
        })?;

    handler
        .handle_recv(role, &partner, &label.name, &mut coro.regs, &val)
        .map_err(|e| Fault::InvokeFault { message: e })?;

    let original = session
        .local_types
        .get(ep)
        .map(|entry| &entry.original)
        .unwrap_or(&LocalTypeR::End);
    let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePcWriteReg { reg: dst_reg, val },
        type_update,
        events: vec![ObsEvent::Received {
            tick,
            session: sid,
            from: partner,
            to: role.to_string(),
            label: label.name.clone(),
        }],
    })
}

fn step_halt(session: &mut SessionState, ep: &Endpoint, _tick: u64) -> Result<StepPack, Fault> {
    if let Some(lt) = session.local_types.get(ep) {
        if !matches!(lt.current, LocalTypeR::End) {
            // V1: permissive
        }
    }
    Ok(StepPack {
        coro_update: CoroUpdate::Halt,
        type_update: Some((ep.clone(), TypeUpdate::Remove)),
        events: vec![],
    })
}

fn step_invoke(
    coro: &mut Coroutine,
    role: &str,
    handler: &dyn EffectHandler,
    tick: u64,
) -> Result<StepPack, Fault> {
    let coro_id = coro.id;
    handler
        .step(role, &mut coro.regs)
        .map_err(|e| Fault::InvokeFault { message: e })?;

    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: None,
        events: vec![ObsEvent::Invoked {
            tick,
            coro_id,
            role: role.to_string(),
        }],
    })
}

fn step_choose(
    session: &mut SessionState,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    label: &str,
    target: PC,
    state: &[Value],
    handler: &dyn EffectHandler,
    tick: u64,
) -> Result<StepPack, Fault> {
    let local_type = session
        .local_types
        .get(ep)
        .ok_or_else(|| Fault::TypeViolation {
            message: format!("{role}: no type registered"),
        })?
        .current
        .clone();

    let (partner, branches) = match &local_type {
        LocalTypeR::Send {
            partner, branches, ..
        } => (partner.clone(), branches.clone()),
        other => {
            return Err(Fault::TypeViolation {
                message: format!("{role}: Choose expects Send, got {other:?}"),
            })
        }
    };

    let (_lbl, _vt, continuation) = branches
        .iter()
        .find(|(l, _, _)| l.name == label)
        .ok_or_else(|| Fault::UnknownLabel {
            label: label.to_string(),
        })?
        .clone();

    let decision = handler
        .send_decision(
            sid,
            role,
            &partner,
            label,
            state,
            Some(Value::Label(label.to_string())),
        )
        .map_err(|e| Fault::InvokeFault { message: e })?;
    let enqueue = match decision {
        SendDecision::Deliver(payload) => session
            .send(role, &partner, payload)
            .map_err(|e| Fault::InvokeFault { message: e })?,
        SendDecision::Drop | SendDecision::Defer => EnqueueResult::Dropped,
    };
    match enqueue {
        EnqueueResult::Ok => {}
        EnqueueResult::WouldBlock => {
            return Ok(StepPack {
                coro_update: CoroUpdate::Block(BlockReason::SendWait {
                    endpoint: ep.clone(),
                }),
                type_update: None,
                events: vec![],
            });
        }
        EnqueueResult::Full => {
            return Err(Fault::BufferFull {
                endpoint: ep.clone(),
            });
        }
        EnqueueResult::Dropped => {}
    }

    let original = session
        .local_types
        .get(ep)
        .map(|entry| &entry.original)
        .unwrap_or(&LocalTypeR::End);
    let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

    Ok(StepPack {
        coro_update: CoroUpdate::SetPc(target),
        type_update,
        events: vec![ObsEvent::Sent {
            tick,
            session: sid,
            from: role.to_string(),
            to: partner,
            label: label.to_string(),
        }],
    })
}

#[allow(clippy::too_many_lines, clippy::too_many_arguments)]
fn step_offer(
    coro: &mut Coroutine,
    session: &mut SessionState,
    ep: &Endpoint,
    role: &str,
    sid: SessionId,
    chan: u16,
    table: &[(String, PC)],
    handler: &dyn EffectHandler,
    tick: u64,
) -> Result<StepPack, Fault> {
    let local_type = session
        .local_types
        .get(ep)
        .ok_or_else(|| Fault::TypeViolation {
            message: format!("{role}: no type registered"),
        })?
        .current
        .clone();

    match &local_type {
        LocalTypeR::Recv {
            partner, branches, ..
        } => {
            let partner = partner.clone();
            let branches = branches.clone();

            if !session.has_message(&partner, role) {
                return Ok(StepPack {
                    coro_update: CoroUpdate::Block(BlockReason::RecvWait {
                        endpoint: ep.clone(),
                    }),
                    type_update: None,
                    events: vec![],
                });
            }

            let val = session
                .recv(&partner, role)
                .ok_or_else(|| Fault::ChannelClosed {
                    endpoint: ep.clone(),
                })?;

            let label = match &val {
                Value::Label(l) => l.clone(),
                _ => {
                    return Err(Fault::TypeViolation {
                        message: format!("{role}: Offer expected Label value, got {val:?}"),
                    })
                }
            };

            let (_lbl, _vt, continuation) = branches
                .iter()
                .find(|(l, _, _)| l.name == label)
                .ok_or_else(|| Fault::UnknownLabel {
                    label: label.clone(),
                })?
                .clone();

            let target_pc = table
                .iter()
                .find(|(l, _)| *l == label)
                .map(|(_, pc)| *pc)
                .ok_or_else(|| Fault::UnknownLabel {
                    label: label.clone(),
                })?;

            let original = session
                .local_types
                .get(ep)
                .map(|entry| &entry.original)
                .unwrap_or(&LocalTypeR::End);
            let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

            coro.regs[usize::from(chan)] = val;

            Ok(StepPack {
                coro_update: CoroUpdate::SetPc(target_pc),
                type_update,
                events: vec![ObsEvent::Received {
                    tick,
                    session: sid,
                    from: partner,
                    to: role.to_string(),
                    label,
                }],
            })
        }
        LocalTypeR::Send {
            partner, branches, ..
        } => {
            let partner = partner.clone();
            let branches = branches.clone();

            let available_labels: Vec<String> =
                branches.iter().map(|(l, _, _)| l.name.clone()).collect();
            let label = handler
                .handle_choose(role, &partner, &available_labels, &coro.regs)
                .map_err(|e| Fault::InvokeFault { message: e })?;

            let (_lbl, _vt, continuation) = branches
                .iter()
                .find(|(l, _, _)| l.name == label)
                .ok_or_else(|| Fault::UnknownLabel {
                    label: label.clone(),
                })?
                .clone();

            let target_pc = table
                .iter()
                .find(|(l, _)| *l == label)
                .map(|(_, pc)| *pc)
                .ok_or_else(|| Fault::UnknownLabel {
                    label: label.clone(),
                })?;

            let decision = handler
                .send_decision(
                    sid,
                    role,
                    &partner,
                    &label,
                    &coro.regs,
                    Some(Value::Label(label.clone())),
                )
                .map_err(|e| Fault::InvokeFault { message: e })?;
            let enqueue = match decision {
                SendDecision::Deliver(payload) => session
                    .send(role, &partner, payload)
                    .map_err(|e| Fault::InvokeFault { message: e })?,
                SendDecision::Drop | SendDecision::Defer => EnqueueResult::Dropped,
            };
            match enqueue {
                EnqueueResult::Ok => {}
                EnqueueResult::WouldBlock => {
                    return Ok(StepPack {
                        coro_update: CoroUpdate::Block(BlockReason::SendWait {
                            endpoint: ep.clone(),
                        }),
                        type_update: None,
                        events: vec![],
                    });
                }
                EnqueueResult::Full => {
                    return Err(Fault::BufferFull {
                        endpoint: ep.clone(),
                    });
                }
                EnqueueResult::Dropped => {}
            }

            let original = session
                .local_types
                .get(ep)
                .map(|entry| &entry.original)
                .unwrap_or(&LocalTypeR::End);
            let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

            Ok(StepPack {
                coro_update: CoroUpdate::SetPc(target_pc),
                type_update,
                events: vec![ObsEvent::Sent {
                    tick,
                    session: sid,
                    from: role.to_string(),
                    to: partner,
                    label,
                }],
            })
        }
        other => Err(Fault::TypeViolation {
            message: format!("{role}: Offer expects Send or Recv, got {other:?}"),
        }),
    }
}

fn step_close(
    session: &mut SessionState,
    ep: &Endpoint,
    sid: SessionId,
    tick: u64,
) -> Result<StepPack, Fault> {
    let has_pending = session.buffers.values().any(|b| !b.is_empty());
    if has_pending {
        session.status = SessionStatus::Draining;
    } else {
        session.status = SessionStatus::Closed;
    }

    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: Some((ep.clone(), TypeUpdate::Remove)),
        events: vec![ObsEvent::Closed { tick, session: sid }],
    })
}

fn step_open(
    store: &ThreadedSessionStore,
    roles: &[String],
    _endpoints: &[(String, u16)],
    tick: u64,
) -> Result<StepPack, Fault> {
    let sid = store.open(roles.to_vec(), &BufferConfig::default(), &BTreeMap::new());

    Ok(StepPack {
        coro_update: CoroUpdate::AdvancePc,
        type_update: None,
        events: vec![ObsEvent::Opened {
            tick,
            session: sid,
            roles: roles.to_vec(),
        }],
    })
}
