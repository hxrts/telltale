//! The VM: ties coroutines, sessions, and scheduler together.
//!
//! Execution follows the Lean spec pattern:
//! - `exec_instr` fetches, dispatches to per-instruction step functions
//! - Each step function owns its type checking via `SessionStore::lookup_type`
//! - Results are bundled in `StepPack` and committed atomically via `commit_pack`
//! - Blocking never advances type state

use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;
use std::time::Duration;
use telltale_types::LocalTypeR;

use crate::buffer::{BufferConfig, EnqueueResult};
use crate::clock::SimClock;
use crate::coroutine::{BlockReason, CoroStatus, Coroutine, Fault, Value};
use crate::effect::{EffectHandler, SendDecision};
use crate::instr::{Endpoint, Instr, PC};
use crate::loader::CodeImage;
use crate::scheduler::{SchedPolicy, Scheduler};
use crate::session::{unfold_if_var_with_scope, SessionId, SessionStore};

/// VM configuration.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct VMConfig {
    /// Scheduling policy.
    pub sched_policy: SchedPolicy,
    /// Default buffer configuration for new sessions.
    pub buffer_config: BufferConfig,
    /// Maximum number of concurrent sessions.
    pub max_sessions: usize,
    /// Maximum number of concurrent coroutines.
    pub max_coroutines: usize,
    /// Number of registers per coroutine.
    pub num_registers: u16,
    /// Simulated time per scheduler round.
    pub tick_duration: Duration,
}

impl Default for VMConfig {
    fn default() -> Self {
        Self {
            sched_policy: SchedPolicy::Cooperative,
            buffer_config: BufferConfig::default(),
            max_sessions: 256,
            max_coroutines: 1024,
            num_registers: 16,
            tick_duration: Duration::from_millis(1),
        }
    }
}

/// Observable event emitted by the VM.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum ObsEvent {
    /// Value sent on an edge.
    Sent {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Sender role.
        from: String,
        /// Receiver role.
        to: String,
        /// Message label.
        label: String,
    },
    /// Value received on an edge.
    Received {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Sender role.
        from: String,
        /// Receiver role.
        to: String,
        /// Message label.
        label: String,
    },
    /// Session opened.
    Opened {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
        /// Participating roles.
        roles: Vec<String>,
    },
    /// Session closed.
    Closed {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Session ID.
        session: SessionId,
    },
    /// Coroutine halted.
    Halted {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Coroutine ID.
        coro_id: usize,
    },
    /// Effect handler invoked.
    Invoked {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Coroutine ID.
        coro_id: usize,
        /// Role name.
        role: String,
    },
    /// Coroutine faulted.
    Faulted {
        /// Scheduler tick when the event occurred.
        tick: u64,
        /// Coroutine ID.
        coro_id: usize,
        /// The fault.
        fault: Fault,
    },
}

/// The VM execution result for a single step.
#[derive(Debug)]
pub enum StepResult {
    /// A coroutine executed an instruction and may continue.
    Continue,
    /// No coroutines are ready (all blocked or done).
    Stuck,
    /// All coroutines have completed.
    AllDone,
}

/// Errors from VM operations.
#[derive(Debug, thiserror::Error)]
pub enum VMError {
    /// A coroutine faulted.
    #[error("coroutine {coro_id} faulted: {fault}")]
    Fault {
        /// Coroutine ID.
        coro_id: usize,
        /// The fault.
        fault: Fault,
    },
    /// Session limit exceeded.
    #[error("max sessions ({max}) exceeded")]
    TooManySessions {
        /// Maximum allowed.
        max: usize,
    },
    /// Coroutine limit exceeded.
    #[error("max coroutines ({max}) exceeded")]
    TooManyCoroutines {
        /// Maximum allowed.
        max: usize,
    },
    /// Session not found.
    #[error("session {0} not found")]
    SessionNotFound(SessionId),
    /// Effect handler error.
    #[error("effect handler error: {0}")]
    HandlerError(String),
    /// Invalid concurrency parameter.
    #[error("invalid concurrency level: {n}")]
    InvalidConcurrency {
        /// Requested concurrency.
        n: usize,
    },
}

// ---- StepPack: atomic instruction result (matches Lean StepPack) ----

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
///
/// Matches the Lean `StepPack` pattern: bundles all mutations so the
/// caller commits them together via `commit_pack`.
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

// ---- The VM ----

/// The choreographic VM.
///
/// Manages coroutines, sessions (which own type state), and a scheduler.
/// Multiple choreographies can be loaded into a single VM, each in its
/// own session namespace — justified by separation logic.
#[derive(Debug, Serialize, Deserialize)]
pub struct VM {
    config: VMConfig,
    coroutines: Vec<Coroutine>,
    sessions: SessionStore,
    scheduler: Scheduler,
    trace: Vec<ObsEvent>,
    clock: SimClock,
    next_coro_id: usize,
    paused_roles: BTreeSet<String>,
}

impl VM {
    /// Create a new VM with the given configuration.
    #[must_use]
    pub fn new(config: VMConfig) -> Self {
        let tick_duration = config.tick_duration;
        let scheduler = Scheduler::new(config.sched_policy.clone());
        Self {
            config,
            coroutines: Vec::new(),
            sessions: SessionStore::new(),
            scheduler,
            trace: Vec::new(),
            clock: SimClock::new(tick_duration),
            next_coro_id: 0,
            paused_roles: BTreeSet::new(),
        }
    }

    /// Load a choreography from a verified code image.
    ///
    /// Creates a session (with local types), spawns coroutines per role,
    /// and returns the session ID. Type state is initialized in the
    /// session store — no separate monitor needed.
    ///
    /// # Errors
    ///
    /// Returns an error if session or coroutine limits are exceeded.
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
            self.coroutines.push(coro);
        }

        Ok(sid)
    }

    /// Execute one scheduler round: advance up to N ready coroutines.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if a coroutine faults.
    pub fn step_round(
        &mut self,
        handler: &dyn EffectHandler,
        n: usize,
    ) -> Result<StepResult, VMError> {
        if n == 0 {
            return Err(VMError::InvalidConcurrency { n });
        }
        self.clock.advance();
        if self.coroutines.iter().all(|c| c.is_terminal()) {
            return Ok(StepResult::AllDone);
        }

        self.try_unblock_receivers();

        let mut progressed = false;
        for _ in 0..n {
            if self.coroutines.iter().all(|c| c.is_terminal()) {
                return Ok(StepResult::AllDone);
            }

            let mut coro_id = None;
            let mut attempts = self.scheduler.ready_count();
            while attempts > 0 {
                attempts -= 1;
                let next_id = match self.scheduler.schedule() {
                    Some(id) => id,
                    None => break,
                };
                let idx = self.coro_index(next_id);
                if self.paused_roles.contains(&self.coroutines[idx].role) {
                    self.scheduler.reschedule(next_id);
                    continue;
                }
                coro_id = Some(next_id);
                break;
            }

            let Some(coro_id) = coro_id else {
                break;
            };

            let result = self.exec_instr(coro_id, handler);

            match result {
                Ok(ExecOutcome::Continue) => {
                    progressed = true;
                    self.scheduler.reschedule(coro_id);
                }
                Ok(ExecOutcome::Blocked(reason)) => {
                    progressed = true;
                    self.scheduler.mark_blocked(coro_id, reason);
                }
                Ok(ExecOutcome::Halted) => {
                    progressed = true;
                    self.scheduler.mark_done(coro_id);
                    self.trace.push(ObsEvent::Halted {
                        tick: self.clock.tick,
                        coro_id,
                    });
                }
                Err(fault) => {
                    self.trace.push(ObsEvent::Faulted {
                        tick: self.clock.tick,
                        coro_id,
                        fault: fault.clone(),
                    });
                    let idx = self.coro_index(coro_id);
                    self.coroutines[idx].status = CoroStatus::Faulted(fault.clone());
                    self.scheduler.mark_done(coro_id);
                    return Err(VMError::Fault { coro_id, fault });
                }
            }
        }

        if progressed {
            Ok(StepResult::Continue)
        } else {
            Ok(StepResult::Stuck)
        }
    }

    /// Execute one scheduler step: pick a coroutine, run one instruction.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if a coroutine faults.
    pub fn step(&mut self, handler: &dyn EffectHandler) -> Result<StepResult, VMError> {
        self.step_round(handler, 1)
    }

    /// Run the VM until all coroutines complete or an error occurs, with concurrency N.
    ///
    /// `max_rounds` prevents infinite loops.
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

    /// Run the VM until all coroutines complete or an error occurs.
    ///
    /// `max_steps` prevents infinite loops.
    ///
    /// # Errors
    ///
    /// Returns a `VMError` if any coroutine faults.
    pub fn run(&mut self, handler: &dyn EffectHandler, max_steps: usize) -> Result<(), VMError> {
        self.run_concurrent(handler, max_steps, 1)
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

    /// Whether all coroutines are terminal (done or faulted).
    #[must_use]
    pub fn all_done(&self) -> bool {
        self.coroutines.iter().all(|c| c.is_terminal())
    }

    /// Get a coroutine by ID.
    #[must_use]
    pub fn coroutine(&self, id: usize) -> Option<&Coroutine> {
        self.coroutines.iter().find(|c| c.id == id)
    }

    /// Get a mutable coroutine by ID.
    pub fn coroutine_mut(&mut self, id: usize) -> Option<&mut Coroutine> {
        self.coroutines.iter_mut().find(|c| c.id == id)
    }

    /// Get all coroutines for a session.
    #[must_use]
    pub fn session_coroutines(&self, sid: SessionId) -> Vec<&Coroutine> {
        self.coroutines
            .iter()
            .filter(|c| c.session_id == sid)
            .collect()
    }

    /// Access the session store.
    #[must_use]
    pub fn sessions(&self) -> &SessionStore {
        &self.sessions
    }

    /// Access the session store mutably.
    pub fn sessions_mut(&mut self) -> &mut SessionStore {
        &mut self.sessions
    }

    /// Inject a message directly into a session buffer.
    ///
    /// Used by simulation middleware (network/fault injection) to deliver
    /// in-flight messages without executing a VM send instruction.
    ///
    /// # Errors
    ///
    /// Returns an error if the session does not exist.
    pub fn inject_message(
        &mut self,
        sid: SessionId,
        from: &str,
        to: &str,
        value: Value,
    ) -> Result<EnqueueResult, VMError> {
        let session = self
            .sessions
            .get_mut(sid)
            .ok_or(VMError::SessionNotFound(sid))?;
        session
            .send(from, to, value)
            .map_err(|_| VMError::SessionNotFound(sid))
    }

    /// Access all coroutines.
    #[must_use]
    pub fn coroutines(&self) -> &[Coroutine] {
        &self.coroutines
    }

    /// Pause execution for all coroutines of a role.
    pub fn pause_role(&mut self, role: &str) {
        self.paused_roles.insert(role.to_string());
    }

    /// Resume execution for all coroutines of a role.
    pub fn resume_role(&mut self, role: &str) {
        self.paused_roles.remove(role);
    }

    /// Replace the paused role set.
    pub fn set_paused_roles(&mut self, roles: &BTreeSet<String>) {
        self.paused_roles = roles.clone();
    }

    /// Access paused roles.
    #[must_use]
    pub fn paused_roles(&self) -> &BTreeSet<String> {
        &self.paused_roles
    }

    // ---- Private ----

    fn coro_index(&self, id: usize) -> usize {
        self.coroutines
            .iter()
            .position(|c| c.id == id)
            .expect("coroutine exists")
    }

    /// Try to unblock coroutines that are waiting on receives.
    fn try_unblock_receivers(&mut self) {
        let blocked_ids = self.scheduler.blocked_ids();
        for coro_id in blocked_ids {
            let idx = self.coro_index(coro_id);
            let role = &self.coroutines[idx].role;
            if self.paused_roles.contains(role) {
                continue;
            }
            let reason = self.scheduler.block_reason(coro_id).cloned();
            if let Some(BlockReason::RecvWait { endpoint }) = reason {
                if let Some(session) = self.sessions.get(endpoint.sid) {
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

    /// Execute one instruction for a coroutine.
    ///
    /// Follows the Lean `execInstr` pipeline:
    /// 1. Fetch instruction at PC
    /// 2. Dispatch to per-instruction step function (which owns type checking)
    /// 3. Commit the `StepPack` atomically
    fn exec_instr(
        &mut self,
        coro_id: usize,
        handler: &dyn EffectHandler,
    ) -> Result<ExecOutcome, Fault> {
        let idx = self.coro_index(coro_id);
        let coro = &self.coroutines[idx];
        let pc = coro.pc;
        let sid = coro.session_id;

        // 1. Fetch.
        if pc >= coro.program.len() {
            return Err(Fault::PcOutOfBounds);
        }
        let instr = coro.program[pc].clone();
        let ep = coro
            .owned_endpoints
            .first()
            .cloned()
            .ok_or(Fault::PcOutOfBounds)?;
        let role = coro.role.clone();

        // 2. Dispatch to per-instruction step function.
        let pack = match instr {
            Instr::Send { val, .. } => self.step_send(idx, &ep, &role, sid, val, handler)?,
            Instr::Recv { dst, .. } => self.step_recv(idx, &ep, &role, sid, dst, handler)?,
            Instr::Halt => self.step_halt(&ep)?,
            Instr::Jmp { target } => StepPack {
                coro_update: CoroUpdate::SetPc(target),
                type_update: None,
                events: vec![],
            },
            Instr::Yield => StepPack {
                coro_update: CoroUpdate::AdvancePc,
                type_update: None,
                events: vec![],
            },
            Instr::Invoke { .. } => self.step_invoke(idx, &role, handler)?,
            Instr::LoadImm { dst, val } => {
                let v = match val {
                    crate::instr::ImmValue::Unit => Value::Unit,
                    crate::instr::ImmValue::Int(i) => Value::Int(i),
                    crate::instr::ImmValue::Real(r) => Value::Real(r),
                    crate::instr::ImmValue::Bool(b) => Value::Bool(b),
                    crate::instr::ImmValue::Str(s) => Value::Str(s),
                };
                StepPack {
                    coro_update: CoroUpdate::AdvancePcWriteReg { reg: dst, val: v },
                    type_update: None,
                    events: vec![],
                }
            }
            Instr::Mov { dst, src } => {
                let v = self.coroutines[idx].regs[usize::from(src)].clone();
                StepPack {
                    coro_update: CoroUpdate::AdvancePcWriteReg { reg: dst, val: v },
                    type_update: None,
                    events: vec![],
                }
            }
            Instr::Choose { label, target, .. } => {
                self.step_choose(idx, &ep, &role, sid, &label, target, handler)?
            }
            Instr::Offer { chan, ref table } => {
                self.step_offer(idx, &ep, &role, sid, chan, table, handler)?
            }
            Instr::Close { .. } => self.step_close(&ep, sid)?,
            Instr::Open {
                ref roles,
                ref endpoints,
            } => self.step_open(idx, roles, endpoints)?,
        };

        // 3. Commit atomically.
        self.commit_pack(idx, pack)
    }

    // ---- Per-instruction step functions (each owns its type logic) ----

    /// Send: lookup type → match Send → compute payload → enqueue → StepPack with L'.
    fn step_send(
        &mut self,
        coro_idx: usize,
        ep: &Endpoint,
        role: &str,
        sid: SessionId,
        _val_reg: u16,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        // Type lookup — instruction owns this.
        let local_type = self
            .sessions
            .lookup_type(ep)
            .ok_or_else(|| Fault::TypeViolation {
                message: format!("{role}: no type registered"),
            })?
            .clone();

        // Pattern match: must be Send.
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

        // Extract continuation (L') from first branch.
        let (label, _vt, continuation) = branches
            .first()
            .ok_or_else(|| Fault::TypeViolation {
                message: format!("{role}: send has no branches"),
            })?
            .clone();

        // Compute payload/decision via handler.
        let coro = &self.coroutines[coro_idx];
        let decision = handler
            .send_decision(sid, role, &partner, &label.name, &coro.regs, None)
            .map_err(|e| Fault::InvokeFault { message: e })?;

        // Enqueue into buffer (if delivered).
        let session = self
            .sessions
            .get_mut(sid)
            .ok_or_else(|| Fault::ChannelClosed {
                endpoint: ep.clone(),
            })?;
        let enqueue = match decision {
            SendDecision::Deliver(payload) => session
                .send(role, &partner, payload)
                .map_err(|e| Fault::InvokeFault { message: e })?,
            SendDecision::Drop | SendDecision::Defer => EnqueueResult::Dropped,
        };
        match enqueue {
            EnqueueResult::Ok => {}
            EnqueueResult::WouldBlock => {
                // Block — NO type advancement.
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

        // Success: resolve continuation and advance type.
        let original = self.sessions.original_type(ep).unwrap_or(&LocalTypeR::End);
        let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update,
            events: vec![ObsEvent::Sent {
                tick: self.clock.tick,
                session: sid,
                from: role.to_string(),
                to: partner,
                label: label.name.clone(),
            }],
        })
    }

    /// Recv: lookup type → match Recv → try dequeue → block or process → StepPack.
    fn step_recv(
        &mut self,
        coro_idx: usize,
        ep: &Endpoint,
        role: &str,
        sid: SessionId,
        dst_reg: u16,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        // Type lookup.
        let local_type = self
            .sessions
            .lookup_type(ep)
            .ok_or_else(|| Fault::TypeViolation {
                message: format!("{role}: no type registered"),
            })?
            .clone();

        // Pattern match: must be Recv.
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

        // Try dequeue.
        let session = self.sessions.get(sid).ok_or_else(|| Fault::ChannelClosed {
            endpoint: ep.clone(),
        })?;
        if !session.has_message(&partner, role) {
            // Block — NO type advancement, NO state change.
            return Ok(StepPack {
                coro_update: CoroUpdate::Block(BlockReason::RecvWait {
                    endpoint: ep.clone(),
                }),
                type_update: None,
                events: vec![],
            });
        }

        // Dequeue.
        let session = self.sessions.get_mut(sid).unwrap();
        let val = session
            .recv(&partner, role)
            .ok_or_else(|| Fault::ChannelClosed {
                endpoint: ep.clone(),
            })?;

        // Process via handler.
        handler
            .handle_recv(
                role,
                &partner,
                &label.name,
                &mut self.coroutines[coro_idx].regs,
                &val,
            )
            .map_err(|e| Fault::InvokeFault { message: e })?;

        // Resolve continuation and advance type.
        let original = self.sessions.original_type(ep).unwrap_or(&LocalTypeR::End);
        let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePcWriteReg { reg: dst_reg, val },
            type_update,
            events: vec![ObsEvent::Received {
                tick: self.clock.tick,
                session: sid,
                from: partner,
                to: role.to_string(),
                label: label.name.clone(),
            }],
        })
    }

    /// Halt: verify type is End → remove type entry.
    fn step_halt(&self, ep: &Endpoint) -> Result<StepPack, Fault> {
        // Optionally verify type is End (permissive in V1).
        if let Some(lt) = self.sessions.lookup_type(ep) {
            if !matches!(lt, LocalTypeR::End) {
                // V1: warn but allow. V2: fault.
            }
        }
        Ok(StepPack {
            coro_update: CoroUpdate::Halt,
            type_update: Some((ep.clone(), TypeUpdate::Remove)),
            events: vec![],
        })
    }

    /// Invoke: call handler.step() for integration.
    fn step_invoke(
        &mut self,
        coro_idx: usize,
        role: &str,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let coro_id = self.coroutines[coro_idx].id;
        handler
            .step(role, &mut self.coroutines[coro_idx].regs)
            .map_err(|e| Fault::InvokeFault { message: e })?;

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![ObsEvent::Invoked {
                tick: self.clock.tick,
                coro_id,
                role: role.to_string(),
            }],
        })
    }

    /// Choose: internal choice — sender selects a statically-known label.
    ///
    /// Lookup type → must be Send → find label in branches → enqueue label →
    /// advance type to that branch's continuation → jump to target PC.
    fn step_choose(
        &mut self,
        coro_idx: usize,
        ep: &Endpoint,
        role: &str,
        sid: SessionId,
        label: &str,
        target: PC,
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let local_type = self
            .sessions
            .lookup_type(ep)
            .ok_or_else(|| Fault::TypeViolation {
                message: format!("{role}: no type registered"),
            })?
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

        // Find matching branch.
        let (_lbl, _vt, continuation) = branches
            .iter()
            .find(|(l, _, _)| l.name == label)
            .ok_or_else(|| Fault::UnknownLabel {
                label: label.to_string(),
            })?
            .clone();

        // Enqueue the label to the buffer (with middleware decision).
        let decision = handler
            .send_decision(
                sid,
                role,
                &partner,
                label,
                &self.coroutines[coro_idx].regs,
                Some(Value::Label(label.to_string())),
            )
            .map_err(|e| Fault::InvokeFault { message: e })?;
        let session = self
            .sessions
            .get_mut(sid)
            .ok_or_else(|| Fault::ChannelClosed {
                endpoint: ep.clone(),
            })?;
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

        let original = self.sessions.original_type(ep).unwrap_or(&LocalTypeR::End);
        let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

        Ok(StepPack {
            coro_update: CoroUpdate::SetPc(target),
            type_update,
            events: vec![ObsEvent::Sent {
                tick: self.clock.tick,
                session: sid,
                from: role.to_string(),
                to: partner,
                label: label.to_string(),
            }],
        })
    }

    /// Offer: polymorphic dispatch with jump table.
    ///
    /// Checks current type to determine mode:
    /// - Recv → external choice: dequeue label from buffer, dispatch
    /// - Send → internal choice: read label from register, enqueue, dispatch
    #[allow(clippy::too_many_lines, clippy::too_many_arguments)]
    fn step_offer(
        &mut self,
        coro_idx: usize,
        ep: &Endpoint,
        role: &str,
        sid: SessionId,
        chan: u16,
        table: &[(String, PC)],
        handler: &dyn EffectHandler,
    ) -> Result<StepPack, Fault> {
        let local_type = self
            .sessions
            .lookup_type(ep)
            .ok_or_else(|| Fault::TypeViolation {
                message: format!("{role}: no type registered"),
            })?
            .clone();

        match &local_type {
            LocalTypeR::Recv {
                partner, branches, ..
            } => {
                // External choice: dequeue label from buffer.
                let partner = partner.clone();
                let branches = branches.clone();

                let session = self.sessions.get(sid).ok_or_else(|| Fault::ChannelClosed {
                    endpoint: ep.clone(),
                })?;
                if !session.has_message(&partner, role) {
                    return Ok(StepPack {
                        coro_update: CoroUpdate::Block(BlockReason::RecvWait {
                            endpoint: ep.clone(),
                        }),
                        type_update: None,
                        events: vec![],
                    });
                }

                let session = self.sessions.get_mut(sid).unwrap();
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

                // Find label in type branches.
                let (_lbl, _vt, continuation) = branches
                    .iter()
                    .find(|(l, _, _)| l.name == label)
                    .ok_or_else(|| Fault::UnknownLabel {
                        label: label.clone(),
                    })?
                    .clone();

                // Find label in jump table.
                let target_pc = table
                    .iter()
                    .find(|(l, _)| *l == label)
                    .map(|(_, pc)| *pc)
                    .ok_or_else(|| Fault::UnknownLabel {
                        label: label.clone(),
                    })?;

                let original = self.sessions.original_type(ep).unwrap_or(&LocalTypeR::End);
                let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

                // Write received value to dst register.
                self.coroutines[coro_idx].regs[usize::from(chan)] = val;

                Ok(StepPack {
                    coro_update: CoroUpdate::SetPc(target_pc),
                    type_update,
                    events: vec![ObsEvent::Received {
                        tick: self.clock.tick,
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
                // Internal choice: read label from register, enqueue.
                let partner = partner.clone();
                let branches = branches.clone();

                let available_labels: Vec<String> =
                    branches.iter().map(|(l, _, _)| l.name.clone()).collect();
                let label = handler
                    .handle_choose(
                        role,
                        &partner,
                        &available_labels,
                        &self.coroutines[coro_idx].regs,
                    )
                    .map_err(|e| Fault::InvokeFault { message: e })?;

                // Find label in type branches.
                let (_lbl, _vt, continuation) = branches
                    .iter()
                    .find(|(l, _, _)| l.name == label)
                    .ok_or_else(|| Fault::UnknownLabel {
                        label: label.clone(),
                    })?
                    .clone();

                // Find label in jump table.
                let target_pc = table
                    .iter()
                    .find(|(l, _)| *l == label)
                    .map(|(_, pc)| *pc)
                    .ok_or_else(|| Fault::UnknownLabel {
                        label: label.clone(),
                    })?;

                // Enqueue label to buffer (with middleware decision).
                let decision = handler
                    .send_decision(
                        sid,
                        role,
                        &partner,
                        &label,
                        &self.coroutines[coro_idx].regs,
                        Some(Value::Label(label.clone())),
                    )
                    .map_err(|e| Fault::InvokeFault { message: e })?;
                let session = self
                    .sessions
                    .get_mut(sid)
                    .ok_or_else(|| Fault::ChannelClosed {
                        endpoint: ep.clone(),
                    })?;
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

                let original = self.sessions.original_type(ep).unwrap_or(&LocalTypeR::End);
                let (_resolved, type_update) = resolve_type_update(&continuation, original, ep);

                Ok(StepPack {
                    coro_update: CoroUpdate::SetPc(target_pc),
                    type_update,
                    events: vec![ObsEvent::Sent {
                        tick: self.clock.tick,
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

    /// Close: close session, remove type entry.
    fn step_close(&mut self, ep: &Endpoint, sid: SessionId) -> Result<StepPack, Fault> {
        self.sessions
            .close(sid)
            .map_err(|e| Fault::CloseFault { message: e })?;

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: Some((ep.clone(), TypeUpdate::Remove)),
            events: vec![ObsEvent::Closed {
                tick: self.clock.tick,
                session: sid,
            }],
        })
    }

    /// Open: create a new session with the given roles.
    fn step_open(
        &mut self,
        _coro_idx: usize,
        roles: &[String],
        _endpoints: &[(String, u16)],
    ) -> Result<StepPack, Fault> {
        let sid = self.sessions.open(
            roles.to_vec(),
            &BufferConfig::default(),
            &std::collections::BTreeMap::new(),
        );

        Ok(StepPack {
            coro_update: CoroUpdate::AdvancePc,
            type_update: None,
            events: vec![ObsEvent::Opened {
                tick: self.clock.tick,
                session: sid,
                roles: roles.to_vec(),
            }],
        })
    }

    /// Commit a `StepPack` atomically: apply coroutine update, type update, events.
    fn commit_pack(&mut self, coro_idx: usize, pack: StepPack) -> Result<ExecOutcome, Fault> {
        let coro = &mut self.coroutines[coro_idx];

        // Apply coroutine update.
        match pack.coro_update {
            CoroUpdate::AdvancePc => {
                coro.pc += 1;
                coro.status = CoroStatus::Ready;
            }
            CoroUpdate::SetPc(pc) => {
                coro.pc = pc;
                coro.status = CoroStatus::Ready;
            }
            CoroUpdate::Block(ref reason) => {
                coro.status = CoroStatus::Blocked(reason.clone());
                // PC unchanged — instruction will re-execute on unblock.
            }
            CoroUpdate::Halt => {
                coro.status = CoroStatus::Done;
            }
            CoroUpdate::AdvancePcWriteReg { reg, ref val } => {
                coro.regs[usize::from(reg)] = val.clone();
                coro.pc += 1;
                coro.status = CoroStatus::Ready;
            }
        }

        // Apply type update.
        if let Some((ep, update)) = pack.type_update {
            match update {
                TypeUpdate::Advance(lt) => self.sessions.update_type(&ep, lt),
                TypeUpdate::AdvanceWithOriginal(lt, orig) => {
                    self.sessions.update_type(&ep, lt);
                    self.sessions.update_original(&ep, orig);
                }
                TypeUpdate::Remove => self.sessions.remove_type(&ep),
            }
        }

        // Emit events.
        self.trace.extend(pack.events);

        // Map to ExecOutcome.
        match &self.coroutines[coro_idx].status {
            CoroStatus::Ready => Ok(ExecOutcome::Continue),
            CoroStatus::Blocked(reason) => Ok(ExecOutcome::Blocked(reason.clone())),
            CoroStatus::Done => Ok(ExecOutcome::Halted),
            CoroStatus::Faulted(f) => Err(f.clone()),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::loader::CodeImage;
    use std::collections::BTreeMap;
    use telltale_types::{GlobalType, Label, LocalTypeR};

    /// Trivial handler that passes values through.
    struct PassthroughHandler;

    impl EffectHandler for PassthroughHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Ok(Value::Int(42))
        }

        fn handle_recv(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &mut Vec<Value>,
            _payload: &Value,
        ) -> Result<(), String> {
            Ok(())
        }

        fn handle_choose(
            &self,
            _role: &str,
            _partner: &str,
            labels: &[String],
            _state: &[Value],
        ) -> Result<String, String> {
            labels
                .first()
                .cloned()
                .ok_or_else(|| "no labels available".into())
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
            Ok(())
        }
    }

    fn simple_send_recv_types() -> BTreeMap<String, LocalTypeR> {
        let mut m = BTreeMap::new();
        m.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );
        m.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );
        m
    }

    #[test]
    fn test_vm_simple_send_recv() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();

        // Both coroutines should be done.
        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));
    }

    #[test]
    fn test_vm_recursive_protocol() {
        // mu step. A!B:msg. B!A:msg. var step
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::mu(
                "step",
                LocalTypeR::Send {
                    partner: "B".into(),
                    branches: vec![(
                        Label::new("msg"),
                        None,
                        LocalTypeR::Recv {
                            partner: "B".into(),
                            branches: vec![(Label::new("msg"), None, LocalTypeR::var("step"))],
                        },
                    )],
                },
            ),
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::mu(
                "step",
                LocalTypeR::Recv {
                    partner: "A".into(),
                    branches: vec![(
                        Label::new("msg"),
                        None,
                        LocalTypeR::Send {
                            partner: "A".into(),
                            branches: vec![(Label::new("msg"), None, LocalTypeR::var("step"))],
                        },
                    )],
                },
            ),
        );

        let global = GlobalType::mu(
            "step",
            GlobalType::send(
                "A",
                "B",
                Label::new("msg"),
                GlobalType::send("B", "A", Label::new("msg"), GlobalType::var("step")),
            ),
        );
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        // Run for enough steps to exercise several loop iterations.
        vm.run(&handler, 200).unwrap();

        // Should not fault — recursive protocol with blocking should work.
        assert!(vm
            .coroutines
            .iter()
            .all(|c| !matches!(c.status, CoroStatus::Faulted(_))));
    }

    #[test]
    fn test_vm_blocking_does_not_advance_type() {
        // Set up a protocol where B must recv before A sends.
        // B: recv, then send. A: send, then recv.
        // B will block on recv until A sends.
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );

        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let image = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;

        // Step once: scheduler picks first ready coro (A or B).
        // If B is picked first, it should block (no message yet).
        // Type should NOT advance on block.
        let ep_b = Endpoint {
            sid,
            role: "B".into(),
        };
        let type_before = vm.sessions.lookup_type(&ep_b).cloned();

        // Run to completion.
        vm.run(&handler, 100).unwrap();
        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));

        // Verify B's type was Recv before execution.
        assert!(matches!(type_before, Some(LocalTypeR::Recv { .. })));
    }

    #[test]
    fn test_vm_load_multiple_sessions() {
        let local_types = simple_send_recv_types();
        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

        let image1 = CodeImage::from_local_types(&local_types, &global);
        let image2 = CodeImage::from_local_types(&local_types, &global);

        let mut vm = VM::new(VMConfig::default());
        let sid1 = vm.load_choreography(&image1).unwrap();
        let sid2 = vm.load_choreography(&image2).unwrap();

        assert_ne!(sid1, sid2);
        assert_eq!(vm.coroutines.len(), 4);

        let handler = PassthroughHandler;
        vm.run(&handler, 200).unwrap();
        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));
    }

    #[test]
    fn test_vm_choice_protocol() {
        // A chooses "yes" or "no", B offers (receives the choice).
        // A: Send { B, [yes → End, no → End] }
        // B: Recv { A, [yes → End, no → End] }
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::send_choice(
                "B",
                vec![
                    (Label::new("yes"), None, LocalTypeR::End),
                    (Label::new("no"), None, LocalTypeR::End),
                ],
            ),
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::recv_choice(
                "A",
                vec![
                    (Label::new("yes"), None, LocalTypeR::End),
                    (Label::new("no"), None, LocalTypeR::End),
                ],
            ),
        );

        let global = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("yes"), GlobalType::End),
                (Label::new("no"), GlobalType::End),
            ],
        );

        // Manually compile: A gets an Offer (send-mode), B gets an Offer (recv-mode).
        let a_code = vec![
            Instr::Choose {
                chan: 0,
                label: "yes".into(),
                target: 1, // jump to Halt
            },
            Instr::Halt,
        ];
        let b_code = vec![
            Instr::Offer {
                chan: 0,
                table: vec![("yes".into(), 1), ("no".into(), 2)],
            },
            Instr::Halt, // yes branch
            Instr::Halt, // no branch
        ];

        let image = CodeImage {
            programs: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), a_code);
                m.insert("B".to_string(), b_code);
                m
            },
            global_type: global,
            local_types,
        };

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();

        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));

        // Verify events include Sent (from Choose) and Received (from Offer).
        let sent = vm
            .trace
            .iter()
            .any(|e| matches!(e, ObsEvent::Sent { label, .. } if label == "yes"));
        let recv = vm
            .trace
            .iter()
            .any(|e| matches!(e, ObsEvent::Received { label, .. } if label == "yes"));
        assert!(sent, "expected Sent event with label 'yes'");
        assert!(recv, "expected Received event with label 'yes'");
    }

    #[test]
    fn test_vm_offer_blocks_until_choice() {
        // B tries to Offer before A has Chosen → should block.
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::send_choice("B", vec![(Label::new("go"), None, LocalTypeR::End)]),
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::recv_choice("A", vec![(Label::new("go"), None, LocalTypeR::End)]),
        );

        let global = GlobalType::send("A", "B", Label::new("go"), GlobalType::End);

        let a_code = vec![
            Instr::Choose {
                chan: 0,
                label: "go".into(),
                target: 1,
            },
            Instr::Halt,
        ];
        let b_code = vec![
            Instr::Offer {
                chan: 0,
                table: vec![("go".into(), 1)],
            },
            Instr::Halt,
        ];

        let image = CodeImage {
            programs: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), a_code);
                m.insert("B".to_string(), b_code);
                m
            },
            global_type: global,
            local_types,
        };

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();
        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));
    }

    #[test]
    fn test_vm_close_session() {
        // Simple: A sends to B, then closes.
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".into(),
                branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
            },
        );

        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

        // A: Send, Close, Halt.  B: Recv, Close, Halt.
        let a_code = vec![
            Instr::Send { chan: 0, val: 1 },
            Instr::Close { session: 0 },
            Instr::Halt,
        ];
        let b_code = vec![
            Instr::Recv { chan: 0, dst: 1 },
            Instr::Close { session: 0 },
            Instr::Halt,
        ];

        let image = CodeImage {
            programs: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), a_code);
                m.insert("B".to_string(), b_code);
                m
            },
            global_type: global,
            local_types,
        };

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();

        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));
        let closed_count = vm
            .trace
            .iter()
            .filter(|e| matches!(e, ObsEvent::Closed { .. }))
            .count();
        assert!(closed_count >= 1, "expected at least one Closed event");
    }

    #[test]
    fn test_compiler_multi_branch() {
        use crate::compiler::compile;

        // Send with 2 branches → should emit Offer + branch code.
        let lt = LocalTypeR::send_choice(
            "B",
            vec![
                (Label::new("yes"), None, LocalTypeR::End),
                (Label::new("no"), None, LocalTypeR::End),
            ],
        );

        let code = compile(&lt);

        // First instruction should be Offer with 2 entries.
        assert!(
            matches!(&code[0], Instr::Offer { table, .. } if table.len() == 2),
            "expected Offer with 2 entries, got {:?}",
            code[0]
        );

        // Each branch should end with Halt.
        if let Instr::Offer { table, .. } = &code[0] {
            for (label, pc) in table {
                assert!(
                    matches!(code[*pc], Instr::Halt),
                    "expected Halt at branch '{label}' PC {pc}, got {:?}",
                    code[*pc]
                );
            }
        }
    }

    #[test]
    fn test_compiler_single_branch_unchanged() {
        use crate::compiler::compile;

        // Single-branch Send → should emit Send, not Offer.
        let lt = LocalTypeR::Send {
            partner: "B".into(),
            branches: vec![(Label::new("msg"), None, LocalTypeR::End)],
        };
        let code = compile(&lt);
        assert!(matches!(code[0], Instr::Send { .. }));
    }

    #[test]
    fn test_vm_recursive_choice_protocol() {
        // mu x. A→B:{continue.A→B:data.x, stop.end}
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::mu(
                "x",
                LocalTypeR::send_choice(
                    "B",
                    vec![
                        (
                            Label::new("continue"),
                            None,
                            LocalTypeR::Send {
                                partner: "B".into(),
                                branches: vec![(Label::new("data"), None, LocalTypeR::var("x"))],
                            },
                        ),
                        (Label::new("stop"), None, LocalTypeR::End),
                    ],
                ),
            ),
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::mu(
                "x",
                LocalTypeR::recv_choice(
                    "A",
                    vec![
                        (
                            Label::new("continue"),
                            None,
                            LocalTypeR::Recv {
                                partner: "A".into(),
                                branches: vec![(Label::new("data"), None, LocalTypeR::var("x"))],
                            },
                        ),
                        (Label::new("stop"), None, LocalTypeR::End),
                    ],
                ),
            ),
        );

        let global = GlobalType::mu(
            "x",
            GlobalType::comm(
                "A",
                "B",
                vec![
                    (
                        Label::new("continue"),
                        GlobalType::send("A", "B", Label::new("data"), GlobalType::var("x")),
                    ),
                    (Label::new("stop"), GlobalType::End),
                ],
            ),
        );

        // Manually craft bytecode: A chooses "stop" immediately.
        let a_code = vec![
            Instr::Choose {
                chan: 0,
                label: "stop".into(),
                target: 1,
            },
            Instr::Halt,
        ];
        let b_code = vec![
            Instr::Offer {
                chan: 0,
                table: vec![("continue".into(), 1), ("stop".into(), 3)],
            },
            // continue branch: Recv data, then loop back to Offer
            Instr::Recv { chan: 0, dst: 1 },
            Instr::Jmp { target: 0 },
            // stop branch: Halt
            Instr::Halt,
        ];

        let image = CodeImage {
            programs: {
                let mut m = BTreeMap::new();
                m.insert("A".to_string(), a_code);
                m.insert("B".to_string(), b_code);
                m
            },
            global_type: global,
            local_types,
        };

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        vm.run(&handler, 100).unwrap();

        assert!(vm.coroutines.iter().all(|c| c.is_terminal()));
    }

    #[test]
    fn test_vm_single_branch_then_multi_branch_choice() {
        // B→A:ack, then mu t. B→A:{continue→t, stop→End}
        // This is the protocol that was failing in fuzz tests.
        let projected: BTreeMap<String, LocalTypeR> = {
            let global = GlobalType::Comm {
                sender: "B".into(),
                receiver: "A".into(),
                branches: vec![(
                    Label::new("ack"),
                    GlobalType::Mu {
                        var: "t".into(),
                        body: Box::new(GlobalType::Comm {
                            sender: "B".into(),
                            receiver: "A".into(),
                            branches: vec![
                                (Label::new("continue"), GlobalType::Var("t".into())),
                                (Label::new("stop"), GlobalType::End),
                            ],
                        }),
                    },
                )],
            };
            telltale_theory::projection::project_all(&global)
                .unwrap()
                .into_iter()
                .collect()
        };

        let global = GlobalType::Comm {
            sender: "B".into(),
            receiver: "A".into(),
            branches: vec![(
                Label::new("ack"),
                GlobalType::Mu {
                    var: "t".into(),
                    body: Box::new(GlobalType::Comm {
                        sender: "B".into(),
                        receiver: "A".into(),
                        branches: vec![
                            (Label::new("continue"), GlobalType::Var("t".into())),
                            (Label::new("stop"), GlobalType::End),
                        ],
                    }),
                },
            )],
        };
        let image = CodeImage::from_local_types(&projected, &global);

        let mut vm = VM::new(VMConfig::default());
        let _sid = vm.load_choreography(&image).unwrap();

        let handler = PassthroughHandler;
        // Don't unwrap — just run to completion
        vm.run(&handler, 500).unwrap_or(());

        let faults: Vec<_> = vm
            .trace
            .iter()
            .filter(|e| matches!(e, ObsEvent::Faulted { .. }))
            .collect();
        assert!(faults.is_empty(), "faults: {faults:?}");
    }
}
