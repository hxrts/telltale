/// Required target-session disposal failed. No successful acknowledgment is
/// returned when protected state cannot be validated.
#[derive(Debug, thiserror::Error)]
pub enum ThreadedSessionLifecycleError {
    /// The requested live or archived session is absent.
    #[error("threaded session {session} does not exist")]
    MissingSession {
        /// Actual session selector that failed residency validation.
        session: SessionId,
    },
    /// A required internal lifecycle lock is genuinely poisoned.
    #[error("threaded session lifecycle lock is poisoned: {component}")]
    LockPoisoned {
        /// Protected state whose actual lock could not be acquired.
        component: &'static str,
    },
    /// The stable id/index ownership mapping is inconsistent.
    #[error("threaded coroutine index is inconsistent for {coroutine}")]
    InvalidCoroutineIndex {
        /// Actual resident coroutine whose ownership index is invalid.
        coroutine: usize,
    },
    /// Advancing the original session epoch would overflow.
    #[error("threaded session {session} epoch is exhausted")]
    EpochExhausted {
        /// Actual resident session with an exhausted epoch.
        session: SessionId,
    },
    /// The actual non-terminal custody counter cannot cover target retirement.
    #[error("threaded non-terminal coroutine count is inconsistent")]
    InvalidNonTerminalCount,
}

impl ThreadedProtocolMachine {
    fn coroutine_by_id(&self, id: usize) -> Option<&Arc<Mutex<Coroutine>>> {
        self.coroutine_indexes
            .get(&id)
            .and_then(|index| self.coroutines.get(*index))
    }

    fn validate_disposal_indices(
        &self,
        guards: &[std::sync::MutexGuard<'_, Coroutine>],
    ) -> Result<(), ThreadedSessionLifecycleError> {
        for (index, guard) in guards.iter().enumerate() {
            if self.coroutine_indexes.get(&guard.id) != Some(&index) {
                return Err(ThreadedSessionLifecycleError::InvalidCoroutineIndex {
                    coroutine: guard.id,
                });
            }
        }
        Ok(())
    }

    /// Close and remove exactly one session after its worker wave has completed.
    ///
    /// Every worker wave is scope-joined by `pool.install(...collect())` before
    /// a mutable step returns. Exclusive mutable entry here acknowledges that
    /// no target-session worker job remains. The shared pool and other sessions
    /// remain live. Repeated disposal returns the original compact summary.
    /// Historical observations are retained; they cannot resume the session.
    ///
    /// # Errors
    ///
    /// Returns a typed lifecycle error when residency, ownership indices,
    /// required locks, epoch arithmetic, or terminal counts fail preflight.
    /// Protected target state is not removed on failure.
    pub fn close_and_reap_session(
        &mut self,
        sid: SessionId,
    ) -> Result<crate::session::ClosedSessionSummary, ThreadedSessionLifecycleError> {
        use ThreadedSessionLifecycleError as Error;
        if let Some(summary) = self.reaped_sessions.get(&sid) {
            return Ok(summary.clone());
        }
        let target = self
            .sessions
            .sessions
            .read()
            .map_err(|_| Error::LockPoisoned {
                component: "session registry",
            })?
            .get(&sid)
            .cloned()
            .ok_or(Error::MissingSession { session: sid })?;
        // Clone the internal Arc references so all preflight locks can remain
        // held through mutation without borrowing the machine's live arrays.
        let coroutines = self.coroutines.clone();
        let mut guards = coroutines
            .iter()
            .map(|coro| {
                coro.lock().map_err(|_| Error::LockPoisoned {
                    component: "coroutine",
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        self.validate_disposal_indices(&guards)?;
        let mut session = target.lock().map_err(|_| Error::LockPoisoned {
            component: "target session",
        })?;
        let (already_terminal, next_epoch) = checked_disposal_epoch(&session)?;
        let resources = self.resource_states.clone();
        let mut resources = resources.lock().map_err(|_| Error::LockPoisoned {
            component: "session resources",
        })?;
        let consumption = self.communication_consumption.clone();
        let mut consumption = consumption.lock().map_err(|_| Error::LockPoisoned {
            component: "communication consumption",
        })?;
        // Registry access is checked before any mutation. The same exclusive
        // machine owner prevents a new worker wave throughout this operation.
        let registry = self
            .sessions
            .sessions
            .get_mut()
            .map_err(|_| Error::LockPoisoned {
                component: "session registry",
            })?;
        if !registry
            .get(&sid)
            .is_some_and(|current| Arc::ptr_eq(current, &target))
        {
            return Err(Error::MissingSession { session: sid });
        }
        let newly_terminal = guards
            .iter()
            .filter(|coro| coro.session_id == sid && !coro.is_terminal())
            .count();
        let non_terminal = self
            .non_terminal_coroutines
            .checked_sub(newly_terminal)
            .ok_or(Error::InvalidNonTerminalCount)?;
        if !already_terminal {
            session.status = SessionStatus::Closed;
        }
        session.epoch = next_epoch;
        let summary = crate::session::ClosedSessionSummary::from_session(&session);
        for coroutine in guards.iter_mut().filter(|coro| coro.session_id == sid) {
            coroutine.status = CoroStatus::Done;
            self.scheduler.unregister(coroutine.id);
        }
        let surviving: Vec<bool> = guards.iter().map(|coro| coro.session_id != sid).collect();
        let surviving_indexes: BTreeMap<usize, usize> = guards
            .iter()
            .filter(|coro| coro.session_id != sid)
            .map(|coro| coro.id)
            .enumerate()
            .map(|(index, id)| (id, index))
            .collect();
        registry.remove(&sid);
        resources.remove(&sid);
        consumption.prune_session(sid);
        drop(session);
        drop(guards);
        self.non_terminal_coroutines = non_terminal;
        let mut index = 0;
        self.coroutines.retain(|_| {
            let keep = surviving[index];
            index += 1;
            keep
        });
        self.coroutine_indexes = surviving_indexes;
        self.pending_handoffs
            .retain(|handoff| handoff.session != sid);
        self.invalidate_outstanding_effects_for_session(sid, "required session disposal");
        self.trace.push(ObsEvent::Closed {
            tick: self.clock.tick,
            session: sid,
        });
        self.reaped_sessions.insert(sid, summary.clone());
        Ok(summary)
    }
}

// This pure preflight reads the still-held target guard; it neither transfers
// ownership nor mutates terminal state. The caller keeps every custody lock.
fn checked_disposal_epoch(
    session: &SessionState,
) -> Result<(bool, usize), ThreadedSessionLifecycleError> {
    let already_terminal = matches!(
        session.status,
        SessionStatus::Closed | SessionStatus::Cancelled | SessionStatus::Faulted { .. }
    );
    let next_epoch = if already_terminal {
        session.epoch
    } else {
        session
            .epoch
            .checked_add(1)
            .ok_or(ThreadedSessionLifecycleError::EpochExhausted {
                session: session.sid,
            })?
    };
    Ok((already_terminal, next_epoch))
}
