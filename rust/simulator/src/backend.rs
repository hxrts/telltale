//! Internal simulator machine backend abstraction.

use std::collections::{BTreeMap, BTreeSet};

use telltale_machine::clock::SimClock;
use telltale_machine::coroutine::{Coroutine, Value};
use telltale_machine::model::effects::{EffectExchangeRecord, EffectHandler, EffectTraceEntry};
use telltale_machine::model::output_condition::OutputConditionCheck;
use telltale_machine::model::semantic_objects::ProtocolMachineSemanticObjects;
use telltale_machine::model::state::{SessionId, SessionState};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{
    ObsEvent, OwnedSession, ProtocolMachine, ProtocolMachineConfig, ProtocolMachineError,
    SemanticAuditRecord, StepResult, ThreadedRoundSemantics,
};

use crate::scenario::{ResolvedExecution, ResolvedExecutionBackend};

#[allow(clippy::large_enum_variant)]
pub enum SimulationMachine {
    Canonical(ProtocolMachine),
    #[cfg(feature = "multi-thread")]
    Threaded(telltale_machine::ThreadedProtocolMachine),
}

impl SimulationMachine {
    #[must_use]
    pub fn new(config: ProtocolMachineConfig, execution: &ResolvedExecution) -> Self {
        let mut config = config;
        // The simulator must opt into the proof-aligned threaded semantics explicitly
        // rather than relying on the protocol-machine default transitively.
        config.threaded_round_semantics = ThreadedRoundSemantics::CanonicalOneStep;
        match execution.backend {
            ResolvedExecutionBackend::Canonical => Self::Canonical(ProtocolMachine::new(config)),
            #[cfg(feature = "multi-thread")]
            ResolvedExecutionBackend::Threaded => {
                Self::Threaded(telltale_machine::ThreadedProtocolMachine::with_workers(
                    config,
                    usize::try_from(execution.worker_threads)
                        .unwrap_or(usize::MAX)
                        .max(1),
                ))
            }
            #[cfg(not(feature = "multi-thread"))]
            ResolvedExecutionBackend::Threaded => {
                unreachable!("threaded execution requires simulator feature `multi-thread`")
            }
        }
    }

    pub fn load_choreography_owned(
        &mut self,
        image: &CodeImage,
        owner_id: impl Into<String>,
    ) -> Result<OwnedSession, ProtocolMachineError> {
        match self {
            Self::Canonical(machine) => machine.load_choreography_owned(image, owner_id),
            #[cfg(feature = "multi-thread")]
            Self::Threaded(machine) => machine.load_choreography_owned(image, owner_id),
        }
    }

    pub fn session_coroutines(&self, sid: SessionId) -> Vec<Coroutine> {
        match self {
            Self::Canonical(machine) => machine
                .session_coroutines(sid)
                .into_iter()
                .cloned()
                .collect(),
            #[cfg(feature = "multi-thread")]
            Self::Threaded(machine) => machine.session_coroutines(sid),
        }
    }

    pub fn coroutines(&self) -> Vec<Coroutine> {
        match self {
            Self::Canonical(machine) => machine.coroutines().to_vec(),
            #[cfg(feature = "multi-thread")]
            Self::Threaded(machine) => machine.coroutines(),
        }
    }

    pub fn session_snapshots(&self) -> BTreeMap<SessionId, SessionState> {
        match self {
            Self::Canonical(machine) => machine
                .sessions()
                .iter()
                .map(|session| (session.sid, session.clone()))
                .collect(),
            #[cfg(feature = "multi-thread")]
            Self::Threaded(machine) => machine.session_snapshots(),
        }
    }

    pub fn overwrite_coroutine_registers(
        &mut self,
        coro_id: usize,
        start: usize,
        values: &[Value],
    ) -> Result<(), String> {
        match self {
            Self::Canonical(machine) => {
                let Some(coro) = machine.coroutine_mut(coro_id) else {
                    return Err(format!("missing coroutine {coro_id}"));
                };
                if start > coro.regs.len() || start.saturating_add(values.len()) > coro.regs.len() {
                    return Err(format!(
                        "register update out of bounds for coroutine {coro_id}: start={start}, len={}",
                        values.len()
                    ));
                }
                for (offset, value) in values.iter().cloned().enumerate() {
                    coro.regs[start + offset] = value;
                }
                Ok(())
            }
            #[cfg(feature = "multi-thread")]
            Self::Threaded(machine) => {
                machine.overwrite_coroutine_registers(coro_id, start, values)
            }
        }
    }

    pub fn clock(&self) -> &SimClock {
        match self {
            Self::Canonical(machine) => machine.clock(),
            #[cfg(feature = "multi-thread")]
            Self::Threaded(machine) => machine.clock(),
        }
    }

    pub fn trace(&self) -> &[ObsEvent] {
        match self {
            Self::Canonical(machine) => machine.trace(),
            #[cfg(feature = "multi-thread")]
            Self::Threaded(machine) => machine.trace(),
        }
    }

    pub fn inject_message(
        &mut self,
        sid: SessionId,
        from: &str,
        to: &str,
        value: Value,
    ) -> Result<telltale_machine::buffer::EnqueueResult, ProtocolMachineError> {
        match self {
            Self::Canonical(machine) => machine.inject_message(sid, from, to, value),
            #[cfg(feature = "multi-thread")]
            Self::Threaded(machine) => machine.inject_message(sid, from, to, value),
        }
    }

    pub fn set_paused_roles(&mut self, roles: &BTreeSet<String>) {
        match self {
            Self::Canonical(machine) => machine.set_paused_roles(roles),
            #[cfg(feature = "multi-thread")]
            Self::Threaded(machine) => machine.set_paused_roles(roles),
        }
    }

    pub fn step_round(
        &mut self,
        handler: &dyn EffectHandler,
        concurrency: usize,
    ) -> Result<StepResult, ProtocolMachineError> {
        match self {
            Self::Canonical(machine) => machine.step_round(handler, concurrency),
            #[cfg(feature = "multi-thread")]
            Self::Threaded(machine) => machine.step_round(handler, concurrency),
        }
    }

    pub fn effect_trace(&self) -> &[EffectTraceEntry] {
        match self {
            Self::Canonical(machine) => machine.effect_trace(),
            #[cfg(feature = "multi-thread")]
            Self::Threaded(machine) => machine.effect_trace(),
        }
    }

    pub fn effect_exchanges(&self) -> &[EffectExchangeRecord] {
        match self {
            Self::Canonical(machine) => machine.effect_exchanges(),
            #[cfg(feature = "multi-thread")]
            Self::Threaded(machine) => machine.effect_exchanges(),
        }
    }

    pub fn output_condition_checks(&self) -> &[OutputConditionCheck] {
        match self {
            Self::Canonical(machine) => machine.output_condition_checks(),
            #[cfg(feature = "multi-thread")]
            Self::Threaded(machine) => machine.output_condition_checks(),
        }
    }

    pub fn semantic_audit_log(&self) -> Vec<SemanticAuditRecord> {
        match self {
            Self::Canonical(machine) => machine.semantic_audit_log(),
            #[cfg(feature = "multi-thread")]
            Self::Threaded(machine) => machine.semantic_audit_log(),
        }
    }

    pub fn semantic_objects(&self) -> ProtocolMachineSemanticObjects {
        match self {
            Self::Canonical(machine) => machine.semantic_objects(),
            #[cfg(feature = "multi-thread")]
            Self::Threaded(machine) => machine.semantic_objects(),
        }
    }
}
