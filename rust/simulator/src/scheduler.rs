//! Single-threaded deterministic scheduler for choreographic simulation.
//!
//! Manages multiple concurrent choreographies, each with its own set of roles.
//! Roles execute local type state machines and exchange messages through
//! in-memory channels.

use serde_json::Value;
use std::collections::{BTreeMap, HashMap, VecDeque};
use telltale_types::LocalTypeR;
use thiserror::Error;

use crate::trace::{StepRecord, Trace};

/// Errors from scheduler operations.
#[derive(Debug, Error)]
pub enum SchedulerError {
    /// A role tried to send but no matching receive was expected.
    #[error("no matching receive for send from {sender} to {receiver}")]
    NoMatchingReceive {
        /// Sending role.
        sender: String,
        /// Intended receiver.
        receiver: String,
    },

    /// Effect handler returned an error.
    #[error("effect handler error: {0}")]
    HandlerError(String),

    /// A role's local type is exhausted but the scheduler expected more steps.
    #[error("role {0} has no more protocol steps")]
    RoleExhausted(String),
}

/// Identifies a choreography instance within the scheduler.
pub type ChoreographyId = usize;

/// A message in transit between two roles.
#[derive(Debug, Clone)]
struct Message {
    /// Label name from the protocol.
    _label: String,
    /// Payload value.
    payload: Value,
}

/// Per-role state within a choreography.
struct RoleState {
    /// Current local type (remaining protocol).
    local_type: LocalTypeR,
    /// Original local type for unfolding recursive variables.
    original_type: LocalTypeR,
    /// Current state vector (concentrations, positions, etc.).
    state: Vec<f64>,
}

/// A single choreography instance with its roles and message queues.
struct Choreography {
    /// Per-role states (BTreeMap for deterministic iteration order).
    roles: BTreeMap<String, RoleState>,
    /// Message queues keyed by (sender, receiver).
    queues: HashMap<(String, String), VecDeque<Message>>,
}

/// Trait for material-specific effect handling.
///
/// Implementors define what happens at each protocol step: computing drift,
/// advancing state, and producing message payloads.
pub trait EffectHandler: Send {
    /// Handle a send action: compute the payload to send.
    ///
    /// # Errors
    ///
    /// Returns an error string if the handler fails.
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[f64],
    ) -> Result<Value, String>;

    /// Handle a receive action: update role state based on received payload.
    ///
    /// # Errors
    ///
    /// Returns an error string if the handler fails.
    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<f64>,
        payload: &Value,
    ) -> Result<(), String>;

    /// Advance the role's state by one integration step.
    ///
    /// Called after all sends/receives for a protocol tick are complete.
    ///
    /// # Errors
    ///
    /// Returns an error string if the handler fails.
    fn step(&self, role: &str, state: &mut Vec<f64>) -> Result<(), String>;
}

/// Single-threaded deterministic scheduler.
///
/// Runs multiple choreographies concurrently, stepping through each role's
/// local type protocol. Choreographies are independent: messages do not
/// cross choreography boundaries.
pub struct Scheduler {
    choreographies: Vec<Choreography>,
}

impl Scheduler {
    /// Create an empty scheduler.
    #[must_use]
    pub fn new() -> Self {
        Self {
            choreographies: Vec::new(),
        }
    }

    /// Register a new choreography with projected local types and initial states.
    ///
    /// Returns the choreography ID for later reference.
    pub fn add_choreography(
        &mut self,
        projections: HashMap<String, LocalTypeR>,
        initial_states: &HashMap<String, Vec<f64>>,
    ) -> ChoreographyId {
        let id = self.choreographies.len();

        let role_names: Vec<String> = projections.keys().cloned().collect();
        let mut queues = HashMap::new();
        for sender in &role_names {
            for receiver in &role_names {
                if sender != receiver {
                    queues.insert((sender.clone(), receiver.clone()), VecDeque::new());
                }
            }
        }

        let roles = projections
            .into_iter()
            .map(|(name, local_type)| {
                let state = initial_states
                    .get(&name)
                    .cloned()
                    .unwrap_or_default();
                (
                    name.clone(),
                    RoleState {
                        original_type: local_type.clone(),
                        local_type,
                        state,
                    },
                )
            })
            .collect();

        self.choreographies.push(Choreography { roles, queues });
        id
    }

    /// Run all choreographies for a fixed number of steps.
    ///
    /// Each step processes one protocol tick across all roles in all
    /// choreographies. Returns the collected trace.
    ///
    /// # Errors
    ///
    /// Returns a [`SchedulerError`] if any role or handler encounters an error.
    pub fn run(
        &mut self,
        steps: usize,
        handler: &dyn EffectHandler,
    ) -> Result<Trace, SchedulerError> {
        let mut trace = Trace::new();

        for step in 0..steps {
            for choreo in &mut self.choreographies {
                Self::step_choreography(choreo, step, handler, &mut trace)?;
            }
        }

        Ok(trace)
    }

    /// Execute one protocol tick for a single choreography.
    fn step_choreography(
        choreo: &mut Choreography,
        step: usize,
        handler: &dyn EffectHandler,
        trace: &mut Trace,
    ) -> Result<(), SchedulerError> {
        let role_names: Vec<String> = choreo.roles.keys().cloned().collect();

        // Process sends, then receives, then integration steps.
        // This ensures messages are available before receives execute.

        // Phase 1: Execute sends.
        for name in &role_names {
            let role = choreo.roles.get(name).expect("role exists");
            if let LocalTypeR::Send {
                partner, branches, ..
            } = &role.local_type
            {
                if let Some((label, _vt, _cont)) = branches.first() {
                    let payload = handler
                        .handle_send(name, partner, &label.name, &role.state)
                        .map_err(SchedulerError::HandlerError)?;

                    let queue = choreo
                        .queues
                        .get_mut(&(name.clone(), partner.clone()))
                        .ok_or_else(|| SchedulerError::NoMatchingReceive {
                            sender: name.clone(),
                            receiver: partner.clone(),
                        })?;
                    queue.push_back(Message {
                        _label: label.name.clone(),
                        payload,
                    });
                }
            }
        }

        // Phase 2: Execute receives.
        // Collect receive info first to avoid borrow conflicts.
        let recv_info: Vec<_> = role_names
            .iter()
            .filter_map(|name| {
                let role = choreo.roles.get(name).expect("role exists");
                if let LocalTypeR::Recv {
                    partner, branches, ..
                } = &role.local_type
                {
                    branches
                        .first()
                        .map(|(label, _vt, _)| (name.clone(), partner.clone(), label.name.clone()))
                } else {
                    None
                }
            })
            .collect();

        for (name, partner, label) in &recv_info {
            let msg = choreo
                .queues
                .get_mut(&(partner.clone(), name.clone()))
                .and_then(|q| q.pop_front());

            if let Some(msg) = msg {
                let role = choreo.roles.get_mut(name).expect("role exists");
                handler
                    .handle_recv(name, partner, label, &mut role.state, &msg.payload)
                    .map_err(SchedulerError::HandlerError)?;
            }
        }

        // Phase 3: Integration step and trace recording.
        // Only call step() when the role performed a protocol action (send/recv).
        for name in &role_names {
            let role = choreo.roles.get_mut(name).expect("role exists");
            let is_active = matches!(
                &role.local_type,
                LocalTypeR::Send { .. } | LocalTypeR::Recv { .. }
            );

            if is_active {
                handler
                    .step(name, &mut role.state)
                    .map_err(SchedulerError::HandlerError)?;
            }

            trace.record(StepRecord {
                step,
                role: name.clone(),
                state: role.state.clone(),
            });
        }

        // Phase 4: Advance local types.
        for name in &role_names {
            let role = choreo.roles.get_mut(name).expect("role exists");
            role.local_type = advance_local_type(&role.local_type, &role.original_type);
        }

        Ok(())
    }
}

impl Default for Scheduler {
    fn default() -> Self {
        Self::new()
    }
}

/// Advance a local type by one step (consuming the outermost send/recv).
///
/// For recursive types (`mu`), unfolds to the body. When a `var` is reached,
/// unfolds back to the original type (which includes the mu wrapper).
fn advance_local_type(lt: &LocalTypeR, original: &LocalTypeR) -> LocalTypeR {
    match lt {
        LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
            let cont = branches
                .first()
                .map(|(_, _vt, cont)| cont.clone())
                .unwrap_or(LocalTypeR::End);
            // If continuation is a Var, unfold back to original (mu-wrapped) type.
            if let LocalTypeR::Var(_) = &cont {
                original.clone()
            } else {
                cont
            }
        }
        LocalTypeR::Mu { body, .. } => advance_local_type(body, original),
        LocalTypeR::Var(_) => original.clone(),
        LocalTypeR::End => LocalTypeR::End,
    }
}
