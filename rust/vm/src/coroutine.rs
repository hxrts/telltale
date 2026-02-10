//! Coroutine: lightweight execution unit within the VM.
//!
//! Each role in a choreography runs as a coroutine with its own PC,
//! register file, and status. Matches the Lean `Coroutine` structure.

use serde::{Deserialize, Serialize};
use telltale_types::{FixedQ32, ValType};

use crate::instr::{Endpoint, PC};
use crate::session::{Edge, HandlerId, SessionId};

fn default_cost_budget() -> usize {
    usize::MAX
}

/// Register-file representation aligned with the Lean VM model.
pub type RegFile = Vec<Value>;

/// Progress-token representation aligned with the Lean VM model.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProgressToken {
    /// Session this token is scoped to.
    pub sid: SessionId,
    /// Endpoint this token authorizes progress for.
    pub endpoint: Endpoint,
}

impl ProgressToken {
    /// Construct a token from an endpoint.
    #[must_use]
    pub fn for_endpoint(endpoint: Endpoint) -> Self {
        Self {
            sid: endpoint.sid,
            endpoint,
        }
    }
}

/// Effect-context placeholder aligned with the Lean VM model.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct EffectCtx<E = ()> {
    /// Optional effect metadata captured for replay/introspection.
    pub last_effect: Option<E>,
}

impl<E> Default for EffectCtx<E> {
    fn default() -> Self {
        Self { last_effect: None }
    }
}

/// Runtime value stored in registers and buffers.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Value {
    /// Unit / no value.
    Unit,
    /// Natural number (Lean-compatible).
    Nat(u64),
    /// Boolean.
    Bool(bool),
    /// String.
    Str(String),
    /// Product pair value (Lean-compatible).
    Prod(Box<Value>, Box<Value>),
    /// Endpoint reference for ownership and guard operations.
    Endpoint(Endpoint),
    /// Fixed-point Q32.32 number for deterministic simulation.
    Q32(FixedQ32),
    /// Vector of fixed-point Q32.32 numbers for deterministic simulation.
    Q32Vec(Vec<FixedQ32>),
}

/// Coroutine execution status.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum CoroStatus {
    /// Ready to execute.
    Ready,
    /// Blocked waiting on something.
    Blocked(BlockReason),
    /// Completed normally.
    Done,
    /// Faulted with an error.
    Faulted(Fault),
    /// Running under speculative execution mode.
    Speculating,
}

/// Why a coroutine is blocked.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[allow(clippy::enum_variant_names)]
pub enum BlockReason {
    /// Waiting to receive on an edge.
    RecvWait {
        /// Edge scope for the receive wait.
        edge: Edge,
        /// Progress token associated with the blocked receive.
        token: ProgressToken,
    },
    /// Waiting for buffer space to send.
    SendWait {
        /// Edge awaiting buffer space.
        edge: Edge,
    },
    /// Waiting for an effect handler response.
    InvokeWait {
        /// Effect handler identifier.
        handler: HandlerId,
    },
    /// Waiting for a guard layer to allow acquisition.
    AcquireDenied {
        /// Guard layer identifier.
        layer: String,
    },
    /// Waiting for consensus-related condition to resolve.
    ConsensusWait {
        /// Consensus wait tag.
        tag: usize,
    },
    /// Waiting for spawn scheduling/activation.
    SpawnWait,
    /// Waiting for a session close to complete.
    CloseWait {
        /// The session being closed.
        sid: SessionId,
    },
}

/// Runtime fault.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[allow(clippy::enum_variant_names)]
pub enum Fault {
    /// Instruction violated the session type.
    TypeViolation {
        /// Expected runtime value type.
        expected: ValType,
        /// Actual runtime value type.
        actual: ValType,
        /// Description of the type violation.
        message: String,
    },
    /// Unknown label in offer/choose.
    UnknownLabel {
        /// The unrecognized label.
        label: String,
    },
    /// Channel/endpoint closed.
    ChannelClosed {
        /// The closed endpoint.
        endpoint: Endpoint,
    },
    /// Signature evidence failed edge validation.
    InvalidSignature {
        /// Edge whose signature check failed.
        edge: Edge,
    },
    /// Effect handler error.
    InvokeFault {
        /// Error message from the handler.
        message: String,
    },
    /// Guard layer failure.
    AcquireFault {
        /// Guard layer identifier.
        layer: String,
        /// Error message.
        message: String,
    },
    /// Ownership transfer failure.
    TransferFault {
        /// Error message.
        message: String,
    },
    /// Speculation failure.
    SpecFault {
        /// Error message.
        message: String,
    },
    /// Session close error.
    CloseFault {
        /// Error message from close.
        message: String,
    },
    /// Protocol-level flow invariant violation.
    FlowViolation {
        /// Violation detail.
        message: String,
    },
    /// Missing progress token for a required edge action.
    NoProgressToken {
        /// Edge missing a valid progress token.
        edge: Edge,
    },
    /// Output-condition commit gate rejected emitted outputs.
    OutputConditionFault {
        /// Predicate reference that failed verification.
        predicate_ref: String,
    },
    /// Register out of bounds.
    OutOfRegisters,
    /// PC out of bounds.
    PcOutOfBounds,
    /// Buffer full and backpressure policy is error.
    BufferFull {
        /// The full endpoint buffer.
        endpoint: Endpoint,
    },
    /// Coroutine exhausted its deterministic execution budget.
    OutOfCredits,
}

impl std::fmt::Display for Fault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TypeViolation {
                expected,
                actual,
                message,
            } => write!(
                f,
                "type violation (expected {expected:?}, actual {actual:?}): {message}"
            ),
            Self::UnknownLabel { label } => write!(f, "unknown label: {label}"),
            Self::ChannelClosed { endpoint } => {
                write!(f, "channel closed: {}:{}", endpoint.sid, endpoint.role)
            }
            Self::InvalidSignature { edge } => write!(
                f,
                "invalid signature on edge {}:{}→{}",
                edge.sid, edge.sender, edge.receiver
            ),
            Self::InvokeFault { message } => write!(f, "invoke fault: {message}"),
            Self::AcquireFault { layer, message } => {
                write!(f, "acquire fault ({layer}): {message}")
            }
            Self::TransferFault { message } => write!(f, "transfer fault: {message}"),
            Self::SpecFault { message } => write!(f, "speculation fault: {message}"),
            Self::CloseFault { message } => write!(f, "close fault: {message}"),
            Self::FlowViolation { message } => write!(f, "flow violation: {message}"),
            Self::NoProgressToken { edge } => write!(
                f,
                "missing progress token for edge {}:{}→{}",
                edge.sid, edge.sender, edge.receiver
            ),
            Self::OutputConditionFault { predicate_ref } => {
                write!(f, "output-condition rejected: {predicate_ref}")
            }
            Self::OutOfRegisters => write!(f, "out of registers"),
            Self::PcOutOfBounds => write!(f, "PC out of bounds"),
            Self::BufferFull { endpoint } => {
                write!(f, "buffer full: {}:{}", endpoint.sid, endpoint.role)
            }
            Self::OutOfCredits => write!(f, "out of credits"),
        }
    }
}

/// A single coroutine executing a role's local protocol.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Coroutine<E = ()> {
    /// Unique coroutine identifier.
    pub id: usize,
    /// Program table index for instruction fetch.
    pub program_id: usize,
    /// Program counter.
    pub pc: PC,
    /// Register file.
    pub regs: RegFile,
    /// Execution status.
    pub status: CoroStatus,
    /// Effect execution context.
    #[serde(default)]
    pub effect_ctx: EffectCtx<E>,
    /// Endpoints owned by this coroutine.
    pub owned_endpoints: Vec<Endpoint>,
    /// Progress tokens for scheduling.
    pub progress_tokens: Vec<ProgressToken>,
    /// Knowledge facts owned by this coroutine.
    pub knowledge_set: KnowledgeSet,
    /// Speculation state, if any.
    pub spec_state: Option<SpeculationState>,
    /// Session this coroutine participates in.
    pub session_id: SessionId,
    /// Role name within the session.
    pub role: String,
    /// Remaining instruction budget for deterministic cost accounting.
    #[serde(default = "default_cost_budget")]
    pub cost_budget: usize,
}

/// Lean-aligned coroutine state alias.
pub type CoroutineState<E = ()> = Coroutine<E>;

/// Knowledge fact for ownership checks.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct KnowledgeFact {
    /// Endpoint that the fact is about.
    pub endpoint: Endpoint,
    /// String fact payload.
    pub fact: String,
}

/// Lean-aligned knowledge set type.
pub type KnowledgeSet = Vec<KnowledgeFact>;

/// Speculation state for a coroutine.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct SpeculationState {
    /// Ghost session identifier.
    pub ghost_sid: usize,
    /// Speculation depth.
    pub depth: usize,
}

impl Coroutine {
    /// Create a new coroutine.
    #[must_use]
    pub fn new(
        id: usize,
        program_id: usize,
        session_id: SessionId,
        role: String,
        num_regs: u16,
        cost_budget: usize,
    ) -> Self {
        Self {
            id,
            program_id,
            pc: 0,
            regs: vec![Value::Unit; usize::from(num_regs)],
            status: CoroStatus::Ready,
            effect_ctx: EffectCtx::default(),
            owned_endpoints: Vec::new(),
            progress_tokens: Vec::new(),
            knowledge_set: Vec::new(),
            spec_state: None,
            session_id,
            role,
            cost_budget,
        }
    }

    /// Whether this coroutine is ready to execute.
    #[must_use]
    pub fn is_ready(&self) -> bool {
        self.status == CoroStatus::Ready
    }

    /// Whether this coroutine has finished (done or faulted).
    #[must_use]
    pub fn is_terminal(&self) -> bool {
        matches!(self.status, CoroStatus::Done | CoroStatus::Faulted(_))
    }
}

impl Fault {
    /// Build a type-violation fault when only a textual diagnostic is available.
    #[must_use]
    pub fn type_violation(message: impl Into<String>) -> Self {
        Self::TypeViolation {
            expected: ValType::Unit,
            actual: ValType::Unit,
            message: message.into(),
        }
    }
}
