//! Coroutine: lightweight execution unit within the VM.
//!
//! Each role in a choreography runs as a coroutine with its own PC,
//! register file, and status. Matches the Lean `Coroutine` structure.

use serde::{Deserialize, Serialize};

use crate::instr::{Endpoint, PC};
use crate::session::SessionId;

/// Runtime value stored in registers and buffers.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Value {
    /// Unit / no value.
    Unit,
    /// Integer.
    Int(i64),
    /// Floating-point.
    Real(f64),
    /// Boolean.
    Bool(bool),
    /// String.
    Str(String),
    /// Vector of floats (for physical state vectors).
    Vec(Vec<f64>),
    /// Label name (for choice/offer).
    Label(String),
    /// JSON value (for interop with effect handlers).
    Json(serde_json::Value),
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
}

/// Why a coroutine is blocked.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[allow(clippy::enum_variant_names)]
pub enum BlockReason {
    /// Waiting to receive on an edge.
    RecvWait {
        /// The endpoint awaiting a message.
        endpoint: Endpoint,
    },
    /// Waiting for buffer space to send.
    SendWait {
        /// The endpoint awaiting buffer space.
        endpoint: Endpoint,
    },
    /// Waiting for an effect handler response.
    InvokeWait,
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
    /// Effect handler error.
    InvokeFault {
        /// Error message from the handler.
        message: String,
    },
    /// Session close error.
    CloseFault {
        /// Error message from close.
        message: String,
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
}

impl std::fmt::Display for Fault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TypeViolation { message } => write!(f, "type violation: {message}"),
            Self::UnknownLabel { label } => write!(f, "unknown label: {label}"),
            Self::ChannelClosed { endpoint } => {
                write!(f, "channel closed: {}:{}", endpoint.sid, endpoint.role)
            }
            Self::InvokeFault { message } => write!(f, "invoke fault: {message}"),
            Self::CloseFault { message } => write!(f, "close fault: {message}"),
            Self::OutOfRegisters => write!(f, "out of registers"),
            Self::PcOutOfBounds => write!(f, "PC out of bounds"),
            Self::BufferFull { endpoint } => {
                write!(f, "buffer full: {}:{}", endpoint.sid, endpoint.role)
            }
        }
    }
}

/// A single coroutine executing a role's local protocol.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Coroutine {
    /// Unique coroutine identifier.
    pub id: usize,
    /// Program counter.
    pub pc: PC,
    /// Register file.
    pub regs: Vec<Value>,
    /// Execution status.
    pub status: CoroStatus,
    /// Endpoints owned by this coroutine.
    pub owned_endpoints: Vec<Endpoint>,
    /// Session this coroutine participates in.
    pub session_id: SessionId,
    /// Role name within the session.
    pub role: String,
    /// Bytecode program.
    pub program: Vec<crate::instr::Instr>,
}

impl Coroutine {
    /// Create a new coroutine.
    #[must_use]
    pub fn new(
        id: usize,
        program: Vec<crate::instr::Instr>,
        session_id: SessionId,
        role: String,
        num_regs: u16,
    ) -> Self {
        Self {
            id,
            pc: 0,
            regs: vec![Value::Unit; usize::from(num_regs)],
            status: CoroStatus::Ready,
            owned_endpoints: Vec::new(),
            session_id,
            role,
            program,
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
