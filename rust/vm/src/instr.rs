//! Bytecode instruction set.
//!
//! Matches the Lean `Instr γ ε` type from `lean/Runtime/VM/Core.lean`.
//! Registers are `u16` indices, PC is `usize`.

use serde::{Deserialize, Serialize};

use crate::session::SessionId;

/// Register index.
pub type Reg = u16;

/// Program counter.
pub type PC = usize;

/// Structured endpoint: identifies a role within a session.
///
/// Matches the Lean `Endpoint` which carries `{ sid, role }`.
/// The session store uses this as the key for local type state.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct Endpoint {
    /// Session this endpoint belongs to.
    pub sid: SessionId,
    /// Role name within the session.
    pub role: String,
}

/// Bytecode instruction.
///
/// The initial instruction set covers communication, session lifecycle,
/// effects, and control flow. Guard/speculation/ownership instructions
/// are deferred.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Instr {
    // -- Communication --
    /// Send value in `val` register to channel in `chan` register.
    Send {
        /// Channel register.
        chan: Reg,
        /// Value register to send.
        val: Reg,
    },
    /// Receive from channel in `chan` register, store in `dst` register.
    Recv {
        /// Channel register.
        chan: Reg,
        /// Destination register for the received value.
        dst: Reg,
    },
    /// Offer a label on channel (external choice — wait for peer to choose).
    Offer {
        /// Channel register.
        chan: Reg,
        /// Label-to-PC jump table.
        table: Vec<(String, PC)>,
    },
    /// Choose a label on channel (internal choice — select a branch).
    Choose {
        /// Channel register.
        chan: Reg,
        /// Label to select.
        label: String,
        /// Jump target after selection.
        target: PC,
    },

    // -- Session lifecycle --
    /// Open a new session with the given roles and endpoint destinations.
    Open {
        /// Role names for the session.
        roles: Vec<String>,
        /// Role-to-register endpoint mappings.
        endpoints: Vec<(String, Reg)>,
    },
    /// Close the session referenced by the register.
    Close {
        /// Register holding the session reference.
        session: Reg,
    },

    // -- Effects --
    /// Invoke an effect handler action.
    Invoke {
        /// Register holding the action descriptor.
        action: Reg,
        /// Destination register for the result.
        dst: Reg,
    },

    // -- Control --
    /// Load an immediate value into a register.
    LoadImm {
        /// Destination register.
        dst: Reg,
        /// Immediate value to load.
        val: ImmValue,
    },
    /// Copy register src to dst.
    Mov {
        /// Destination register.
        dst: Reg,
        /// Source register.
        src: Reg,
    },
    /// Unconditional jump.
    Jmp {
        /// Target program counter.
        target: PC,
    },
    /// Yield execution to the scheduler.
    Yield,
    /// Halt this coroutine (normal termination).
    Halt,
}

/// Immediate values that can be loaded into registers.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum ImmValue {
    /// Unit value.
    Unit,
    /// Integer value.
    Int(i64),
    /// Real number value.
    Real(f64),
    /// Boolean value.
    Bool(bool),
    /// String value.
    Str(String),
}

impl Eq for ImmValue {}
