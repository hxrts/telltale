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

/// Effect action descriptor carried by `Invoke`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum InvokeAction {
    /// Named action descriptor (Lean-aligned shape).
    Named(String),
    /// Legacy register-carried action descriptor.
    Reg(Reg),
}

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
    Receive {
        /// Channel register.
        chan: Reg,
        /// Destination register for the received value.
        dst: Reg,
    },
    /// Offer a label on channel.
    Offer {
        /// Channel register.
        chan: Reg,
        /// Label to select.
        label: String,
    },
    /// Choose from a branch table using a received label.
    Choose {
        /// Channel register.
        chan: Reg,
        /// Label-to-PC jump table.
        table: Vec<(String, PC)>,
    },

    // -- Session lifecycle --
    /// Open a new session with the given roles and endpoint destinations.
    Open {
        /// Role names for the session.
        roles: Vec<String>,
        /// Role-to-local-type mappings for session initialization.
        local_types: Vec<(String, telltale_types::LocalTypeR)>,
        /// Edge-to-handler mappings as `((sender, receiver), handler_id)`.
        handlers: Vec<((String, String), String)>,
        /// Role-to-register endpoint mappings.
        dsts: Vec<(String, Reg)>,
    },
    /// Close the session referenced by the register.
    Close {
        /// Register holding the session reference.
        session: Reg,
    },

    // -- Effects --
    /// Invoke an effect handler action.
    Invoke {
        /// Action descriptor.
        action: InvokeAction,
        /// Legacy compatibility field for register-result encoding.
        #[serde(default)]
        dst: Option<Reg>,
    },
    /// Acquire a guard layer and store evidence in a register.
    Acquire {
        /// Guard layer identifier.
        layer: String,
        /// Destination register for evidence.
        dst: Reg,
    },
    /// Release a guard layer using evidence from a register.
    Release {
        /// Guard layer identifier.
        layer: String,
        /// Register holding evidence.
        evidence: Reg,
    },

    // -- Speculation --
    /// Enter speculation using a ghost session id.
    Fork {
        /// Register holding the ghost session id.
        ghost: Reg,
    },
    /// Join speculative execution.
    Join,
    /// Abort speculative execution.
    Abort,

    // -- Ownership and knowledge --
    /// Transfer an endpoint to another coroutine.
    Transfer {
        /// Register holding the endpoint.
        endpoint: Reg,
        /// Register holding the target coroutine id.
        target: Reg,
        /// Register holding a bundle descriptor.
        bundle: Reg,
    },
    /// Tag a knowledge fact and return success.
    Tag {
        /// Register holding the fact.
        fact: Reg,
        /// Destination register for the result.
        dst: Reg,
    },
    /// Check a knowledge fact against the flow policy.
    Check {
        /// Register holding the knowledge fact.
        knowledge: Reg,
        /// Register holding the target role.
        target: Reg,
        /// Destination register for the result.
        dst: Reg,
    },

    // -- Control --
    /// Set a register to an immediate value.
    Set {
        /// Destination register.
        dst: Reg,
        /// Immediate value to load.
        val: ImmValue,
    },
    /// Copy register src to dst.
    Move {
        /// Destination register.
        dst: Reg,
        /// Source register.
        src: Reg,
    },
    /// Unconditional jump.
    Jump {
        /// Target program counter.
        target: PC,
    },
    /// Spawn a new coroutine at target PC with argument registers.
    Spawn {
        /// Target program counter for the spawned coroutine.
        target: PC,
        /// Registers to copy into the spawned coroutine argument area.
        args: Vec<Reg>,
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
    /// Natural-number value (Lean-compatible).
    Nat(u64),
    /// Boolean value.
    Bool(bool),
    /// String value.
    Str(String),
}

impl Eq for ImmValue {}
