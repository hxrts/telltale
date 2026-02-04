//! Bytecode VM for choreographic session type protocols.
//!
//! This crate provides a standalone, embeddable virtual machine that executes
//! choreographic protocols projected to local session types. The VM validates
//! every instruction against its session type monitor, ensuring protocol
//! conformance at runtime.
//!
//! # Architecture
//!
//! The VM follows the Lean specification in `lean/Runtime/VM/`:
//! - **Instructions** ([`instr::Instr`]): bytecode ops for send/recv/choice/session lifecycle
//! - **Coroutines** ([`coroutine::Coroutine`]): lightweight execution units, one per role
//! - **Sessions** ([`session::SessionStore`]): manage session lifecycle and namespaces
//! - **Buffers** ([`buffer::BoundedBuffer`]): bounded message channels with backpressure
//! - **Scheduler** ([`scheduler::Scheduler`]): policy-based coroutine scheduling
//! - **Loader** ([`loader`]): dynamic choreography loading with validation
//! - **Compiler** ([`compiler`]): compile `LocalTypeR` to bytecode
//!
//! The VM is the **single execution engine** for simulation and runtime
//! orchestration. Higher-level systems (e.g. `telltale-simulator`) wrap the
//! VM with deterministic middleware for network latency, faults, property
//! monitoring, and checkpointing.
//!
//! **Nested simulation** is supported via [`nested::NestedVMHandler`], which
//! allows a VM coroutine to host an inner VM for distributed or hierarchical
//! simulations.
//!
//! # Effect Handler Contract
//!
//! The VM's [`effect::EffectHandler`] is synchronous, deterministic, and
//! **session-local**. It must not depend on global time or shared mutable
//! state across sessions. This is distinct from the async, typed
//! `telltale_choreography::ChoreoHandler` used by generated choreography code.
//!
//! # Usage
//!
//! ```ignore
//! use telltale_vm::{VM, VMConfig, compiler, loader::CodeImage};
//!
//! let config = VMConfig::default();
//! let mut vm = VM::new(config);
//! let image = CodeImage::from_local_types(&local_types, &global_type);
//! let sid = vm.load_choreography(image, &handler)?;
//! while vm.step(&handler)? {}
//! ```

pub mod backend;
pub mod buffer;
pub mod clock;
pub mod compiler;
pub mod coroutine;
pub mod effect;
pub mod instr;
pub mod loader;
pub mod nested;
pub mod scheduler;
pub mod session;
pub mod trace;
#[cfg(feature = "multi-thread")]
pub mod threaded;
pub mod vm;
#[cfg(target_arch = "wasm32")]
pub mod wasm;

pub use backend::VMBackend;
pub use clock::SimClock;
pub use coroutine::{CoroStatus, Coroutine, Value};
pub use instr::Instr;
pub use nested::NestedVMHandler;
pub use scheduler::{SchedPolicy, Scheduler};
pub use session::{SessionId, SessionStore};
pub use trace::{normalize_trace, obs_session, strict_trace, with_tick};
#[cfg(target_arch = "wasm32")]
pub use wasm::WasmVM;
#[cfg(feature = "multi-thread")]
pub use threaded::ThreadedVM;
pub use vm::{VMConfig, VM};
