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

pub mod buffer;
pub mod compiler;
pub mod coroutine;
pub mod effect;
pub mod instr;
pub mod loader;
pub mod scheduler;
pub mod session;
pub mod vm;

pub use coroutine::{CoroStatus, Coroutine, Value};
pub use instr::Instr;
pub use scheduler::{SchedPolicy, Scheduler};
pub use session::{SessionId, SessionStore};
pub use vm::{VMConfig, VM};
