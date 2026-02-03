# VM Overview

This document introduces the bytecode VM that executes session type protocols.

## Introduction

The bytecode VM is the core execution engine used by the simulator. The VM compiles local types to bytecode instructions and manages scheduling, buffers, and session lifecycle. Effect handlers remain pluggable through the `EffectHandler` trait.

The VM is located in `rust/vm/`. The crate depends on `telltale-types` and `telltale-theory` for type definitions and projection algorithms.

## Design Principles

The VM follows three core principles that enable formal verification.

Session isolation ensures that coroutines in different sessions cannot interfere with each other. Each session has its own buffers, type state, and namespace. Cross-session operations are impossible by construction.

Deterministic execution means that given the same inputs, the VM produces the same observable trace. The simulation clock provides deterministic timing. Random number generation requires explicit seeding through effect handlers.

Effect separation keeps the VM core pure. All side effects flow through the `EffectHandler` trait. The handler contract requires deterministic, session-local behavior for N-invariance guarantees.

## Architecture

The VM struct contains coroutines, sessions, scheduler state, and the observable trace.

```rust
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
```

Each coroutine owns its bytecode program. The `sessions` store tracks active sessions with their buffers and type state. The `scheduler` manages the ready queue and blocked set. The trace records observable events for deterministic replay.

The `Coroutine` struct represents a lightweight execution unit.

```rust
pub struct Coroutine {
    pub id: usize,
    pub pc: usize,
    pub regs: Vec<Value>,
    pub status: CoroStatus,
    pub session_id: SessionId,
    pub role: String,
    pub program: Vec<Instr>,
}
```

Each coroutine has a program counter, register file, and status. The `role` field identifies which participant this coroutine embodies. The `session_id` links the coroutine to its session.

## Code Image Loading

The `CodeImage` struct packages bytecode programs with their source types.

```rust
pub struct CodeImage {
    pub global_type: GlobalType,
    pub local_types: BTreeMap<String, LocalTypeR>,
    pub programs: BTreeMap<String, Vec<Instr>>,
}

impl CodeImage {
    pub fn from_local_types(
        local_types: &BTreeMap<String, LocalTypeR>,
        global_type: &GlobalType,
    ) -> Self
}
```

The constructor takes projected local types and the source global type. It assumes the inputs are already validated. Use `UntrustedImage::validate` when loading untrusted inputs.

The `load_choreography` method instantiates a session from a code image.

```rust
impl VM {
    pub fn load_choreography(&mut self, image: &CodeImage) -> Result<SessionId, VMError>
}
```

This method loads precompiled bytecode from the image. It allocates buffers for all role pairs. It spawns one coroutine per role with the appropriate program. The method returns the new session ID.

Multiple calls to `load_choreography` create independent sessions. Each call compiles fresh programs and spawns new coroutines. This supports dynamic protocol loading at runtime.

## VMBackend Trait

The `VMBackend` trait abstracts over cooperative and threaded execution.

```rust
pub trait VMBackend {
    fn load_choreography(&mut self, image: &CodeImage) -> Result<SessionId, VMError>;
    fn step_round(&mut self, handler: &dyn EffectHandler, n: usize) -> Result<StepResult, VMError>;
    fn run(&mut self, handler: &dyn EffectHandler, max_rounds: usize) -> Result<(), VMError>;
    fn trace(&self) -> Vec<ObsEvent>;
}
```

The cooperative backend executes in a single thread using manual yielding. The threaded backend uses OS threads when the `multi-thread` feature is enabled. Both backends produce identical per-session traces due to scheduling confluence in the Lean model.

WASM targets use the cooperative backend exclusively. The `wasm` feature configures the VM for single-threaded execution with JavaScript-compatible random number generation.

## Example

This example loads and runs a simple protocol.

```rust
use std::collections::BTreeMap;
use telltale_theory::project_all;
use telltale_types::LocalTypeR;
use telltale_vm::{VM, VMConfig};
use telltale_vm::loader::CodeImage;

// Project global type to local types
let projected = project_all(&global)?;
let local_types: BTreeMap<String, LocalTypeR> = projected.into_iter().collect();

// Create code image and VM
let image = CodeImage::from_local_types(&local_types, &global);
let mut vm = VM::new(VMConfig::default());

// Load choreography and run
let sid = vm.load_choreography(&image)?;
vm.run(&handler, 1000)?;
```

The first section projects the global type for each role. The second section creates a code image and initializes the VM. The third section loads the choreography and runs until completion or fuel exhaustion.

See [Bytecode Instructions](10_bytecode_instructions.md) for the instruction set reference. See [VM Scheduling](11_vm_scheduling.md) for concurrency and N-invariance details.
