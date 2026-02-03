# VM Overview

This document introduces the bytecode VM that executes session type protocols.

## Introduction

The bytecode VM provides an alternative execution model to direct effect handler interpretation. The VM compiles local types to bytecode instructions and manages scheduling, buffers, and session lifecycle. Effect handlers remain pluggable through the `EffectHandler` trait.

The VM is located in `rust/vm/`. The crate depends on `telltale-types` and `telltale-theory` for type definitions and projection algorithms.

## Design Principles

The VM follows three core principles that enable formal verification.

Session isolation ensures that coroutines in different sessions cannot interfere with each other. Each session has its own buffers, type state, and namespace. Cross-session operations are impossible by construction.

Deterministic execution means that given the same inputs, the VM produces the same observable trace. The simulation clock provides deterministic timing. Random number generation requires explicit seeding through effect handlers.

Effect separation keeps the VM core pure. All side effects flow through the `EffectHandler` trait. The handler contract requires deterministic, session-local behavior for N-invariance guarantees.

## Architecture

The VM struct contains programs, coroutines, sessions, and scheduler state.

```rust
pub struct VM {
    config: VMConfig,
    programs: Vec<Program>,
    coroutines: Vec<Coroutine>,
    sessions: SessionStore,
    scheduler: SchedState,
    clock: SimClock,
}
```

The `programs` array holds bytecode programs. Each coroutine has a `programId` referencing its assigned program in this array. The `sessions` store tracks active sessions with their buffers and type state. The `scheduler` manages the ready queue and blocked set.

The `Coroutine` struct represents a lightweight execution unit.

```rust
pub struct Coroutine {
    pub id: usize,
    pub program_id: usize,
    pub pc: usize,
    pub regs: Vec<Value>,
    pub status: CoroStatus,
    pub role: String,
    pub session_id: SessionId,
}
```

Each coroutine has a program counter, register file, and status. The `role` field identifies which participant this coroutine embodies. The `session_id` links the coroutine to its session.

## Code Image Loading

The `CodeImage` struct packages local types for loading into the VM.

```rust
pub struct CodeImage {
    pub global_type: GlobalType,
    pub local_types: Vec<(Role, LocalTypeR)>,
}

impl CodeImage {
    pub fn from_local_types(
        local_types: &[(Role, LocalTypeR)],
        global_type: &GlobalType,
    ) -> Self
}
```

The constructor takes projected local types and the source global type. Well-formedness is validated at construction time.

The `load_choreography` method instantiates a session from a code image.

```rust
impl VM {
    pub fn load_choreography(&mut self, image: &CodeImage) -> Result<SessionId, VMError>
}
```

This method compiles each local type to bytecode and creates a program. It allocates buffers for all role pairs. It spawns one coroutine per role with the appropriate program ID. The method returns the new session ID.

Multiple calls to `load_choreography` create independent sessions. Each call compiles fresh programs and spawns new coroutines. This supports dynamic protocol loading at runtime.

## VMBackend Trait

The `VMBackend` trait abstracts over cooperative and threaded execution.

```rust
pub trait VMBackend {
    fn run(&mut self, vm: &mut VM, handler: &dyn EffectHandler, fuel: usize) -> RunResult;
}
```

The cooperative backend executes in a single thread using manual yielding. The threaded backend uses OS threads when the `multi-thread` feature is enabled. Both backends produce identical per-session traces due to N-invariance.

WASM targets use the cooperative backend exclusively. The `wasm` feature configures the VM for single-threaded execution with JavaScript-compatible random number generation.

## Example

This example loads and runs a simple protocol.

```rust
use telltale_vm::{VM, VMConfig, CodeImage};
use telltale_theory::project;

// Project global type to local types
let local_alice = project(&global, "Alice")?;
let local_bob = project(&global, "Bob")?;
let local_types = vec![
    ("Alice".into(), local_alice),
    ("Bob".into(), local_bob),
];

// Create code image and VM
let image = CodeImage::from_local_types(&local_types, &global);
let mut vm = VM::new(VMConfig::default());

// Load choreography and run
let sid = vm.load_choreography(&image)?;
vm.run(&handler, 1000)?;
```

The first section projects the global type for each role. The second section creates a code image and initializes the VM. The third section loads the choreography and runs until completion or fuel exhaustion.

See [Bytecode Instructions](10_bytecode_instructions.md) for the instruction set reference. See [VM Scheduling](11_vm_scheduling.md) for concurrency and N-invariance details.
