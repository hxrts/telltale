# Bytecode Instructions

This document provides a complete reference for the VM instruction set.

## Instruction Categories

The bytecode instruction set is organized into four categories.

Communication instructions handle message passing between session participants. These include `Send`, `Receive`, `Offer`, and `Choose`. Session instructions manage session lifecycle through `Open` and `Close`. Effect instructions invoke domain-specific behavior via `Invoke`. Control instructions handle program flow with `Set`, `Move`, `Jump`, `Spawn`, `Yield`, and `Halt`.

## Communication Instructions

Communication instructions implement the session type primitives.

### Send

The `Send` instruction transmits a value to a partner role.

```rust
Send { chan: Reg, val: Reg }
```

The `chan` register identifies the endpoint register. The `val` register is reserved for payloads, but the current VM computes payloads via the `EffectHandler` instead of reading from registers. The instruction enqueues the handler-provided value into the appropriate buffer for the destination role.

### Receive

The `Receive` instruction receives a value from a partner role.

```rust
Receive { chan: Reg, dst: Reg }
```

The `chan` register identifies the endpoint register. The `dst` register receives the incoming value. If no message is available, the coroutine blocks with status `RecvWait`.

### Offer

The `Offer` instruction sends a selected label.

```rust
Offer { chan: Reg, label: String }
```

The VM checks the current local type is `Send`, verifies the label exists in the send branches, enqueues it, advances the local type continuation, and advances PC.

### Choose

The `Choose` instruction receives a label and dispatches via a branch table.

```rust
Choose { chan: Reg, table: Vec<(String, PC)> }
```

The VM checks the current local type is `Recv`, dequeues a label from the partner, validates that label against both session branches and the instruction table, then jumps to the selected PC.

## Session Instructions

Session instructions manage the session lifecycle.

### Open

The `Open` instruction creates a new session.

```rust
Open {
    roles: Vec<String>,
    endpoints: Vec<(String, Reg)>,
}
```

The instruction allocates a new session with the given roles. Endpoints are written to the destination registers. The current VM uses default buffer settings and does not bind handlers per edge.

### Close

The `Close` instruction terminates a session.

```rust
Close { session: Reg }
```

The instruction closes the session and removes its type state. Further access to the session causes a fault.

## Effect Instructions

Effect instructions invoke domain-specific behavior.

### Invoke

The `Invoke` instruction calls an effect handler.

```rust
Invoke { action: Reg, dst: Reg }
```

The instruction calls `EffectHandler::step` and records an observable event. The handler must satisfy the determinism contract for scheduling confluence. The registers are reserved for future effect payloads.

## Control Instructions

Control instructions manage program flow and register state.

### Set

The `Set` instruction loads an immediate value.

```rust
Set { dst: Reg, val: ImmValue }
```

The value is written directly to the destination register.

### Move

The `Move` instruction copies between registers.

```rust
Move { dst: Reg, src: Reg }
```

The value in the source register is copied to the destination register.

### Jump

The `Jump` instruction performs an unconditional jump.

```rust
Jump { target: PC }
```

The program counter is set to the target address. This implements loops via recursion variable unfolding.

### Spawn

The `Spawn` instruction reserves a coroutine-spawn opcode in the ISA.

```rust
Spawn { target: PC, args: Vec<Reg> }
```

Current status: this variant is modeled in the instruction set but not yet implemented in the cooperative or threaded runtime.

### Yield

The `Yield` instruction returns control to the scheduler.

```rust
Yield
```

The coroutine is placed back on the ready queue. The scheduler selects the next coroutine to run.

### Halt

The `Halt` instruction terminates the coroutine.

```rust
Halt
```

The coroutine status becomes `Done`. The coroutine is removed from the ready queue.

## Compilation from LocalTypeR

The compiler translates `LocalTypeR` directly to bytecode instructions.

| LocalTypeR | Instructions |
|------------|--------------|
| `Send(partner, [(label, sort, cont)])` | `Send`, `Invoke`, recurse on cont |
| `Send(partner, branches)` | deterministic `Offer` using first label, recurse on selected continuation |
| `Recv(partner, [(label, sort, cont)])` | `Receive`, `Invoke`, recurse on cont |
| `Recv(partner, branches)` | `Choose` with jump table, then branch blocks |
| `Mu(var, body)` | Record loop target PC, recurse on body |
| `Var(name)` | `Jump` to loop target |
| `End` | `Halt` |

The translation is straightforward. Single-branch send and receive compile to the primitive instructions. Multi-branch types compile to selection and branching. Recursive types use jump instructions for looping.

The `compileLocalTypeR` function in `rust/vm/src/compiler.rs` implements this translation. Every compiled program ends with either `Halt` or `Jump`.
