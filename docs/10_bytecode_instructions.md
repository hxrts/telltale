# Bytecode Instructions

This document provides a complete reference for the VM instruction set.

## Instruction Categories

The bytecode instruction set is organized into four categories.

Communication instructions handle message passing between session participants. These include `Send`, `Recv`, `Offer`, and `Choose`. Session instructions manage session lifecycle through `Open` and `Close`. Effect instructions invoke domain-specific behavior via `Invoke`. Control instructions handle program flow with `LoadImm`, `Mov`, `Jmp`, `Yield`, and `Halt`.

## Communication Instructions

Communication instructions implement the session type primitives.

### Send

The `Send` instruction transmits a value to a partner role.

```rust
Send { chan: Reg, val: Reg }
```

The `chan` register identifies the endpoint register. The `val` register is reserved for payloads, but the current VM computes payloads via the `EffectHandler` instead of reading from registers. The instruction enqueues the handler-provided value into the appropriate buffer for the destination role.

### Recv

The `Recv` instruction receives a value from a partner role.

```rust
Recv { chan: Reg, dst: Reg }
```

The `chan` register identifies the endpoint register. The `dst` register receives the incoming value. If no message is available, the coroutine blocks with status `RecvWait`.

### Offer

The `Offer` instruction waits for a label and dispatches based on a jump table.

```rust
Offer { chan: Reg, table: Vec<(String, PC)> }
```

For external choice, the instruction dequeues a label from the partner and jumps to the matching entry. For internal choice, the handler selects a label and the VM enqueues it before jumping. The `chan` register receives the label value.

### Choose

The `Choose` instruction selects a fixed label and jumps.

```rust
Choose { chan: Reg, label: String, target: PC }
```

The instruction enqueues the provided label and jumps to the target PC. It is useful when the label is statically known.

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

### LoadImm

The `LoadImm` instruction loads an immediate value.

```rust
LoadImm { dst: Reg, val: ImmValue }
```

The value is written directly to the destination register.

### Mov

The `Mov` instruction copies between registers.

```rust
Mov { dst: Reg, src: Reg }
```

The value in the source register is copied to the destination register.

### Jmp

The `Jmp` instruction performs an unconditional jump.

```rust
Jmp { target: PC }
```

The program counter is set to the target address. This implements loops via recursion variable unfolding.

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
| `Send(partner, branches)` | `Offer` with jump table, then branch blocks |
| `Recv(partner, [(label, sort, cont)])` | `Recv`, `Invoke`, recurse on cont |
| `Recv(partner, branches)` | `Offer` with jump table, then branch blocks |
| `Mu(var, body)` | Record loop target PC, recurse on body |
| `Var(name)` | `Jmp` to loop target |
| `End` | `Halt` |

The translation is straightforward. Single-branch send and receive compile to the primitive instructions. Multi-branch types compile to selection and branching. Recursive types use jump instructions for looping.

The `compileLocalTypeR` function in `rust/vm/src/compiler.rs` implements this translation. Every compiled program ends with either `Halt` or `Jmp`.
