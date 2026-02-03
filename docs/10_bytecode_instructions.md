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

The `chan` register holds the channel endpoint. The `val` register holds the value to send. The instruction enqueues the value into the appropriate buffer for the destination role.

### Recv

The `Recv` instruction receives a value from a partner role.

```rust
Recv { chan: Reg, dst: Reg }
```

The `chan` register holds the channel endpoint. The `dst` register receives the incoming value. If no message is available, the coroutine blocks with status `RecvWait`.

### Offer

The `Offer` instruction sends a label for branch selection.

```rust
Offer { chan: Reg, label: Label }
```

The sender uses `Offer` to communicate their choice to the receiver. The label determines which branch the session will follow.

### Choose

The `Choose` instruction branches based on an offered label.

```rust
Choose { chan: Reg, table: Vec<(Label, PC)> }
```

The receiver uses `Choose` to read the offered label and jump to the corresponding program counter. The table maps labels to branch entry points.

## Session Instructions

Session instructions manage the session lifecycle.

### Open

The `Open` instruction creates a new session.

```rust
Open {
    roles: Vec<Role>,
    local_types: Vec<(Role, LocalTypeR)>,
    handlers: Vec<(Edge, HandlerId)>,
    dsts: Vec<(Role, Reg)>,
}
```

The instruction allocates buffers for all role pairs. It binds effect handlers to edges at this point. Channel endpoints are written to the destination registers. If handler binding fails, the instruction faults.

### Close

The `Close` instruction terminates a session.

```rust
Close { session: Reg }
```

The instruction drains any remaining buffered messages. It releases all resources held by the session. Further access to the session causes a fault.

## Effect Instructions

Effect instructions invoke domain-specific behavior.

### Invoke

The `Invoke` instruction calls an effect handler.

```rust
Invoke { action: EffectAction }
```

The instruction sends a request to the bound effect handler. Execution blocks until the handler responds. The handler must satisfy the determinism contract for N-invariance guarantees. See [Effect Handlers](07_effect_handlers.md) for handler implementation details.

## Control Instructions

Control instructions manage program flow and register state.

### LoadImm

The `LoadImm` instruction loads an immediate value.

```rust
LoadImm { dst: Reg, value: Value }
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
| `Send(partner, branches)` | `Choose`, then branch blocks with `Jmp` |
| `Recv(partner, [(label, sort, cont)])` | `Recv`, `Invoke`, recurse on cont |
| `Recv(partner, branches)` | `Offer`, then branch blocks |
| `Mu(var, body)` | Record loop target PC, recurse on body |
| `Var(name)` | `Jmp` to loop target |
| `End` | `Halt` |

The translation is straightforward. Single-branch send and receive compile to the primitive instructions. Multi-branch types compile to selection and branching. Recursive types use jump instructions for looping.

The `compileLocalTypeR` function in `rust/vm/src/compiler.rs` implements this translation. Every compiled program ends with either `Halt` or `Jmp`.
