# Bytecode Instructions

This document defines the current VM instruction set in `rust/vm/src/instr.rs`.

## Instruction Families

The VM groups instructions by execution concern.

| Family | Instructions |
|---|---|
| Communication | `Send`, `Receive`, `Offer`, `Choose` |
| Session lifecycle | `Open`, `Close` |
| Effect and guard | `Invoke`, `Acquire`, `Release` |
| Speculation | `Fork`, `Join`, `Abort` |
| Ownership and knowledge | `Transfer`, `Tag`, `Check` |
| Control | `Set`, `Move`, `Jump`, `Spawn`, `Yield`, `Halt` |

## Instruction Reference

### Communication

| Instruction | Fields | Runtime effect |
|---|---|---|
| `Send` | `chan`, `val` | Emits a send on the endpoint in `chan`. Payload routing is decided through the effect handler path. |
| `Receive` | `chan`, `dst` | Reads one message from the partner edge and writes the payload to `dst`. |
| `Offer` | `chan`, `label` | Performs internal choice and emits the selected label. |
| `Choose` | `chan`, `table` | Reads a label and branches by jump table entry. |

### Session lifecycle

| Instruction | Fields | Runtime effect |
|---|---|---|
| `Open` | `roles`, `local_types`, `handlers`, `dsts` | Allocates a new session, initializes local type state per role, binds edge handlers, and writes endpoint handles to destination registers. |
| `Close` | `session` | Closes the referenced session and emits close and epoch events. |

### Effect and guard

| Instruction | Fields | Runtime effect |
|---|---|---|
| `Invoke` | `action`, `dst` | Executes an effect step through the bound handler for the session. `dst` is an optional compatibility field. |
| `Acquire` | `layer`, `dst` | Attempts guard acquisition and writes evidence to `dst` when granted. |
| `Release` | `layer`, `evidence` | Releases a guard layer using previously issued evidence. |

### Speculation

| Instruction | Fields | Runtime effect |
|---|---|---|
| `Fork` | `ghost` | Enters speculation scope tied to a ghost session identifier. |
| `Join` | none | Commits speculative state when reconciliation checks pass. |
| `Abort` | none | Restores scoped checkpoint state and exits speculation. |

### Ownership and knowledge

| Instruction | Fields | Runtime effect |
|---|---|---|
| `Transfer` | `endpoint`, `target`, `bundle` | Transfers endpoint ownership and associated proof bundle to a target coroutine. |
| `Tag` | `fact`, `dst` | Tags a local knowledge fact and returns the result in `dst`. |
| `Check` | `knowledge`, `target`, `dst` | Checks a fact under the active flow policy and writes the check result to `dst`. |

### Control

| Instruction | Fields | Runtime effect |
|---|---|---|
| `Set` | `dst`, `val` | Writes an immediate value to a register. |
| `Move` | `dst`, `src` | Copies a register value. |
| `Jump` | `target` | Performs an unconditional jump. |
| `Spawn` | `target`, `args` | Spawns a child coroutine in cooperative execution. Threaded runtime rejects this opcode today. |
| `Yield` | none | Yields back to the scheduler. |
| `Halt` | none | Terminates coroutine execution. |

## Compilation From Local Types

`rust/vm/src/compiler.rs` exposes `compile(local_type: &LocalTypeR) -> Vec<Instr>`.

The compiler emits only communication and control instructions. It does not emit guard, speculation, or ownership opcodes.

| `LocalTypeR` node | Emission pattern |
|---|---|
| single-branch `Send` | `Send` then `Invoke` then continuation |
| multi-branch `Send` | deterministic `Offer` on first branch then continuation |
| single-branch `Recv` | `Receive` then `Invoke` then continuation |
| multi-branch `Recv` | `Choose` with patched jump table then branch blocks |
| `Mu` | records loop target then compiles body |
| `Var` | `Jump` to loop target if bound, otherwise `Halt` |
| `End` | `Halt` |

The compiler is intentionally simple. Full ISA coverage is provided by direct bytecode construction and runtime loaders.

## Related Docs

- [VM Architecture](11_vm_architecture.md)
- [Session Lifecycle](13_session_lifecycle.md)
- [Lean-Rust Bridge](19_lean_rust_bridge.md)
