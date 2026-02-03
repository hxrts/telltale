# Session Lifecycle

This document details session state management and buffer configuration.

## Session State

A session represents an active protocol instance in the VM.

```rust
pub struct Session {
    pub id: SessionId,
    pub roles: Vec<Role>,
    pub status: SessionStatus,
    pub buffers: HashMap<Edge, Buffer>,
    pub types: HashMap<Role, LocalTypeR>,
}

pub enum SessionStatus {
    Active,
    Draining,
    Closed,
}
```

The `Session` struct holds the session ID, participating roles, and current status. The `buffers` map holds message queues indexed by edge. The `types` map tracks the current local type for each role.

The session progresses through three statuses. Active sessions allow all operations. Draining sessions accept no new sends but allow receives to empty buffers. Closed sessions reject all operations.

## Lifecycle Overview

```mermaid
sequenceDiagram
    participant VM
    participant Session
    participant Buffers
    participant Coroutines

    Note over VM,Coroutines: Opening Phase
    VM->>Session: create(roles, local_types)
    Session->>Buffers: allocate(role_pairs, config)
    Buffers-->>Session: buffer_map
    Session->>Session: status = Active
    VM->>Coroutines: spawn(role, program_id, session_id)
    Session-->>VM: session_id

    Note over VM,Coroutines: Active Phase
    loop Protocol Execution
        Coroutines->>Session: lookup_type(role)
        Session-->>Coroutines: current_type
        alt Send Operation
            Coroutines->>Buffers: enqueue(edge, value)
            Buffers-->>Coroutines: Sent | Blocked
        else Recv Operation
            Coroutines->>Buffers: dequeue(edge)
            Buffers-->>Coroutines: value | RecvWait
        end
        Coroutines->>Session: update_type(role, continuation)
    end

    Note over VM,Coroutines: Draining Phase
    VM->>Session: close(session_id)
    Session->>Session: status = Draining
    loop Drain Buffers
        Coroutines->>Buffers: dequeue(edge)
        Buffers-->>Coroutines: value
    end

    Note over VM,Coroutines: Closed Phase
    Session->>Buffers: release_all()
    Session->>Session: status = Closed
    VM->>VM: release_namespace(session_id)
```

This diagram shows the four phases of a session lifecycle. The opening phase allocates resources and spawns coroutines. The active phase executes protocol operations with type state tracking. The draining phase empties buffers while rejecting new sends. The closed phase releases all resources.

## Opening Sessions

The `Open` instruction creates a new session through several phases.

Buffer allocation creates a bounded buffer for each role pair. The buffer configuration specifies capacity and mode. All buffers start empty with type state initialized from the code image.

```rust
fn open_session(
    vm: &mut VM,
    roles: &[Role],
    local_types: &[(Role, LocalTypeR)],
) -> SessionId {
    let sid = vm.next_session_id();
    let buffers = allocate_buffers(roles, &vm.config.buffer_config);
    let types = local_types.iter().cloned().collect();
    vm.sessions.insert(Session {
        id: sid,
        roles: roles.to_vec(),
        status: SessionStatus::Active,
        buffers,
        types,
    });
    sid
}
```

The function generates a fresh session ID and allocates resources.

Handler binding associates effect handlers with edges during open. Each edge must have exactly one handler. The handler must satisfy the transport specification for that edge.

## Type State Management

The VM tracks the current local type for each role as the session progresses.

```rust
impl Session {
    pub fn lookup_type(&self, role: &Role) -> Option<&LocalTypeR> {
        self.types.get(role)
    }

    pub fn update_type(&mut self, role: &Role, new_type: LocalTypeR) {
        self.types.insert(role.clone(), new_type);
    }
}
```

The `lookup_type` method retrieves the current type for a role. The `update_type` method advances the type after an instruction executes.

Recursive types require unfolding before use. The `unfold_mu` function substitutes the recursion body for the variable.

```rust
fn unfold_mu(lt: &LocalTypeR) -> LocalTypeR {
    match lt {
        LocalTypeR::Mu { var, body } => {
            substitute(body, var, lt)
        }
        _ => lt.clone(),
    }
}
```

The function handles the `Mu` constructor by performing substitution.

## Bounded Buffers

Each buffer has a mode that controls message handling.

```rust
pub enum BufferMode {
    FIFO,
    LatestValue,
}
```

The `FIFO` mode preserves message ordering. Messages are delivered in the order they were sent. The buffer behaves as a bounded queue.

The `LatestValue` mode keeps only the most recent message. Older messages are discarded when a new message arrives. This mode suits scenarios where only current state matters.

```rust
pub struct Buffer {
    pub mode: BufferMode,
    pub capacity: usize,
    pub messages: VecDeque<Value>,
    pub backpressure: BackpressurePolicy,
}
```

The `Buffer` struct holds configuration and message storage.

## Backpressure Policies

Backpressure policies determine behavior when a send would exceed buffer capacity.

```rust
pub enum BackpressurePolicy {
    Block,
    Drop,
    Error,
    Resize { max_capacity: usize },
}
```

The `Block` policy causes the sending coroutine to block until space becomes available. The `Drop` policy silently discards the message and continues. The `Error` policy causes the send instruction to fault. The `Resize` policy grows the buffer up to the maximum capacity.

```rust
fn try_send(buffer: &mut Buffer, value: Value) -> SendResult {
    if buffer.messages.len() < buffer.capacity {
        buffer.messages.push_back(value);
        return SendResult::Sent;
    }
    match buffer.backpressure {
        BackpressurePolicy::Block => SendResult::Blocked,
        BackpressurePolicy::Drop => SendResult::Sent,
        BackpressurePolicy::Error => SendResult::Faulted,
        BackpressurePolicy::Resize { max_capacity } => {
            if buffer.capacity < max_capacity {
                buffer.capacity += 1;
                buffer.messages.push_back(value);
                SendResult::Sent
            } else {
                SendResult::Blocked
            }
        }
    }
}
```

The function implements the backpressure logic for each policy.

## Closing Sessions

The `Close` instruction terminates a session through several phases.

The session status transitions to Draining. No new sends are accepted. Pending receives continue to drain remaining buffered messages.

```rust
fn close_session(vm: &mut VM, sid: SessionId) -> CloseResult {
    let session = vm.sessions.get_mut(&sid)?;
    session.status = SessionStatus::Draining;

    // Wait for buffers to empty
    if session.buffers.values().any(|b| !b.messages.is_empty()) {
        return CloseResult::Draining;
    }

    // Release resources
    session.status = SessionStatus::Closed;
    vm.release_namespace(sid);
    CloseResult::Closed
}
```

The function transitions the session through draining to closed.

Once all buffers are empty, the session releases its namespace. The namespace removal prevents further access. Any subsequent operation on the session causes a fault.
