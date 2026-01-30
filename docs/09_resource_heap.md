# Resource Heap

The resource heap provides explicit state management for protocol execution. Resources are allocated with content-addressed identifiers and consumed with nullifier tracking. This enables replay protection, deterministic execution, and ZK compatibility.

## Overview

The resource heap provides three capabilities. It tracks allocated resources with unique identifiers. It prevents double-consumption through nullifier sets. It supports Merkleization for verifiable state proofs.

## Motivation

Channel consumption is implicit in traditional session type implementations. The resource heap makes consumption explicit for several benefits.

Replay protection prevents processing the same message twice. Byzantine fault detection proves protocol violations with heap state. ZK compatibility represents state as a Merkle tree. Deterministic execution ensures heap operations are pure functions.

## Resource Model

Resources are protocol artifacts with unique identifiers.

```rust
pub struct ResourceId {
    hash: [u8; 32],
    counter: u64,
}

pub enum Resource {
    Channel(ChannelState),
    Message(Message),
    Session { role: String, type_hash: u64 },
    Value { tag: String, data: Vec<u8> },
}
```

The `ResourceId` stores a content hash and an allocation counter. The `Resource` enum represents different kinds of heap-allocated values.

## Heap Structure

The heap stores resources in a deterministic data structure.

```rust
pub struct Heap {
    resources: BTreeMap<ResourceId, Resource>,
    nullifiers: BTreeSet<ResourceId>,
    counter: u64,
}
```

Resources are stored in a `BTreeMap` for deterministic iteration order. Nullifiers track consumed resources. The allocation counter ensures unique IDs for identical content.

## Heap Operations

All heap operations are pure functions returning new heap values.

### Allocation

```rust
impl Heap {
    pub fn alloc(&self, resource: Resource) -> (ResourceId, Heap) {
        let rid = ResourceId::from_resource(&resource, self.counter);
        let mut new_heap = self.clone();
        new_heap.resources.insert(rid.clone(), resource);
        new_heap.counter += 1;
        (rid, new_heap)
    }
}
```

Allocation creates a new resource ID from the content hash and counter. The counter ensures unique IDs when allocating identical content multiple times.

### Consumption

```rust
impl Heap {
    pub fn consume(&self, rid: &ResourceId) -> Result<Heap, HeapError> {
        if self.nullifiers.contains(rid) {
            return Err(HeapError::AlreadyConsumed(rid.clone()));
        }
        if !self.resources.contains_key(rid) {
            return Err(HeapError::NotFound(rid.clone()));
        }
        let mut new_heap = self.clone();
        new_heap.nullifiers.insert(rid.clone());
        Ok(new_heap)
    }
}
```

Consumption adds the resource ID to the nullifier set. Double-consumption fails with an error. The resource remains in the heap for reference but is marked as consumed.

### Reading

```rust
impl Heap {
    pub fn read(&self, rid: &ResourceId) -> Result<&Resource, HeapError> {
        if self.is_consumed(rid) {
            return Err(HeapError::AlreadyConsumed(rid.clone()));
        }
        self.resources.get(rid).ok_or(HeapError::NotFound(rid.clone()))
    }

    pub fn is_consumed(&self, rid: &ResourceId) -> bool {
        self.nullifiers.contains(rid)
    }
}
```

Reading retrieves a resource by ID and fails if it was consumed. The `is_consumed` method checks the nullifier set.

## Nullifier Tracking

Nullifiers prevent double-spending of resources.

```rust
let (msg_id, heap1) = heap.alloc(Resource::Message(msg));
let heap2 = heap1.consume(&msg_id)?;
let result = heap2.consume(&msg_id); // Error: AlreadyConsumed
```

Once a resource is consumed, subsequent consumption attempts fail. This provides replay protection at the heap level.

## Merkleization

The heap state can be converted to a Merkle tree for verification.

```rust
use telltale_choreography::{HeapCommitment, MerkleTree};

let tree = MerkleTree::from_heap(&heap);
let root = tree.root;
let proof = tree.prove(0);
let commitment = HeapCommitment::from_heap(&heap);
```

The Merkle root commits to the active resources in the heap. `MerkleTree::prove` generates inclusion proofs by leaf index. `HeapCommitment::from_heap` combines resource and nullifier roots with the allocation counter.

## Integration with Configuration

The heap replaces ad-hoc state tracking in protocol configurations.

```rust
pub struct Configuration {
    processes: Vec<RoleProcess>,
    heap: Heap,
}
```

Channels become heap-allocated resources. Messages are enqueued via allocation and dequeued via consumption. Session state is tracked as a resource.

## Reduction Semantics

Protocol reduction rules use heap operations.

The Send rule allocates a message resource.

```rust
fn reduce_send(config: Configuration, from: Role, to: Role, msg: Message)
    -> Configuration
{
    let (msg_id, new_heap) = config.heap.alloc(Resource::Message(msg));
    Configuration { heap: new_heap, ..config }
}
```

The Recv rule consumes a message resource.

```rust
fn reduce_recv(config: Configuration, rid: ResourceId)
    -> Result<(Message, Configuration), ReductionError>
{
    let msg = config.heap.read(&rid)?;
    let new_heap = config.heap.consume(&rid)?;
    Ok((msg.clone(), Configuration { heap: new_heap, ..config }))
}
```

This makes message passing explicit and verifiable.

## Determinism Requirements

All heap operations are deterministic.

Resource IDs derive from content hash plus allocation counter. The `BTreeMap` and `BTreeSet` provide deterministic iteration order. Serialization produces sorted `(ResourceId, Resource)` pairs.

No `HashMap` or `HashSet` appears in heap implementation. This ensures the same operations produce the same results across executions.

## Lean Correspondence

The Lean formalization defines heap types and operations.

```lean
structure ResourceId where
  id : ContentId
  deriving DecidableEq, BEq, Hashable

inductive Resource where
  | channel : ChannelState → Resource
  | message : Message → Resource
  | session : LocalTypeR → Resource

structure Heap where
  resources : RBMap ResourceId Resource compare
  nullifiers : RBSet ResourceId compare

def Heap.alloc (h : Heap) (r : Resource) : (ResourceId × Heap) := ...
def Heap.consume (h : Heap) (rid : ResourceId) : Except HeapError Heap := ...
def Heap.read (h : Heap) (rid : ResourceId) : Except HeapError Resource := ...
```

Verification theorems are proven for heap properties.

```lean
theorem alloc_consume_succeeds (h : Heap) (r : Resource) :
  let (rid, h') := h.alloc r
  (h'.consume rid).isOk = true

theorem consume_consume_fails (h : Heap) (rid : ResourceId) :
  (h.consume rid).isOk → (h.consume rid >>= fun h' => h'.consume rid).isErr
```

These theorems ensure allocation followed by consumption succeeds, and double-consumption fails.

## Error Types

```rust
pub enum HeapError {
    NotFound(ResourceId),
    AlreadyConsumed(ResourceId),
    AlreadyExists(ResourceId),
    TypeMismatch { expected: String, got: String },
    Other(String),
}
```

Errors provide context for debugging heap operations.

## Usage Example

```rust
use telltale_choreography::{Heap, HeapMessage, MerkleTree, Resource};

// Create empty heap
let heap = Heap::new();

// Allocate a message
let msg = HeapMessage::new("Alice", "Bob", "ping", vec![], 0);
let (msg_id, heap) = heap.alloc(Resource::Message(msg));

// Check resource exists
assert!(!heap.is_consumed(&msg_id));

// Consume the message
let heap = heap.consume(&msg_id)?;
assert!(heap.is_consumed(&msg_id));

// Double consumption fails
assert!(heap.consume(&msg_id).is_err());

// Compute Merkle root for verification
let tree = MerkleTree::from_heap(&heap);
let root = tree.root;
let proof = tree.prove(0);
```

This example demonstrates allocation, consumption, and Merkle proof generation. The proof uses a leaf index from the active resource list.

## ZK Compatibility

The heap design supports zero-knowledge proof systems.

Merkle proofs enable proving resource existence without revealing the full heap. Nullifier proofs enable proving consumption without revealing which resource was consumed. The deterministic structure ensures proof verification is reproducible.

Custom hashers can be introduced for ZK-friendly hashing when generating circuit-compatible proofs.
