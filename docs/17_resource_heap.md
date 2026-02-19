# Resource Heap

The resource heap provides explicit state tracking for protocol resources. It stores content addressed resources, records consumption in a nullifier set, and can produce Merkle commitments.

## Overview

The heap lives in `telltale_choreography::heap`. It is immutable by default, so operations return a new heap value and preserve deterministic behavior.

## Resource Types

Resources are immutable values with content based identifiers.

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

`ResourceId` combines a content hash with an allocation counter. The hash is derived from a simple byte encoding of the resource, so identical resources with different counters still receive unique IDs.

## Heap Structure

The heap stores resources and nullifiers in ordered maps.

```rust
pub struct Heap {
    resources: BTreeMap<ResourceId, Resource>,
    nullifiers: BTreeSet<ResourceId>,
    counter: u64,
}
```

`BTreeMap` and `BTreeSet` provide deterministic iteration order for reproducible hashing and proofs.

## Heap Operations

Allocate and consume resources using the functional API.

```rust
let heap = Heap::new();
let (msg_id, heap) = heap.alloc_message("Alice", "Bob", "Ping", vec![1, 2, 3], 0);
let heap = heap.consume(&msg_id)?;
```

`consume` marks a resource as nullified while keeping it in the heap. `read` returns an error if the resource does not exist or has already been consumed.

## Merkle Commitments

Merkle trees commit to active resources and nullifiers.

```rust
use telltale_choreography::heap::{HeapCommitment, MerkleTree};

let tree = MerkleTree::from_heap(&heap);
let proof = tree.prove(0);
let commitment = HeapCommitment::from_heap(&heap);
```

`MerkleTree::from_heap` hashes active resources. `HeapCommitment` combines the resource root, nullifier root, and allocation counter.

## Error Types

Heap operations return `HeapError` values.

```rust
pub enum HeapError {
    NotFound(ResourceId),
    AlreadyConsumed(ResourceId),
    AlreadyExists(ResourceId),
    TypeMismatch { expected: String, got: String },
    Other(String),
}
```

Use these errors to distinguish missing resources from double consumption.

## Determinism Notes

All operations are deterministic and avoid hash map iteration order. The resource byte encoding is currently a bespoke format, and future work may replace it with a canonical codec.

See [Content Addressing](16_content_addressing.md) for the type level content ID system and [Effect Handlers](08_effect_handlers.md) for runtime integration.
