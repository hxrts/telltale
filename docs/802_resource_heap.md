# Resource Heap

The resource heap provides explicit runtime state tracking for choreography-layer resources.
It stores resources under deterministic identifiers, tracks consumed resources in a nullifier set, and can derive Merkle commitments for the current heap state.
This module lives in `telltale_runtime::heap`.

## Scope

The heap is a `telltale-runtime` utility.
It is not the same system as the type-level content addressing in `telltale-types`.
The runtime heap uses the shared `Hasher` abstraction with its own heap-local encoding and commitment logic.

The heap abstraction is currently Rust-only.
The resource concepts correspond loosely to `lean/Runtime/Resources/ResourceModel.lean`, but the heap container and Merkle utilities do not currently have a first-class Lean mirror.

## Resource Identifiers

Resources are identified by `ResourceId`.
Each ID stores a hasher digest and an allocation counter.
The current default uses the shared BLAKE3 policy through `DefaultContentHasher`.
The identifier is computed by hashing the resource byte encoding plus the allocation counter.

```rust
pub struct ResourceId<H: Hasher = DefaultContentHasher> {
    hash: H::Digest,
    counter: u64,
}
```

This means the identifier is allocation-unique rather than pure-content-stable.
Two identical resources allocated with different counters produce different `ResourceId` values.
That behavior is intentional in the current runtime heap.

## Resource Types

The heap stores four resource kinds.

```rust
pub enum Resource {
    Channel(ChannelState),
    Message(Message),
    Session { role: String, type_hash: u64 },
    Value { tag: String, data: Vec<u8> },
}
```

`ChannelState` stores sender, receiver, and an in-memory queue of `MessagePayload`.
`Message` stores source, destination, label, payload bytes, and a sequence number.
`Session` stores a role name and a `type_hash` value.

## Heap Structure

The heap uses deterministic ordered containers.

```rust
pub struct Heap<H: Hasher = DefaultContentHasher> {
    resources: BTreeMap<ResourceId<H>, Resource>,
    nullifiers: BTreeSet<ResourceId<H>>,
    counter: u64,
}
```

`BTreeMap` and `BTreeSet` give stable iteration order.
That stable order is important for reproducible commitments and proofs.
The nullifier set records consumed resource IDs without deleting them from the resource map.

## Heap APIs

The heap supports both functional and mutable update styles.
The functional APIs return a new heap value.
The mutable APIs exist for efficient in-place construction and updates.

```rust
use telltale_runtime::heap::{DefaultHeapHasher, Heap, Resource};

let heap = Heap::<DefaultHeapHasher>::new();
let msg = Resource::message("Alice", "Bob", "Ping", vec![1, 2, 3], 0);
let (msg_id, heap) = heap.alloc(msg);
let heap = heap.consume(&msg_id)?;
```

`alloc(...)`, `consume(...)`, `remove(...)`, `alloc_many(...)`, and `consume_many(...)` are the main functional operations.
`alloc_mut(...)` and `consume_mut(...)` provide mutable variants.
`consume_many(...)` validates the whole batch first and then nullifies all requested resources atomically.

`read(...)` only succeeds for active resources.
If a resource has been consumed, `read(...)` returns `HeapError::AlreadyConsumed`.
Use `contains(...)`, `is_consumed(...)`, `is_active(...)`, `active_resources(...)`, and `consumed_ids(...)` when you need explicit state inspection.

## Size and Retention Semantics

`size()` returns the number of entries in the resource map.
Consumed resources still count toward that number because `consume(...)` keeps them in the heap and only adds a nullifier.
`nullified_count()` reports the number of consumed resource IDs.

`remove(...)` is the operation that actually deletes a resource from the heap.
It also removes the resource from the nullifier set if it was already consumed.
This makes `remove(...)` a cleanup operation rather than a normal consumption operation.

## Merkle Commitments

The heap can derive Merkle commitments over its current state.
`MerkleTree::from_heap(...)` builds a Merkle tree from active resources only.
`HeapCommitment::from_heap(...)` combines the active-resource root, the nullifier root, and the allocation counter.

```rust
use telltale_runtime::heap::{HeapCommitment, MerkleTree};

let tree = MerkleTree::from_heap(&heap);
let proof = tree.prove(0);
let commitment = HeapCommitment::from_heap(&heap);
```

`prove(...)` generates an inclusion proof by leaf index in the current active-resource ordering.
That ordering follows `BTreeMap` iteration over active `ResourceId` keys.
`HeapCommitment::hash()` then hashes the two roots plus the counter with the selected heap hasher.

## Error Types

Heap operations use `HeapError`.

```rust
pub enum HeapError<H: Hasher = DefaultContentHasher> {
    NotFound(ResourceId<H>),
    AlreadyConsumed(ResourceId<H>),
    AlreadyExists(ResourceId<H>),
    TypeMismatch { expected: String, got: String },
    Other(String),
}
```

In the current implementation, `NotFound` and `AlreadyConsumed` are the main operational cases returned by heap methods.
`AlreadyExists` and `TypeMismatch` are part of the public error vocabulary but are not heavily exercised by the basic heap operations shown above.

## Serialization and Hashing Notes

The current resource byte encoding is a simplified bespoke format.
It is not the same canonical serialization system used by `telltale-types::Contentable`.
It also does not encode every field in full detail.

For example, channel encoding currently includes sender, receiver, and queue length rather than the full queued payload contents.
Message encoding currently includes source, destination, label, and sequence number, but not the full payload bytes.
The heap should therefore be understood as using a deterministic runtime-local identifier scheme, not as a general canonical content-addressing layer.

## Determinism Notes

Heap operations are deterministic because they use ordered maps and sets and avoid hash-map iteration order.
`state_hash()` provides a simple debug-oriented heap summary based on resource counters and nullifiers.
It is not a cryptographic commitment and should not be treated as one.

Use `HeapCommitment` when you need a cryptographic summary of heap state.
Use [Content Addressing](801_content_addressing.md) for the type-level artifact identity system.
Use [Choreography Effect Handlers](301_effect_handlers.md) for choreography runtime integration.
