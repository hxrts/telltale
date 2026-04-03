# Resource Heap

The resource heap provides explicit runtime state tracking for choreography-layer resources.
It stores resources under deterministic identifiers, tracks consumed resources in a nullifier set, and can derive Merkle commitments for the current heap state.
This module lives in `telltale_runtime::heap`.

## Scope

The heap is a `telltale-runtime` utility.
It is not the same system as the type-level content addressing in `telltale-types`.
The runtime heap uses the shared `Hasher` abstraction with its own canonical heap encoding and commitment logic.

The heap now has a focused Lean parity mirror.
`lean/Runtime/Resources/HeapModel.lean` mirrors canonical bytes, tagged preimages, ordering rules, proof-index semantics, and deterministic replay for the published heap corpus.
Digest computation remains Rust-side and is checked against published vectors rather than reimplemented in Lean.

## Resource Identifiers

Resources are identified by `ResourceId`.
Each ID stores a hasher digest and an allocation counter.
The current default uses the shared BLAKE3 policy through `DefaultContentHasher`.
The identifier is computed by hashing the canonical resource bytes plus the allocation counter.

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
`resource_id_preimage(...)`, `resource_leaf_preimage(...)`, `nullifier_leaf_preimage(...)`, `merkle_node_preimage(...)`, and `heap_commitment_preimage(...)` expose the tagged preimage rules directly.
`resource_leaf_hash(...)`, `nullifier_leaf_hash(...)`, and `merkle_node_hash(...)` then hash those preimages.
`HeapCommitment::hash()` then hashes a tagged preimage that contains the two roots and the counter.

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

## Encoding and Hashing Guarantees

The heap uses a versioned canonical binary format for resources.
Every canonical heap value starts with the `TTHP` magic prefix, a little-endian encoding version, and a one-byte type tag.
Strings and byte slices use explicit little-endian `u32` length prefixes.
Nested heap values are encoded as full canonical child values.

The heap also uses tagged preimages for `ResourceId`, resource-leaf hashes, nullifier-leaf hashes, Merkle internal nodes, and `HeapCommitment::hash()`.
Those tagged preimages are part of the public heap contract.

### Canonical Encoding Model

The heap uses a runtime-local canonical binary format.
It does not reuse the type-level artifact encoding in [Content Addressing](801_content_addressing.md).
The current format is versioned by `HEAP_ENCODING_VERSION`.

Every canonical heap value starts with the same prelude.
The prelude is the four-byte magic value `TTHP`, followed by the little-endian encoding version, followed by a one-byte type tag.
The remainder of the byte sequence is the canonical body for that tagged value.

Strings and byte slices use explicit little-endian `u32` length prefixes.
Counters and numeric fields use little-endian integer encoding.
Nested heap values are encoded as full canonical child values.

### Covered Types

`ChannelState` encoding includes sender, receiver, queue length, and every queued `MessagePayload` in order.
`Message` encoding includes source, destination, label, full payload bytes, and sequence number.
`Session` and `Value` resources encode all of their current semantic fields.

The current canonical encoding also covers `MessagePayload`, `ChannelState`, `Message`, and `Resource`.
`Resource::Session` includes role and `type_hash`.
`Resource::Value` includes `tag` and full `data`.

### Resource Identity

`ResourceId` remains allocation-unique in the current design.
The heap computes it from a tagged preimage that contains the canonical resource bytes and the little-endian allocation counter.
The digest uses the selected heap hasher, which defaults to `DefaultHeapHasher`.

This design keeps repeated allocations of identical semantic resources distinct.
It also ties the ID contract directly to the canonical heap encoding boundary.

### Merkle Leaves and Commitments

Active-resource leaves hash a tagged preimage that contains the `ResourceId` digest and the canonical resource bytes.
Nullifier leaves hash a distinct tagged preimage that contains the `ResourceId` digest bytes.
Internal Merkle nodes hash a tagged preimage that contains the left child digest and the right child digest.
`HeapCommitment` stores the active-resource root, the nullifier root, and the allocation counter.
`HeapCommitment::hash()` hashes a tagged preimage that contains those three values.

The allocation counter remains part of the authoritative commitment contract.
This keeps the commitment aligned with allocation history rather than only current live content.
The current heap model treats that history as semantically relevant.

### Cross-Implementation Expectations

Another implementation should reproduce canonical bytes exactly.
It should also preserve active-resource ordering and nullifier ordering exactly.
The published heap test vectors are the conformance target for that behavior.
The current published vector file is `rust/runtime/tests/data/heap_vectors_v1.json`.

The runtime heap now has a Lean parity mirror for canonical bytes and tagged preimages.
That mirror lives in `lean/Runtime/Resources/HeapModel.lean` and is exercised through `lean/Runtime/Tests/HeapParityRunner.lean`.

The digest algorithm itself is still treated as an operational conformance target.
Rust and Lean must agree on the published heap vectors exactly, but Lean does not currently reimplement BLAKE3.
This section therefore defines both the boundary that an external embedder must match and the boundary that the current Rust↔Lean heap lane enforces.

See [Rust-Lean Bridge and Parity](703_rust_lean_parity.md) for the Lean mirror boundary.

## Determinism Contract

Heap operations are deterministic by contract.
Active-resource ordering follows `ResourceId` ordering in the heap `BTreeMap`.
Consumed-resource ordering follows the same `ResourceId` ordering in the nullifier `BTreeSet`.
Merkle proof indices refer to that exact active-resource order.

### Ordering Rules

Active resources are ordered by `ResourceId`.
`ResourceId` ordering compares digest bytes first and allocation counter second.
`Heap::active_resources()` uses that order because the heap stores resources in a `BTreeMap`.

Consumed resource IDs are ordered by the same `ResourceId` ordering.
`Heap::consumed_ids()` uses that order because the heap stores nullifiers in a `BTreeSet`.
Merkle leaves follow the iteration order of `active_resources()`.
Merkle proof indices refer to that exact active-leaf order.

### Replay Contract

Repeated executions of the same heap operation sequence must yield the same `ResourceId` values, proof paths, and `HeapCommitment` values.
This contract is sequence-sensitive.
If allocation order changes, the allocation counter changes.
That changes `ResourceId` values and therefore changes commitments.

### Commitment Authority

`HeapCommitment` is the authoritative cryptographic summary of heap state.
`HeapCommitment::hash()` is the only supported single-value digest for that state.
The heap no longer exposes a separate debug-only state fingerprint.

### Order-Insensitive Operations

Some operations are deterministic even when their input lists are permuted.
`consume_many(...)` is one example.
If the same set of resource IDs is consumed successfully, the resulting nullifier set and heap commitment must match regardless of argument order.

### Scope

This contract now has a focused Lean mirror.
`lean/Runtime/Resources/HeapModel.lean` mirrors active/nullifier ordering, proof-index semantics, and deterministic replay for the published heap corpus.
The published vectors and the strict Rust↔Lean heap parity suite are the current conformance boundary for other implementations.

Use [Content Addressing](801_content_addressing.md) for the type-level artifact identity system.
Use [Choreography Effect Handlers](301_effect_handlers.md) for choreography runtime integration.
See [Rust-Lean Bridge and Parity](703_rust_lean_parity.md) for the Rust↔Lean conformance lane.
