# Heap Determinism Contract

This document states the deterministic behavior that the runtime heap promises.
It complements [Resource Heap](802_resource_heap.md) and [Heap Encoding and Commitments](808_heap_encoding_commitments.md).

## Ordering Rules

Active resources are ordered by `ResourceId`.
`ResourceId` ordering compares digest bytes first and allocation counter second.
`Heap::active_resources()` uses that order because the heap stores resources in a `BTreeMap`.

Consumed resource IDs are ordered by the same `ResourceId` ordering.
`Heap::consumed_ids()` uses that order because the heap stores nullifiers in a `BTreeSet`.
Merkle leaves follow the iteration order of `active_resources()`.
Merkle proof indices refer to that exact active-leaf order.

## Replay Contract

The same heap operation sequence must produce the same `ResourceId` values.
It must also produce the same active-resource order, proof paths, and `HeapCommitment` values.
This contract is tested directly in the runtime heap test suite.

The contract is sequence-sensitive.
If allocation order changes, the allocation counter changes.
That changes `ResourceId` values and therefore changes commitments.

## Commitment Authority

`HeapCommitment` is the authoritative cryptographic summary of heap state.
`HeapCommitment::hash()` is the only supported single-value digest for that state.
The heap no longer exposes a separate debug-only state fingerprint.

## Order-Insensitive Operations

Some operations are deterministic even when their input lists are permuted.
`consume_many(...)` is one example.
If the same set of resource IDs is consumed successfully, the resulting nullifier set and heap commitment must match regardless of argument order.

## Scope

This contract is currently Rust-first.
The heap container and proof utilities do not yet have a first-class Lean mirror.
The published vectors and tests are the current conformance boundary for other implementations.
