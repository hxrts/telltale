# Heap Encoding and Commitments

This document specifies the canonical byte encoding and commitment inputs for the runtime heap.
It complements [Resource Heap](802_resource_heap.md) by defining the byte-level contract instead of the API surface.

## Scope

The heap uses a runtime-local canonical binary format.
It does not reuse the type-level artifact encoding in [Content Addressing](801_content_addressing.md).
The current format is versioned by `HEAP_ENCODING_VERSION`.

## Canonical Encoding Model

Every canonical heap value starts with the same prelude.
The prelude is the four-byte magic value `TTHP`, followed by the little-endian encoding version, followed by a one-byte type tag.
The remainder of the byte sequence is the canonical body for that tagged value.

Strings and byte slices use explicit little-endian `u32` length prefixes.
Counters and numeric fields use little-endian integer encoding.
Nested heap values are encoded as full canonical child values.

## Covered Types

The current canonical encoding covers `MessagePayload`, `ChannelState`, `Message`, and `Resource`.
`ChannelState` includes sender, receiver, queue length, and every queued payload in order.
`Message` includes source, destination, full payload content, and sequence number.
`Resource::Session` includes role and `type_hash`.
`Resource::Value` includes `tag` and full `data`.

## Resource Identity

`ResourceId` remains allocation-unique in the current design.
The heap computes it as `hash(resource_canonical_bytes || allocation_counter_le)`.
The digest uses the selected heap hasher, which defaults to `DefaultHeapHasher`.

This design keeps repeated allocations of identical semantic resources distinct.
It also ties the ID contract directly to the canonical heap encoding boundary.

## Merkle Leaves and Commitments

Active-resource leaves hash `resource_id_digest || resource_canonical_bytes`.
Nullifier leaves currently use the `ResourceId` digest bytes directly.
`HeapCommitment` combines the active-resource root, the nullifier root, and the allocation counter.
`HeapCommitment::hash()` then hashes those three values with the selected heap hasher.

See [Resource Heap](802_resource_heap.md) for the public heap APIs.
See [API Reference](805_api_reference.md) for the exported runtime heap types.

## Cross-Implementation Expectations

Another implementation should reproduce canonical bytes exactly.
It should also preserve active-resource ordering and nullifier ordering exactly.
The published heap test vectors are the conformance target for that behavior.

The heap container and Merkle utilities are still Rust-first.
This document defines the boundary that a parity lane or external embedder must match.
