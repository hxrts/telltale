# Content Addressing

Content addressing assigns cryptographic identities to protocol artifacts. Each value receives a unique hash derived from its canonical serialization. This enables structural sharing, memoization, and verifiable protocol state.

## Overview

The content addressing system provides three capabilities. It computes deterministic content IDs for all protocol types. It enables memoization of expensive operations like projection. It supports structural sharing for memory efficiency.

## ContentId

The `ContentId` type wraps a cryptographic hash of a value's canonical form.

```rust
use rumpsteak_types::{ContentId, Sha256Hasher, GlobalType, Label};
use rumpsteak_types::contentable::Contentable;

let g = GlobalType::comm("A", "B", vec![(Label::new("msg"), GlobalType::End)]);
let cid: ContentId<Sha256Hasher> = ContentId::from_bytes(&g.to_bytes());
```

The content ID is computed from the canonical JSON bytes of the value. Two structurally equivalent types produce the same content ID. DAG-CBOR is a possible future encoding.

## Hasher Trait

The hash algorithm is configurable through the `Hasher` trait.

```rust
pub trait Hasher: Clone + Default + PartialEq + Send + Sync + 'static {
    const HASH_SIZE: usize;
    fn digest(data: &[u8]) -> Vec<u8>;
    fn algorithm_name() -> &'static str;
}
```

SHA-256 is the default implementation. Additional hashers can be implemented by users when a different tradeoff is required.

The `Sha256Hasher` provides cryptographic security and broad compatibility. Custom hashers can target performance or proof system constraints.

## Contentable Trait

Types that support content addressing implement the `Contentable` trait.

```rust
pub trait Contentable {
    fn to_bytes(&self) -> Vec<u8>;
    fn from_bytes(data: &[u8]) -> Result<Self, ContentableError>;
}
```

The `to_bytes` method produces a canonical byte representation. The `from_bytes` method reconstructs the value from bytes.

Implementations exist for `GlobalType`, `LocalTypeR`, `Label`, and `PayloadSort`. Custom types can implement the trait for integration.

## Deterministic Serialization

Content addressing requires deterministic serialization. Two invariants ensure this property.

Branch ordering sorts labeled branches by label name before serialization. This ensures `{a: T1, b: T2}` and `{b: T2, a: T1}` produce the same content ID.

De Bruijn indices replace named variables with numeric indices. This ensures alpha-equivalent types produce the same content ID.

```
Named:       μx. A → B : x        μy. A → B : y
De Bruijn:   μ. A → B : 0         μ. A → B : 0
```

The conversion to de Bruijn form happens during serialization. The runtime representation retains named variables for debugging.

## De Bruijn Conversion

The de Bruijn representation is computed on demand for serialization.

```rust
impl GlobalType {
    fn to_de_bruijn(&self) -> GlobalTypeDB {
        self.to_de_bruijn_with_env(&[])
    }
}
```

The environment tracks bound variables. Each `Mu` binding extends the environment. Variable references are converted to indices.

```rust
GlobalType::Var(name) => {
    let index = env.iter().position(|&v| v == name).unwrap_or(0);
    GlobalTypeDB::Var(index)
}
```

This transformation is internal to the serialization layer.

## Memoization

Content IDs enable efficient memoization of expensive operations.

```rust
use rumpsteak_theory::ProjectionCache;

let cache = ProjectionCache::new();
let local = cache.project(&global, "Alice")?;
```

The cache uses `(ContentId, Role)` pairs as keys. Repeated projections of the same global type return cached results.

Cache statistics are available for performance analysis.

```rust
let stats = cache.stats();
println!("Hits: {}, Misses: {}", stats.hits, stats.misses);
```

This reports cache hit and miss counts. It can be used in profiling runs.

## Content Store

The `ContentStore` provides deduplication for protocol artifacts.

```rust
use rumpsteak_types::ContentStore;

let mut store = ContentStore::new();
let cid = store.insert(global_type);
let retrieved = store.get(&cid);
```

Identical types are stored once regardless of how many times they are inserted. The store uses content IDs as keys for O(1) lookup.

## Lean Correspondence

The Lean formalization defines equivalent types and proofs.

```lean
structure ContentId (H : Type) [Hasher H] where
  hash : ByteArray
  deriving DecidableEq, BEq, Hashable

class Contentable (α : Type) where
  toCbor : α → ByteArray
  fromCbor : ByteArray → Except String α

def contentId [Hasher H] [Contentable α] (x : α) : ContentId H :=
  ⟨Hasher.hash H (Contentable.toCbor x)⟩
```

The `fromCbor ∘ toCbor = id` property is proven for all contentable types. This ensures round-trip correctness.

## Verification Properties

Several properties are verified in Lean.

Content equivalence holds when two values with the same content ID are structurally equal. This assumes collision resistance of the hash function.

Projection determinism holds when the same global type and role always produce the same local type. Content IDs enable caching without correctness concerns.

Alpha equivalence holds when de Bruijn conversion produces identical results for alpha-equivalent types.

## Usage Example

```rust
use rumpsteak_types::{GlobalType, ContentId, Sha256Hasher, ContentStore};
use rumpsteak_theory::ProjectionCache;

// Create a protocol
let ping_pong = GlobalType::comm(
    "Alice", "Bob",
    vec![
        (Label::new("ping"), GlobalType::comm(
            "Bob", "Alice",
            vec![(Label::new("pong"), GlobalType::End)],
        )),
    ],
);

// Compute content ID
let cid = ContentId::<Sha256Hasher>::new(&ping_pong);
println!("Protocol CID: {:?}", cid);

// Store in content-addressed storage
let mut store = ContentStore::new();
store.insert(ping_pong.clone());

// Project with memoization
let cache = ProjectionCache::new();
let alice_type = cache.project(&ping_pong, "Alice")?;
let bob_type = cache.project(&ping_pong, "Bob")?;
```

This example demonstrates content ID computation, storage, and memoized projection.
