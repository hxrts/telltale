# Content Addressing

Content addressing assigns cryptographic identities to protocol artifacts. Each value receives a unique hash derived from its canonical serialization. This enables structural sharing, memoization, and verifiable protocol state.

## Overview

The content addressing system provides three capabilities. It computes deterministic content IDs for all protocol types. It enables memoization of expensive operations like projection. It supports structural sharing for memory efficiency.

## ContentId

The `ContentId` type wraps a cryptographic hash of a value's canonical form.

```rust
use rumpsteak_types::{ContentId, Sha256Hasher};

let g = GlobalType::comm("A", "B", vec![(Label::new("msg"), GlobalType::End)]);
let cid = ContentId::<Sha256Hasher>::new(&g);
```

The content ID is computed from the DAG-CBOR serialization of the type. Two structurally equivalent types produce the same content ID.

## Hasher Trait

The hash algorithm is configurable through the `Hasher` trait.

```rust
pub trait Hasher: Clone + Default {
    const HASH_SIZE: usize;
    fn hash(data: &[u8]) -> Vec<u8>;
}
```

SHA-256 is the default implementation. Other implementations are available for specific use cases.

The `Sha256Hasher` provides cryptographic security and broad compatibility. The `Blake3Hasher` offers faster performance for non-cryptographic use cases. The `PoseidonHasher` enables ZK circuit compatibility.

## Contentable Trait

Types that support content addressing implement the `Contentable` trait.

```rust
pub trait Contentable {
    fn to_cbor(&self) -> Vec<u8>;
    fn from_cbor(data: &[u8]) -> Result<Self, ContentError>;
}
```

The `to_cbor` method produces a canonical byte representation. The `from_cbor` method reconstructs the value from bytes.

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
