# Content Addressing

Content addressing assigns stable hashes to protocol artifacts. The hash is computed from a canonical serialization, which enables memoization and structural sharing.

## ContentId and Hasher

`ContentId` wraps a hash digest produced by a `Hasher`.

```rust
pub trait Hasher: Clone + Default + PartialEq + Send + Sync + 'static {
    type Digest: AsRef<[u8]> + Clone + PartialEq + Eq + Hash + Send + Sync + 'static;
    const HASH_SIZE: usize;
    fn digest(data: &[u8]) -> Self::Digest;
    fn algorithm_name() -> &'static str;
}

pub type DefaultContentHasher = Blake3Hasher;

pub struct ContentId<H: Hasher = DefaultContentHasher> {
    hash: H::Digest,
}
```

`DefaultContentHasher` is the central policy alias for content addressing and currently resolves to `Blake3Hasher`. SHA-256 remains available as an explicit alternative behind the `sha256` crate feature when compatibility matters. A custom `Hasher` implementation can still trade off speed or proof system constraints.

The runtime heap reuses the same `Hasher` abstraction, but it does not share the same byte-level encoding contract.
Heap resources use the runtime-local canonical format described in [Resource Heap](802_resource_heap.md).
That separation is intentional.

## Contentable

Types that can be serialized canonically implement `Contentable`.

```rust
pub trait Contentable: Sized {
    fn to_bytes(&self) -> Result<Vec<u8>, ContentableError>;
    fn from_bytes(bytes: &[u8]) -> Result<Self, ContentableError>;
    fn to_template_bytes(&self) -> Result<Vec<u8>, ContentableError>;
}
```

`GlobalType`, `LocalTypeR`, `Label`, and `PayloadSort` implement this trait. The serializer converts types to a de Bruijn representation and normalizes branch ordering. Alpha equivalent types share the same content ID.

## Closed vs Open Terms

`content_id` is defined for closed terms only. Open terms use `template_id`, which includes an explicit free-variable interface in the serialized template envelope.

```rust
use telltale_types::{GlobalType, Label};
use telltale_types::contentable::Contentable;

let open = GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("free_t"));
assert!(open.content_id_default().is_err());

let template_id = open.template_id_default()?;
let template_bytes = open.to_template_bytes()?;
```

Template bytes and template IDs enable caching and comparing partially specified protocols before all binders are resolved.

## Serialization Formats

JSON is the default format. DAG-CBOR is available with the `dag-cbor` feature and produces compact binary output.

```rust
use telltale_types::{GlobalType, Label};
use telltale_types::contentable::Contentable;

let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
let json_bytes = g.to_bytes()?;
let cid = g.content_id_default()?;
```

JSON and DAG-CBOR produce different content IDs for the same value. One format should be used consistently within a system. Switching formats is a cache-boundary event that requires regenerating persisted IDs.

## ContentStore

`ContentStore` maps content IDs to cached values and tracks cache metrics.

```rust
use telltale_types::content_store::ContentStore;
use telltale_types::{GlobalType, Label, LocalTypeR};

let mut store: ContentStore<GlobalType, LocalTypeR> = ContentStore::new();
let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
let local = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);

store.insert(&global, local.clone())?;
let cached = store.get(&global)?;
```

`KeyedContentStore` adds an additional key alongside the content ID for composite lookups.

## Memoization Pattern

Content IDs are useful for caching projection results.

```rust
use std::collections::HashMap;
use telltale_types::{ContentId, GlobalType, Label, LocalTypeR};
use telltale_theory::project;

let global = GlobalType::send("Alice", "Bob", Label::new("ping"), GlobalType::End);
let mut cache: HashMap<(ContentId<_>, String), LocalTypeR> = HashMap::new();
let cid = global.content_id_default()?;
let key = (cid, "Alice".to_string());

if let Some(cached) = cache.get(&key) {
    // use cached
} else {
    let local = project(&global, "Alice")?;
    cache.insert(key, local);
}
```

This avoids repeated projection work when the same global type appears multiple times.

See [Choreographic Projection Patterns](203_projection.md) for the projection pipeline and [Resource Heap](802_resource_heap.md) for higher-level storage patterns.
