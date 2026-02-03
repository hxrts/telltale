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

pub struct ContentId<H: Hasher = Sha256Hasher> {
    hash: H::Digest,
}
```

SHA-256 is the default hasher. You can provide a custom `Hasher` to trade off speed or proof system constraints.

## Contentable

Types that can be serialized canonically implement `Contentable`.

```rust
pub trait Contentable: Sized {
    fn to_bytes(&self) -> Result<Vec<u8>, ContentableError>;
    fn from_bytes(bytes: &[u8]) -> Result<Self, ContentableError>;
}
```

`GlobalType`, `LocalTypeR`, `Label`, and `PayloadSort` implement this trait. The serializer converts types to a de Bruijn representation and normalizes branch ordering, so alpha equivalent types share the same content ID.

## Serialization Formats

JSON is the default format. DAG-CBOR is available with the `dag-cbor` feature and produces compact binary output.

```rust
use telltale_types::{GlobalType, Label};
use telltale_types::contentable::Contentable;

let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
let json_bytes = g.to_bytes()?;
let cid = g.content_id_sha256()?;
```

JSON and DAG-CBOR produce different content IDs for the same value. Choose one format consistently within a system.

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

Use `KeyedContentStore` when you need an additional key alongside the content ID.

## Memoization Pattern

Content IDs are useful for caching projection results.

```rust
use std::collections::HashMap;
use telltale_types::{ContentId, GlobalType, Label};
use telltale_theory::project;

let global = GlobalType::send("Alice", "Bob", Label::new("ping"), GlobalType::End);
let mut cache: HashMap<(ContentId<_>, String), LocalTypeR> = HashMap::new();
let cid = global.content_id_sha256()?;
let key = (cid, "Alice".to_string());

if let Some(cached) = cache.get(&key) {
    // use cached
} else {
    let local = project(&global, "Alice")?;
    cache.insert(key, local);
}
```

This avoids repeated projection work when the same global type appears multiple times.

See [Projection](05_projection.md) for the projection pipeline and [Resource Heap](22_resource_heap.md) for higher level storage patterns.
