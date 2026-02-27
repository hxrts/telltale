//! Content Store for Memoization and Deduplication
//!
//! This module provides a content-addressed store for memoizing expensive
//! computations and deduplicating structurally identical values.
//!
//! # Design
//!
//! The `ContentStore` maps `ContentId` to values, enabling:
//! - Memoization of expensive computations (e.g., projection)
//! - Structural sharing of identical protocol artifacts
//! - Cache hit/miss metrics for performance analysis
//!
//! # Lean Correspondence
//!
//! This corresponds to the memoization infrastructure in the Lean formalization.

use crate::content_id::{ContentId, Hasher, Sha256Hasher};
use crate::contentable::{Contentable, ContentableError};
use std::collections::HashMap;
use std::hash::Hash as StdHash;
use std::sync::atomic::{AtomicU64, Ordering};

/// Metrics for cache performance analysis.
#[derive(Debug, Clone, Default)]
pub struct CacheMetrics {
    /// Number of cache hits
    pub hits: u64,
    /// Number of cache misses
    pub misses: u64,
    /// Number of items currently stored
    pub size: usize,
}

impl CacheMetrics {
    /// Calculate the hit rate as a percentage.
    #[must_use]
    pub fn hit_rate(&self) -> f64 {
        let total = self.hits + self.misses;
        if total == 0 {
            0.0
        } else {
            (self.hits as f64 / total as f64) * 100.0
        }
    }
}

/// A content-addressed store for memoization and deduplication.
///
/// Values are stored by their content ID, ensuring that structurally
/// identical values share storage and enabling efficient cache lookups.
///
/// # Type Parameters
///
/// - `K`: The content key type (must implement `Contentable`)
/// - `V`: The cached value type
/// - `H`: The hash algorithm (default: `Sha256Hasher`)
///
/// # Examples
///
/// ```
/// use telltale_types::content_store::ContentStore;
/// use telltale_types::{GlobalType, LocalTypeR, Label};
///
/// let mut store: ContentStore<GlobalType, LocalTypeR> = ContentStore::new();
///
/// let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
/// let local = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
///
/// // Store a projection result
/// store.insert(&global, local.clone()).unwrap();
///
/// // Retrieve it later (cache hit)
/// assert_eq!(store.get(&global).unwrap(), Some(&local));
/// ```
#[derive(Debug)]
pub struct ContentStore<K: Contentable, V, H: Hasher + Eq + StdHash = Sha256Hasher> {
    store: HashMap<ContentId<H>, V>,
    collision_witnesses: Option<HashMap<ContentId<H>, Vec<u8>>>,
    hits: AtomicU64,
    misses: AtomicU64,
    _key: std::marker::PhantomData<K>,
}

impl<K: Contentable, V, H: Hasher + Eq + StdHash> Default for ContentStore<K, V, H> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Contentable, V, H: Hasher + Eq + StdHash> ContentStore<K, V, H> {
    /// Create a new empty content store.
    #[must_use]
    pub fn new() -> Self {
        Self {
            store: HashMap::new(),
            collision_witnesses: None,
            hits: AtomicU64::new(0),
            misses: AtomicU64::new(0),
            _key: std::marker::PhantomData,
        }
    }

    /// Create a new content store that validates `ContentId` collisions by
    /// storing canonical-byte witnesses.
    #[must_use]
    pub fn new_collision_defended() -> Self {
        Self {
            store: HashMap::new(),
            collision_witnesses: Some(HashMap::new()),
            hits: AtomicU64::new(0),
            misses: AtomicU64::new(0),
            _key: std::marker::PhantomData,
        }
    }

    /// Create a content store with pre-allocated capacity.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            store: HashMap::with_capacity(capacity),
            collision_witnesses: None,
            hits: AtomicU64::new(0),
            misses: AtomicU64::new(0),
            _key: std::marker::PhantomData,
        }
    }

    /// Create a pre-sized collision-defended content store.
    #[must_use]
    pub fn with_capacity_collision_defended(capacity: usize) -> Self {
        Self {
            store: HashMap::with_capacity(capacity),
            collision_witnesses: Some(HashMap::with_capacity(capacity)),
            hits: AtomicU64::new(0),
            misses: AtomicU64::new(0),
            _key: std::marker::PhantomData,
        }
    }

    /// Get a cached value by its content key.
    ///
    /// Updates cache metrics (hit/miss counters).
    pub fn get(&self, key: &K) -> Result<Option<&V>, ContentableError> {
        let cid = key.content_id::<H>()?;
        if let Some(v) = self.store.get(&cid) {
            if let Some(witnesses) = &self.collision_witnesses {
                let bytes = key.to_bytes()?;
                if witnesses.get(&cid).is_some_and(|stored| stored != &bytes) {
                    return Err(ContentableError::InvalidFormat(
                        "content-id collision detected during get".to_string(),
                    ));
                }
            }
            self.hits.fetch_add(1, Ordering::Relaxed);
            return Ok(Some(v));
        }
        self.misses.fetch_add(1, Ordering::Relaxed);
        Ok(None)
    }

    /// Insert a value into the store.
    ///
    /// Returns the previous value if the key already existed.
    pub fn insert(&mut self, key: &K, value: V) -> Result<Option<V>, ContentableError> {
        let cid = key.content_id::<H>()?;
        if let Some(witnesses) = &mut self.collision_witnesses {
            let bytes = key.to_bytes()?;
            if let Some(stored) = witnesses.get(&cid) {
                if stored != &bytes {
                    return Err(ContentableError::InvalidFormat(
                        "content-id collision detected during insert".to_string(),
                    ));
                }
            } else {
                witnesses.insert(cid.clone(), bytes);
            }
        }
        Ok(self.store.insert(cid, value))
    }

    /// Get or compute a value.
    ///
    /// If the key exists, returns the cached value (cache hit).
    /// Otherwise, computes the value using the provided function,
    /// stores it, and returns a reference (cache miss).
    pub fn get_or_insert_with<F>(&mut self, key: &K, f: F) -> Result<&V, ContentableError>
    where
        F: FnOnce() -> V,
    {
        let cid = key.content_id::<H>()?;
        if let Some(witnesses) = &mut self.collision_witnesses {
            let bytes = key.to_bytes()?;
            if let Some(stored) = witnesses.get(&cid) {
                if stored != &bytes {
                    return Err(ContentableError::InvalidFormat(
                        "content-id collision detected during get_or_insert_with".to_string(),
                    ));
                }
            } else {
                witnesses.insert(cid.clone(), bytes);
            }
        }
        match self.store.entry(cid) {
            std::collections::hash_map::Entry::Occupied(entry) => {
                self.hits.fetch_add(1, Ordering::Relaxed);
                Ok(entry.into_mut())
            }
            std::collections::hash_map::Entry::Vacant(entry) => {
                self.misses.fetch_add(1, Ordering::Relaxed);
                Ok(entry.insert(f()))
            }
        }
    }

    /// Check if a key exists in the store.
    pub fn contains(&self, key: &K) -> Result<bool, ContentableError> {
        let cid = key.content_id::<H>()?;
        Ok(self.store.contains_key(&cid))
    }

    /// Remove a value from the store.
    pub fn remove(&mut self, key: &K) -> Result<Option<V>, ContentableError> {
        let cid = key.content_id::<H>()?;
        let removed = self.store.remove(&cid);
        if removed.is_some() && self.collision_witnesses.is_some() {
            if let Some(witnesses) = &mut self.collision_witnesses {
                witnesses.remove(&cid);
            }
        }
        Ok(removed)
    }

    /// Clear all entries from the store.
    pub fn clear(&mut self) {
        self.store.clear();
        if let Some(witnesses) = &mut self.collision_witnesses {
            witnesses.clear();
        }
    }

    /// Get the number of entries in the store.
    #[must_use]
    pub fn len(&self) -> usize {
        self.store.len()
    }

    /// Check if the store is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.store.is_empty()
    }

    /// Get cache performance metrics.
    #[must_use]
    pub fn metrics(&self) -> CacheMetrics {
        CacheMetrics {
            hits: self.hits.load(Ordering::Relaxed),
            misses: self.misses.load(Ordering::Relaxed),
            size: self.store.len(),
        }
    }

    /// Reset cache metrics to zero.
    pub fn reset_metrics(&self) {
        self.hits.store(0, Ordering::Relaxed);
        self.misses.store(0, Ordering::Relaxed);
    }
}

impl<K: Contentable, V: Clone, H: Hasher + Eq + StdHash> Clone for ContentStore<K, V, H> {
    fn clone(&self) -> Self {
        Self {
            store: self.store.clone(),
            collision_witnesses: self.collision_witnesses.clone(),
            hits: AtomicU64::new(self.hits.load(Ordering::Relaxed)),
            misses: AtomicU64::new(self.misses.load(Ordering::Relaxed)),
            _key: std::marker::PhantomData,
        }
    }
}

/// A keyed content store for memoizing functions with multiple parameters.
///
/// This store uses a composite key of (ContentId, extra key) for caching,
/// useful for functions like projection that depend on both a type and a role.
///
/// # Type Parameters
///
/// - `K`: The content key type (must implement `Contentable`)
/// - `E`: The extra key type (e.g., role name)
/// - `V`: The cached value type
/// - `H`: The hash algorithm (default: `Sha256Hasher`)
///
/// # Examples
///
/// ```
/// use telltale_types::content_store::KeyedContentStore;
/// use telltale_types::{GlobalType, LocalTypeR, Label};
///
/// let mut store: KeyedContentStore<GlobalType, String, LocalTypeR> = KeyedContentStore::new();
///
/// let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
///
/// // Store projection result for role "A"
/// let local_a = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
/// store.insert(&global, "A".to_string(), local_a.clone()).unwrap();
///
/// // Retrieve it later
/// assert_eq!(store.get(&global, &"A".to_string()).unwrap(), Some(&local_a));
///
/// // Different role has different projection
/// assert_eq!(store.get(&global, &"B".to_string()).unwrap(), None);
/// ```
#[derive(Debug)]
pub struct KeyedContentStore<
    K: Contentable,
    E: StdHash + Eq,
    V,
    H: Hasher + Eq + StdHash = Sha256Hasher,
> {
    store: HashMap<ContentId<H>, HashMap<E, V>>,
    collision_witnesses: Option<HashMap<ContentId<H>, Vec<u8>>>,
    hits: AtomicU64,
    misses: AtomicU64,
    _key: std::marker::PhantomData<K>,
}

impl<K: Contentable, E: StdHash + Eq + Clone, V, H: Hasher + Eq + StdHash> Default
    for KeyedContentStore<K, E, V, H>
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K: Contentable, E: StdHash + Eq + Clone, V, H: Hasher + Eq + StdHash>
    KeyedContentStore<K, E, V, H>
{
    /// Create a new empty keyed content store.
    #[must_use]
    pub fn new() -> Self {
        Self {
            store: HashMap::new(),
            collision_witnesses: None,
            hits: AtomicU64::new(0),
            misses: AtomicU64::new(0),
            _key: std::marker::PhantomData,
        }
    }

    /// Create a new keyed content store with collision-defense enabled.
    #[must_use]
    pub fn new_collision_defended() -> Self {
        Self {
            store: HashMap::new(),
            collision_witnesses: Some(HashMap::new()),
            hits: AtomicU64::new(0),
            misses: AtomicU64::new(0),
            _key: std::marker::PhantomData,
        }
    }

    /// Create a keyed content store with pre-allocated capacity.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            store: HashMap::with_capacity(capacity),
            collision_witnesses: None,
            hits: AtomicU64::new(0),
            misses: AtomicU64::new(0),
            _key: std::marker::PhantomData,
        }
    }

    /// Create a pre-sized keyed collision-defended store.
    #[must_use]
    pub fn with_capacity_collision_defended(capacity: usize) -> Self {
        Self {
            store: HashMap::with_capacity(capacity),
            collision_witnesses: Some(HashMap::with_capacity(capacity)),
            hits: AtomicU64::new(0),
            misses: AtomicU64::new(0),
            _key: std::marker::PhantomData,
        }
    }

    /// Get a cached value by precomputed content id and extra key.
    #[must_use]
    pub fn get_with_content_id(&self, cid: &ContentId<H>, extra: &E) -> Option<&V> {
        match self.store.get(cid).and_then(|inner| inner.get(extra)) {
            Some(v) => {
                self.hits.fetch_add(1, Ordering::Relaxed);
                Some(v)
            }
            None => {
                self.misses.fetch_add(1, Ordering::Relaxed);
                None
            }
        }
    }

    /// Get a cached value by content key and extra key.
    pub fn get(&self, key: &K, extra: &E) -> Result<Option<&V>, ContentableError> {
        let cid = key.content_id::<H>()?;
        if let Some(witnesses) = &self.collision_witnesses {
            if witnesses.contains_key(&cid) {
                let bytes = key.to_bytes()?;
                if witnesses.get(&cid).is_some_and(|stored| stored != &bytes) {
                    return Err(ContentableError::InvalidFormat(
                        "content-id collision detected during keyed get".to_string(),
                    ));
                }
            }
        }
        Ok(self.get_with_content_id(&cid, extra))
    }

    /// Insert a value by precomputed content id and extra key.
    pub fn insert_with_content_id(&mut self, cid: ContentId<H>, extra: E, value: V) -> Option<V> {
        self.store.entry(cid).or_default().insert(extra, value)
    }

    /// Insert a value into the store.
    pub fn insert(&mut self, key: &K, extra: E, value: V) -> Result<Option<V>, ContentableError> {
        let cid = key.content_id::<H>()?;
        if let Some(witnesses) = &mut self.collision_witnesses {
            let bytes = key.to_bytes()?;
            if let Some(stored) = witnesses.get(&cid) {
                if stored != &bytes {
                    return Err(ContentableError::InvalidFormat(
                        "content-id collision detected during keyed insert".to_string(),
                    ));
                }
            } else {
                witnesses.insert(cid.clone(), bytes);
            }
        }
        Ok(self.insert_with_content_id(cid, extra, value))
    }

    /// Get or compute a value.
    pub fn get_or_insert_with<F>(&mut self, key: &K, extra: E, f: F) -> Result<&V, ContentableError>
    where
        F: FnOnce() -> V,
    {
        let cid = key.content_id::<H>()?;
        if let Some(witnesses) = &mut self.collision_witnesses {
            let bytes = key.to_bytes()?;
            if let Some(stored) = witnesses.get(&cid) {
                if stored != &bytes {
                    return Err(ContentableError::InvalidFormat(
                        "content-id collision detected during keyed get_or_insert_with".to_string(),
                    ));
                }
            } else {
                witnesses.insert(cid.clone(), bytes);
            }
        }
        match self.store.entry(cid).or_default().entry(extra) {
            std::collections::hash_map::Entry::Occupied(entry) => {
                self.hits.fetch_add(1, Ordering::Relaxed);
                Ok(entry.into_mut())
            }
            std::collections::hash_map::Entry::Vacant(entry) => {
                self.misses.fetch_add(1, Ordering::Relaxed);
                Ok(entry.insert(f()))
            }
        }
    }

    /// Check if a key pair exists in the store.
    pub fn contains(&self, key: &K, extra: &E) -> Result<bool, ContentableError> {
        let cid = key.content_id::<H>()?;
        Ok(self.contains_with_content_id(&cid, extra))
    }

    /// Check if a precomputed content id + extra key exists.
    #[must_use]
    pub fn contains_with_content_id(&self, cid: &ContentId<H>, extra: &E) -> bool {
        self.store.get(cid).is_some_and(|inner| inner.contains_key(extra))
    }

    /// Remove a value from the store.
    pub fn remove(&mut self, key: &K, extra: &E) -> Result<Option<V>, ContentableError> {
        let cid = key.content_id::<H>()?;
        if let Some(inner) = self.store.get_mut(&cid) {
            let removed = inner.remove(extra);
            if inner.is_empty() {
                self.store.remove(&cid);
                if let Some(witnesses) = &mut self.collision_witnesses {
                    witnesses.remove(&cid);
                }
            }
            Ok(removed)
        } else {
            Ok(None)
        }
    }

    /// Clear all entries from the store.
    pub fn clear(&mut self) {
        self.store.clear();
        if let Some(witnesses) = &mut self.collision_witnesses {
            witnesses.clear();
        }
    }

    /// Get the number of entries in the store.
    #[must_use]
    pub fn len(&self) -> usize {
        self.store.values().map(HashMap::len).sum()
    }

    /// Check if the store is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get cache performance metrics.
    #[must_use]
    pub fn metrics(&self) -> CacheMetrics {
        CacheMetrics {
            hits: self.hits.load(Ordering::Relaxed),
            misses: self.misses.load(Ordering::Relaxed),
            size: self.store.len(),
        }
    }

    /// Reset cache metrics to zero.
    pub fn reset_metrics(&self) {
        self.hits.store(0, Ordering::Relaxed);
        self.misses.store(0, Ordering::Relaxed);
    }
}

impl<K: Contentable, E: StdHash + Eq + Clone, V: Clone, H: Hasher + Eq + StdHash> Clone
    for KeyedContentStore<K, E, V, H>
{
    fn clone(&self) -> Self {
        Self {
            store: self.store.clone(),
            collision_witnesses: self.collision_witnesses.clone(),
            hits: AtomicU64::new(self.hits.load(Ordering::Relaxed)),
            misses: AtomicU64::new(self.misses.load(Ordering::Relaxed)),
            _key: std::marker::PhantomData,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::content_id::Hasher;
    use crate::{GlobalType, Label, LocalTypeR};

    #[derive(Clone, Default, PartialEq, Eq, Hash)]
    struct ConstantHasher;

    impl Hasher for ConstantHasher {
        type Digest = [u8; 1];
        const HASH_SIZE: usize = 1;

        fn digest(_data: &[u8]) -> Self::Digest {
            [0u8]
        }

        fn algorithm_name() -> &'static str {
            "constant"
        }
    }

    #[test]
    fn test_content_store_basic() {
        let mut store: ContentStore<GlobalType, LocalTypeR> = ContentStore::new();

        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let local = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);

        // Initially empty
        assert!(store.is_empty());
        assert_eq!(store.get(&global).unwrap(), None);

        // Insert
        store.insert(&global, local.clone()).unwrap();
        assert_eq!(store.len(), 1);

        // Get (cache hit)
        assert_eq!(store.get(&global).unwrap(), Some(&local));

        // Metrics
        let metrics = store.metrics();
        assert_eq!(metrics.hits, 1); // The second get
        assert_eq!(metrics.misses, 1); // The first get before insert
    }

    #[test]
    fn test_content_store_alpha_equivalence() {
        let mut store: ContentStore<GlobalType, String> = ContentStore::new();

        // Two α-equivalent types should map to the same cache entry
        let g1 = GlobalType::mu(
            "x",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("x")),
        );
        let g2 = GlobalType::mu(
            "y",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("y")),
        );

        store.insert(&g1, "result".to_string()).unwrap();

        // g2 should hit the same cache entry
        assert_eq!(store.get(&g2).unwrap(), Some(&"result".to_string()));
    }

    #[test]
    fn test_content_store_get_or_insert_with() {
        let mut store: ContentStore<GlobalType, i32> = ContentStore::new();
        let global = GlobalType::End;

        let mut computed = false;
        let value = store
            .get_or_insert_with(&global, || {
                computed = true;
                42
            })
            .unwrap();
        assert_eq!(*value, 42);
        assert!(computed);

        // Second call should not compute
        computed = false;
        let value = store
            .get_or_insert_with(&global, || {
                computed = true;
                99
            })
            .unwrap();
        assert_eq!(*value, 42); // Same value
        assert!(!computed); // Not recomputed

        let metrics = store.metrics();
        assert_eq!(metrics.hits, 1);
        assert_eq!(metrics.misses, 1);
    }

    #[test]
    fn test_keyed_content_store() {
        let mut store: KeyedContentStore<GlobalType, String, LocalTypeR> = KeyedContentStore::new();

        let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let local_a = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let local_b = LocalTypeR::recv("A", Label::new("msg"), LocalTypeR::End);

        // Store projections for different roles
        store
            .insert(&global, "A".to_string(), local_a.clone())
            .unwrap();
        store
            .insert(&global, "B".to_string(), local_b.clone())
            .unwrap();

        assert_eq!(store.len(), 2);
        assert_eq!(
            store.get(&global, &"A".to_string()).unwrap(),
            Some(&local_a)
        );
        assert_eq!(
            store.get(&global, &"B".to_string()).unwrap(),
            Some(&local_b)
        );
        assert_eq!(store.get(&global, &"C".to_string()).unwrap(), None);
    }

    #[test]
    fn test_cache_metrics() {
        let mut store: ContentStore<GlobalType, i32> = ContentStore::new();
        let g1 = GlobalType::End;
        let g2 = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

        // Miss
        store.get(&g1).unwrap();
        store.get(&g2).unwrap();

        // Insert
        store.insert(&g1, 1).unwrap();

        // Hit
        store.get(&g1).unwrap();
        store.get(&g1).unwrap();

        // Miss again
        store.get(&g2).unwrap();

        let metrics = store.metrics();
        assert_eq!(metrics.misses, 3); // g1 miss, g2 miss, g2 miss
        assert_eq!(metrics.hits, 2); // g1 hit x2
        assert!((metrics.hit_rate() - 40.0).abs() < 0.01); // 2 / 5 = 40%
    }

    #[test]
    fn test_content_store_clear() {
        let mut store: ContentStore<GlobalType, i32> = ContentStore::new();

        store.insert(&GlobalType::End, 1).unwrap();
        store
            .insert(
                &GlobalType::send("A", "B", Label::new("msg"), GlobalType::End),
                2,
            )
            .unwrap();

        assert_eq!(store.len(), 2);

        store.clear();
        assert!(store.is_empty());
    }

    #[test]
    fn test_content_store_remove() {
        let mut store: ContentStore<GlobalType, i32> = ContentStore::new();
        let global = GlobalType::End;

        store.insert(&global, 42).unwrap();
        assert!(store.contains(&global).unwrap());

        let removed = store.remove(&global).unwrap();
        assert_eq!(removed, Some(42));
        assert!(!store.contains(&global).unwrap());
    }

    #[test]
    fn test_collision_defense_rejects_hash_alias_in_content_store() {
        let mut store: ContentStore<GlobalType, i32, ConstantHasher> =
            ContentStore::new_collision_defended();
        let g1 = GlobalType::send("A", "B", Label::new("x"), GlobalType::End);
        let g2 = GlobalType::send("A", "B", Label::new("y"), GlobalType::End);
        store.insert(&g1, 1).expect("first insert should succeed");
        let result = store.insert(&g2, 2);
        assert!(matches!(result, Err(ContentableError::InvalidFormat(_))));
    }

    #[test]
    fn test_collision_defense_rejects_hash_alias_in_keyed_store() {
        let mut store: KeyedContentStore<GlobalType, String, i32, ConstantHasher> =
            KeyedContentStore::new_collision_defended();
        let g1 = GlobalType::send("A", "B", Label::new("x"), GlobalType::End);
        let g2 = GlobalType::send("A", "B", Label::new("y"), GlobalType::End);
        store
            .insert(&g1, "A".to_string(), 1)
            .expect("first insert should succeed");
        let result = store.insert(&g2, "B".to_string(), 2);
        assert!(matches!(result, Err(ContentableError::InvalidFormat(_))));
    }
}
