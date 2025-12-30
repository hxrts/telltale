//! # Heap Implementation
//!
//! Deterministic heap for explicit resource management.
//!
//! ## Overview
//!
//! This module provides a pure, deterministic heap for managing protocol resources.
//! The heap uses BTreeMap/BTreeSet for O(log n) operations with deterministic iteration order.
//!
//! Key properties:
//! - **Immutable API**: All operations return new heaps (functional style)
//! - **Deterministic**: Same operations produce identical results
//! - **Content-addressed**: Resources identified by content hash
//! - **Nullifier tracking**: Consumed resources are tracked to prevent double-spending
//!
//! ## Lean Correspondence
//!
//! This module corresponds to `lean/Rumpsteak/Protocol/Heap.lean`:
//! - `Heap` ↔ Lean's `Heap`
//! - `alloc` ↔ Lean's `Heap.alloc`
//! - `consume` ↔ Lean's `Heap.consume`
//! - `read` ↔ Lean's `Heap.read`

use super::resource::{HeapError, Resource, ResourceId};
use std::collections::{BTreeMap, BTreeSet};

/// Deterministic heap for protocol resources.
///
/// Uses BTreeMap for O(log n) operations with deterministic iteration order.
/// The nullifiers set tracks consumed resources to prevent double-spending.
#[derive(Debug, Clone, Default)]
pub struct Heap {
    /// Map from ResourceId to Resource
    resources: BTreeMap<ResourceId, Resource>,
    /// Set of consumed (nullified) resource IDs
    nullifiers: BTreeSet<ResourceId>,
    /// Counter for generating unique ResourceIds
    counter: u64,
}

impl Heap {
    /// Create an empty heap.
    pub fn new() -> Self {
        Self::default()
    }

    /// Get the number of active (non-nullified) resources.
    pub fn size(&self) -> usize {
        self.resources.len()
    }

    /// Get the number of nullified resources.
    pub fn nullified_count(&self) -> usize {
        self.nullifiers.len()
    }

    /// Check if a resource exists in the heap (not necessarily active).
    pub fn contains(&self, rid: &ResourceId) -> bool {
        self.resources.contains_key(rid)
    }

    /// Check if a resource has been consumed (nullified).
    pub fn is_consumed(&self, rid: &ResourceId) -> bool {
        self.nullifiers.contains(rid)
    }

    /// Check if a resource is active (exists and not consumed).
    pub fn is_active(&self, rid: &ResourceId) -> bool {
        self.contains(rid) && !self.is_consumed(rid)
    }

    /// Get the current allocation counter.
    pub fn alloc_counter(&self) -> u64 {
        self.counter
    }

    /// Allocate a new resource on the heap.
    ///
    /// Returns the new ResourceId and updated heap.
    /// The ResourceId is derived from the resource content and allocation counter.
    pub fn alloc(&self, resource: Resource) -> (ResourceId, Heap) {
        let rid = ResourceId::from_resource(&resource, self.counter);
        let mut new_heap = self.clone();
        new_heap.resources.insert(rid.clone(), resource);
        new_heap.counter += 1;
        (rid, new_heap)
    }

    /// Allocate a resource mutably (for efficiency when building heaps).
    pub fn alloc_mut(&mut self, resource: Resource) -> ResourceId {
        let rid = ResourceId::from_resource(&resource, self.counter);
        self.resources.insert(rid.clone(), resource);
        self.counter += 1;
        rid
    }

    /// Read a resource from the heap.
    ///
    /// Returns an error if the resource doesn't exist or has been consumed.
    pub fn read(&self, rid: &ResourceId) -> Result<&Resource, HeapError> {
        if self.is_consumed(rid) {
            return Err(HeapError::AlreadyConsumed(rid.clone()));
        }
        self.resources
            .get(rid)
            .ok_or_else(|| HeapError::NotFound(rid.clone()))
    }

    /// Consume a resource, adding it to the nullifier set.
    ///
    /// Returns an error if the resource doesn't exist or has already been consumed.
    /// The resource remains in the heap but is marked as consumed.
    pub fn consume(&self, rid: &ResourceId) -> Result<Heap, HeapError> {
        if self.is_consumed(rid) {
            return Err(HeapError::AlreadyConsumed(rid.clone()));
        }
        if !self.contains(rid) {
            return Err(HeapError::NotFound(rid.clone()));
        }
        let mut new_heap = self.clone();
        new_heap.nullifiers.insert(rid.clone());
        Ok(new_heap)
    }

    /// Consume a resource mutably.
    pub fn consume_mut(&mut self, rid: &ResourceId) -> Result<(), HeapError> {
        if self.is_consumed(rid) {
            return Err(HeapError::AlreadyConsumed(rid.clone()));
        }
        if !self.contains(rid) {
            return Err(HeapError::NotFound(rid.clone()));
        }
        self.nullifiers.insert(rid.clone());
        Ok(())
    }

    /// Remove a resource from the heap entirely (for cleanup).
    ///
    /// Unlike `consume`, this removes the resource from both maps.
    /// Returns an error if the resource doesn't exist.
    pub fn remove(&self, rid: &ResourceId) -> Result<Heap, HeapError> {
        if !self.contains(rid) {
            return Err(HeapError::NotFound(rid.clone()));
        }
        let mut new_heap = self.clone();
        new_heap.resources.remove(rid);
        new_heap.nullifiers.remove(rid);
        Ok(new_heap)
    }

    /// Get all active (non-consumed) resources.
    pub fn active_resources(&self) -> impl Iterator<Item = (&ResourceId, &Resource)> {
        self.resources
            .iter()
            .filter(|(rid, _)| !self.nullifiers.contains(*rid))
    }

    /// Get all consumed resource IDs.
    pub fn consumed_ids(&self) -> impl Iterator<Item = &ResourceId> {
        self.nullifiers.iter()
    }

    /// Allocate multiple resources at once.
    pub fn alloc_many(
        &self,
        resources: impl IntoIterator<Item = Resource>,
    ) -> (Vec<ResourceId>, Heap) {
        let mut new_heap = self.clone();
        let rids: Vec<_> = resources
            .into_iter()
            .map(|r| new_heap.alloc_mut(r))
            .collect();
        (rids, new_heap)
    }

    /// Try to consume multiple resources atomically.
    ///
    /// If any consumption fails, returns the error without modifying the heap.
    pub fn consume_many(&self, rids: &[ResourceId]) -> Result<Heap, HeapError> {
        // First validate all can be consumed
        for rid in rids {
            if self.is_consumed(rid) {
                return Err(HeapError::AlreadyConsumed(rid.clone()));
            }
            if !self.contains(rid) {
                return Err(HeapError::NotFound(rid.clone()));
            }
        }
        // Then consume all
        let mut new_heap = self.clone();
        for rid in rids {
            new_heap.nullifiers.insert(rid.clone());
        }
        Ok(new_heap)
    }

    /// Create a channel resource and allocate it.
    pub fn alloc_channel(&self, sender: &str, receiver: &str) -> (ResourceId, Heap) {
        self.alloc(Resource::channel(sender, receiver))
    }

    /// Create a message resource and allocate it.
    pub fn alloc_message(
        &self,
        source: &str,
        dest: &str,
        label: &str,
        payload: Vec<u8>,
        seq_no: u64,
    ) -> (ResourceId, Heap) {
        self.alloc(Resource::message(source, dest, label, payload, seq_no))
    }

    /// Create a session state resource and allocate it.
    pub fn alloc_session(&self, role: &str, type_hash: u64) -> (ResourceId, Heap) {
        self.alloc(Resource::session(role, type_hash))
    }

    /// Compute a simple hash of the heap state (for debugging).
    ///
    /// A real implementation would compute a Merkle root.
    pub fn state_hash(&self) -> u64 {
        let resource_hash: u64 = self
            .resources
            .keys()
            .fold(0u64, |acc, rid| acc ^ rid.counter);
        let nullifier_hash: u64 = self
            .nullifiers
            .iter()
            .fold(0u64, |acc, rid| acc ^ rid.counter);
        resource_hash ^ nullifier_hash ^ self.counter
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_heap_alloc() {
        let heap = Heap::new();
        assert_eq!(heap.size(), 0);
        assert_eq!(heap.alloc_counter(), 0);

        let resource = Resource::channel("Alice", "Bob");
        let (rid, heap) = heap.alloc(resource);

        assert_eq!(heap.size(), 1);
        assert_eq!(heap.alloc_counter(), 1);
        assert!(heap.contains(&rid));
        assert!(heap.is_active(&rid));
    }

    #[test]
    fn test_heap_read() {
        let heap = Heap::new();
        let resource = Resource::channel("Alice", "Bob");
        let (rid, heap) = heap.alloc(resource);

        let read_resource = heap.read(&rid).unwrap();
        assert_eq!(read_resource.kind(), "channel");

        // Reading nonexistent resource fails
        let fake_rid = ResourceId::new([0u8; 32], 999);
        assert!(heap.read(&fake_rid).is_err());
    }

    #[test]
    fn test_heap_consume() {
        let heap = Heap::new();
        let resource = Resource::channel("Alice", "Bob");
        let (rid, heap) = heap.alloc(resource);

        assert!(!heap.is_consumed(&rid));
        let heap = heap.consume(&rid).unwrap();
        assert!(heap.is_consumed(&rid));
        assert!(!heap.is_active(&rid));

        // Can still read consumed resources for verification
        assert!(heap.contains(&rid));

        // But read() should fail
        assert!(heap.read(&rid).is_err());

        // Double consume fails
        assert!(heap.consume(&rid).is_err());
    }

    #[test]
    fn test_heap_remove() {
        let heap = Heap::new();
        let resource = Resource::channel("Alice", "Bob");
        let (rid, heap) = heap.alloc(resource);

        let heap = heap.remove(&rid).unwrap();
        assert!(!heap.contains(&rid));
        assert_eq!(heap.size(), 0);
    }

    #[test]
    fn test_heap_alloc_many() {
        let heap = Heap::new();
        let resources = vec![
            Resource::channel("Alice", "Bob"),
            Resource::channel("Bob", "Carol"),
            Resource::message("Alice", "Bob", "Hello", vec![], 0),
        ];

        let (rids, heap) = heap.alloc_many(resources);

        assert_eq!(rids.len(), 3);
        assert_eq!(heap.size(), 3);
        assert_eq!(heap.alloc_counter(), 3);
    }

    #[test]
    fn test_heap_consume_many() {
        let heap = Heap::new();
        let (rids, heap) = heap.alloc_many(vec![
            Resource::channel("Alice", "Bob"),
            Resource::channel("Bob", "Carol"),
        ]);

        let heap = heap.consume_many(&rids).unwrap();
        assert!(heap.is_consumed(&rids[0]));
        assert!(heap.is_consumed(&rids[1]));
        assert_eq!(heap.nullified_count(), 2);
    }

    #[test]
    fn test_heap_active_resources() {
        let heap = Heap::new();
        let (rids, heap) = heap.alloc_many(vec![
            Resource::channel("Alice", "Bob"),
            Resource::channel("Bob", "Carol"),
        ]);

        let heap = heap.consume(&rids[0]).unwrap();

        let active: Vec<_> = heap.active_resources().collect();
        assert_eq!(active.len(), 1);
        assert_eq!(active[0].0, &rids[1]);
    }

    #[test]
    fn test_heap_determinism() {
        let h1 = Heap::new();
        let h2 = Heap::new();

        let r1 = Resource::channel("Alice", "Bob");
        let r2 = Resource::channel("Alice", "Bob");

        let (rid1, h1) = h1.alloc(r1);
        let (rid2, h2) = h2.alloc(r2);

        // Same operations → same results
        assert_eq!(rid1, rid2);
        assert_eq!(h1.state_hash(), h2.state_hash());
    }

    #[test]
    fn test_heap_state_hash() {
        let heap = Heap::new();
        let hash1 = heap.state_hash();

        let (_, heap) = heap.alloc(Resource::channel("Alice", "Bob"));
        let hash2 = heap.state_hash();

        assert_ne!(hash1, hash2);
    }

    #[test]
    fn test_helper_methods() {
        let heap = Heap::new();

        let (rid1, heap) = heap.alloc_channel("Alice", "Bob");
        assert!(matches!(heap.read(&rid1), Ok(Resource::Channel(_))));

        let (rid2, heap) = heap.alloc_message("Alice", "Bob", "Hello", vec![1, 2, 3], 0);
        assert!(matches!(heap.read(&rid2), Ok(Resource::Message(_))));

        let (rid3, heap) = heap.alloc_session("Alice", 12345);
        assert!(matches!(heap.read(&rid3), Ok(Resource::Session { .. })));

        assert_eq!(heap.size(), 3);
    }
}
