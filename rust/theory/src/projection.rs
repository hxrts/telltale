//! Projection of Global Types to Local Types
//!
//! This module implements the projection operation that transforms a global type
//! (bird's-eye view of a protocol) into a local type for a specific role.
//!
//! Based on: "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)
//!
//! # Projection Rules
//!
//! For a global type `G` and role `r`, the projection `G↓r` is defined as:
//!
//! - `end↓r = end`
//! - `(p → q : {lᵢ.Gᵢ})↓r`:
//!   - If `r = p`: `!q{lᵢ.(Gᵢ↓r)}` (sender sees internal choice)
//!   - If `r = q`: `?p{lᵢ.(Gᵢ↓r)}` (receiver sees external choice)
//!   - Otherwise: `merge(Gᵢ↓r)` (non-participant merges branches)
//! - `(μt.G)↓r = μt.(G↓r)`
//! - `t↓r = t`
//!
//! # Memoization
//!
//! For large protocols or repeated projections, use `MemoizedProjector` to cache
//! results by content ID:
//!
//! ```
//! use rumpsteak_theory::projection::MemoizedProjector;
//! use rumpsteak_types::{GlobalType, Label};
//!
//! let mut projector = MemoizedProjector::new();
//! let global = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
//!
//! // First call computes and caches
//! let a_view = projector.project(&global, "A").unwrap();
//!
//! // Second call uses cached result
//! let a_view_again = projector.project(&global, "A").unwrap();
//! assert_eq!(a_view, a_view_again);
//!
//! // Check cache metrics
//! let metrics = projector.metrics();
//! assert_eq!(metrics.hits, 1);
//! assert_eq!(metrics.misses, 1);
//! ```

use crate::merge::{merge_all, MergeError};
use rumpsteak_types::content_store::{CacheMetrics, KeyedContentStore};
use rumpsteak_types::{GlobalType, Label, LocalTypeR};
use thiserror::Error;

/// Errors that can occur during projection
#[derive(Debug, Clone, Error)]
pub enum ProjectionError {
    /// Role not found in the protocol
    #[error("role '{0}' not found in protocol")]
    RoleNotFound(String),

    /// Branches could not be merged for a non-participant
    #[error("cannot merge branches for role '{role}': {source}")]
    MergeFailure {
        role: String,
        #[source]
        source: MergeError,
    },

    /// Empty branches in communication
    #[error("empty branches in communication from {sender} to {receiver}")]
    EmptyBranches { sender: String, receiver: String },
}

/// Result type for projection operations
pub type ProjectionResult = Result<LocalTypeR, ProjectionError>;

/// Project a global type onto a specific role.
///
/// This transforms a bird's-eye view protocol description into the local
/// view for a single participant.
///
/// # Examples
///
/// ```
/// use rumpsteak_theory::project;
/// use rumpsteak_types::{GlobalType, LocalTypeR, Label};
///
/// // A -> B: msg. end
/// let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
///
/// // From A's perspective: send msg to B, then end
/// let a_view = project(&g, "A").unwrap();
/// assert!(matches!(a_view, LocalTypeR::Send { partner, .. } if partner == "B"));
///
/// // From B's perspective: receive msg from A, then end
/// let b_view = project(&g, "B").unwrap();
/// assert!(matches!(b_view, LocalTypeR::Recv { partner, .. } if partner == "A"));
/// ```
pub fn project(global: &GlobalType, role: &str) -> ProjectionResult {
    match global {
        GlobalType::End => Ok(LocalTypeR::End),

        GlobalType::Comm {
            sender,
            receiver,
            branches,
        } => {
            if branches.is_empty() {
                return Err(ProjectionError::EmptyBranches {
                    sender: sender.clone(),
                    receiver: receiver.clone(),
                });
            }

            if role == sender {
                // Sender sees internal choice (send)
                let local_branches: Vec<(Label, LocalTypeR)> = branches
                    .iter()
                    .map(|(label, cont)| {
                        let local_cont = project(cont, role)?;
                        Ok((label.clone(), local_cont))
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(LocalTypeR::Send {
                    partner: receiver.clone(),
                    branches: local_branches,
                })
            } else if role == receiver {
                // Receiver sees external choice (recv)
                let local_branches: Vec<(Label, LocalTypeR)> = branches
                    .iter()
                    .map(|(label, cont)| {
                        let local_cont = project(cont, role)?;
                        Ok((label.clone(), local_cont))
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                Ok(LocalTypeR::Recv {
                    partner: sender.clone(),
                    branches: local_branches,
                })
            } else {
                // Non-participant: merge all branch projections
                let projections: Vec<LocalTypeR> = branches
                    .iter()
                    .map(|(_, cont)| project(cont, role))
                    .collect::<Result<Vec<_>, _>>()?;

                merge_all(&projections).map_err(|e| ProjectionError::MergeFailure {
                    role: role.to_string(),
                    source: e,
                })
            }
        }

        GlobalType::Mu { var, body } => {
            let local_body = project(body, role)?;

            // Optimization: if the role doesn't appear in the body, return End
            // This handles the case where a role is not involved after a recursion point
            if matches!(local_body, LocalTypeR::End) && !body_mentions_role(body, role) {
                return Ok(LocalTypeR::End);
            }

            Ok(LocalTypeR::Mu {
                var: var.clone(),
                body: Box::new(local_body),
            })
        }

        GlobalType::Var(var) => Ok(LocalTypeR::Var(var.clone())),
    }
}

/// Check if a global type body mentions a specific role
fn body_mentions_role(global: &GlobalType, role: &str) -> bool {
    match global {
        GlobalType::End => false,
        GlobalType::Comm {
            sender,
            receiver,
            branches,
        } => {
            sender == role
                || receiver == role
                || branches
                    .iter()
                    .any(|(_, cont)| body_mentions_role(cont, role))
        }
        GlobalType::Mu { body, .. } => body_mentions_role(body, role),
        GlobalType::Var(_) => false,
    }
}

/// Project a global type onto all its roles.
///
/// Returns a map from role names to their local types.
pub fn project_all(global: &GlobalType) -> Result<Vec<(String, LocalTypeR)>, ProjectionError> {
    let roles = global.roles();
    roles
        .into_iter()
        .map(|role| {
            let local = project(global, &role)?;
            Ok((role, local))
        })
        .collect()
}

// ============================================================================
// Memoized Projection
// ============================================================================

/// A memoized projector that caches projection results by content ID.
///
/// Use this for large protocols or when projecting the same global type
/// multiple times. The cache key is `(ContentId(global), role)`, so
/// α-equivalent types share cache entries.
///
/// # Examples
///
/// ```
/// use rumpsteak_theory::projection::MemoizedProjector;
/// use rumpsteak_types::{GlobalType, Label};
///
/// let mut projector = MemoizedProjector::new();
///
/// let global = GlobalType::mu("t",
///     GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t"))
/// );
///
/// // Project for all roles
/// for role in &["A", "B"] {
///     let local = projector.project(&global, role).unwrap();
///     println!("{}: {:?}", role, local);
/// }
///
/// // Check metrics
/// let metrics = projector.metrics();
/// println!("Cache: {} hits, {} misses", metrics.hits, metrics.misses);
/// ```
#[derive(Debug, Clone)]
pub struct MemoizedProjector {
    cache: KeyedContentStore<GlobalType, String, Result<LocalTypeR, ProjectionError>>,
}

impl Default for MemoizedProjector {
    fn default() -> Self {
        Self::new()
    }
}

impl MemoizedProjector {
    /// Create a new memoized projector with empty cache.
    #[must_use]
    pub fn new() -> Self {
        Self {
            cache: KeyedContentStore::new(),
        }
    }

    /// Create a memoized projector with pre-allocated cache capacity.
    #[must_use]
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            cache: KeyedContentStore::with_capacity(capacity),
        }
    }

    /// Project a global type onto a role, using cached result if available.
    ///
    /// On cache miss, computes the projection and caches the result.
    /// On cache hit, returns the cached result directly.
    pub fn project(&mut self, global: &GlobalType, role: &str) -> ProjectionResult {
        let role_key = role.to_string();

        // Check if already cached
        if let Some(result) = self.cache.get(global, &role_key) {
            return result.clone();
        }

        // Compute and cache
        let result = project(global, role);
        self.cache.insert(global, role_key, result.clone());
        result
    }

    /// Project a global type onto all its roles, using cached results.
    pub fn project_all(
        &mut self,
        global: &GlobalType,
    ) -> Result<Vec<(String, LocalTypeR)>, ProjectionError> {
        let roles = global.roles();
        roles
            .into_iter()
            .map(|role| {
                let local = self.project(global, &role)?;
                Ok((role, local))
            })
            .collect()
    }

    /// Get cache performance metrics.
    #[must_use]
    pub fn metrics(&self) -> CacheMetrics {
        self.cache.metrics()
    }

    /// Clear the cache.
    pub fn clear(&mut self) {
        self.cache.clear();
    }

    /// Get the number of cached entries.
    #[must_use]
    pub fn cache_size(&self) -> usize {
        self.cache.len()
    }

    /// Reset cache metrics to zero.
    pub fn reset_metrics(&self) {
        self.cache.reset_metrics();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_project_end() {
        let g = GlobalType::End;
        let local = project(&g, "A").unwrap();
        assert_eq!(local, LocalTypeR::End);
    }

    #[test]
    fn test_project_sender() {
        // A -> B: msg. end
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let local = project(&g, "A").unwrap();

        match local {
            LocalTypeR::Send { partner, branches } => {
                assert_eq!(partner, "B");
                assert_eq!(branches.len(), 1);
                assert_eq!(branches[0].0.name, "msg");
                assert_eq!(branches[0].1, LocalTypeR::End);
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_project_receiver() {
        // A -> B: msg. end
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let local = project(&g, "B").unwrap();

        match local {
            LocalTypeR::Recv { partner, branches } => {
                assert_eq!(partner, "A");
                assert_eq!(branches.len(), 1);
                assert_eq!(branches[0].0.name, "msg");
            }
            _ => panic!("Expected Recv"),
        }
    }

    #[test]
    fn test_project_non_participant() {
        // A -> B: msg. end
        // C is not involved, should get End
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let local = project(&g, "C").unwrap();
        assert_eq!(local, LocalTypeR::End);
    }

    #[test]
    fn test_project_choice() {
        // A -> B: {yes.end, no.end}
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (Label::new("yes"), GlobalType::End),
                (Label::new("no"), GlobalType::End),
            ],
        );

        // A sees internal choice
        let a_local = project(&g, "A").unwrap();
        match a_local {
            LocalTypeR::Send { branches, .. } => {
                assert_eq!(branches.len(), 2);
            }
            _ => panic!("Expected Send"),
        }

        // B sees external choice
        let b_local = project(&g, "B").unwrap();
        match b_local {
            LocalTypeR::Recv { branches, .. } => {
                assert_eq!(branches.len(), 2);
            }
            _ => panic!("Expected Recv"),
        }
    }

    #[test]
    fn test_project_recursive() {
        // μt. A -> B: msg. t
        let g = GlobalType::mu(
            "t",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("t")),
        );

        let a_local = project(&g, "A").unwrap();
        match a_local {
            LocalTypeR::Mu { var, body } => {
                assert_eq!(var, "t");
                match body.as_ref() {
                    LocalTypeR::Send { partner, branches } => {
                        assert_eq!(partner, "B");
                        assert!(matches!(branches[0].1, LocalTypeR::Var(ref v) if v == "t"));
                    }
                    _ => panic!("Expected Send in body"),
                }
            }
            _ => panic!("Expected Mu"),
        }
    }

    #[test]
    fn test_project_all() {
        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);
        let projections = project_all(&g).unwrap();

        assert_eq!(projections.len(), 2);
        let a_proj = projections.iter().find(|(r, _)| r == "A").unwrap();
        let b_proj = projections.iter().find(|(r, _)| r == "B").unwrap();

        assert!(matches!(a_proj.1, LocalTypeR::Send { .. }));
        assert!(matches!(b_proj.1, LocalTypeR::Recv { .. }));
    }

    #[test]
    fn test_project_three_party_merge_sends_different_labels_fails() {
        // A -> B: {l1. C -> B: x. end, l2. C -> B: y. end}
        // From C's perspective, this is INVALID because:
        // - C is not involved in the A->B choice
        // - But C must send different labels (x vs y) depending on that choice
        // - This violates the merge rule: sends must have identical label sets
        //
        // This matches Lean's `mergeSendSorted` semantics.
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (
                    Label::new("l1"),
                    GlobalType::send("C", "B", Label::new("x"), GlobalType::End),
                ),
                (
                    Label::new("l2"),
                    GlobalType::send("C", "B", Label::new("y"), GlobalType::End),
                ),
            ],
        );

        let result = project(&g, "C");
        assert!(
            result.is_err(),
            "Projection should fail: C cannot choose different sends based on unseen choice"
        );
    }

    #[test]
    fn test_project_three_party_merge_sends_same_label_succeeds() {
        // A -> B: {l1. C -> B: msg. end, l2. C -> B: msg. end}
        // From C's perspective, this IS VALID because:
        // - C sends the same message (msg) regardless of which branch was taken
        // - The merge succeeds because both branches have identical label sets
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (
                    Label::new("l1"),
                    GlobalType::send("C", "B", Label::new("msg"), GlobalType::End),
                ),
                (
                    Label::new("l2"),
                    GlobalType::send("C", "B", Label::new("msg"), GlobalType::End),
                ),
            ],
        );

        let c_local = project(&g, "C").unwrap();
        match c_local {
            LocalTypeR::Send { partner, branches } => {
                assert_eq!(partner, "B");
                assert_eq!(branches.len(), 1);
                assert_eq!(branches[0].0.name, "msg");
            }
            _ => panic!("Expected Send"),
        }
    }

    #[test]
    fn test_project_three_party_merge_recvs_different_labels_succeeds() {
        // A -> B: {l1. B -> C: x. end, l2. B -> C: y. end}
        // From C's perspective, this IS VALID because:
        // - C receives from B in both branches
        // - Recv merge unions the label sets: ?B{x.end, y.end}
        //
        // This matches Lean's `mergeRecvSorted` semantics.
        let g = GlobalType::comm(
            "A",
            "B",
            vec![
                (
                    Label::new("l1"),
                    GlobalType::send("B", "C", Label::new("x"), GlobalType::End),
                ),
                (
                    Label::new("l2"),
                    GlobalType::send("B", "C", Label::new("y"), GlobalType::End),
                ),
            ],
        );

        let c_local = project(&g, "C").unwrap();
        match c_local {
            LocalTypeR::Recv { partner, branches } => {
                assert_eq!(partner, "B");
                assert_eq!(branches.len(), 2);
                let labels: Vec<_> = branches.iter().map(|(l, _)| l.name.as_str()).collect();
                assert!(labels.contains(&"x"));
                assert!(labels.contains(&"y"));
            }
            _ => panic!("Expected Recv with merged branches"),
        }
    }

    // ========================================================================
    // MemoizedProjector tests
    // ========================================================================

    #[test]
    fn test_memoized_projector_basic() {
        let mut projector = MemoizedProjector::new();

        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

        // First call (cache miss)
        let a1 = projector.project(&g, "A").unwrap();

        // Second call (cache hit)
        let a2 = projector.project(&g, "A").unwrap();

        assert_eq!(a1, a2);

        let metrics = projector.metrics();
        assert_eq!(metrics.misses, 1);
        assert_eq!(metrics.hits, 1);
    }

    #[test]
    fn test_memoized_projector_alpha_equivalence() {
        let mut projector = MemoizedProjector::new();

        // Two α-equivalent types
        let g1 = GlobalType::mu(
            "x",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("x")),
        );
        let g2 = GlobalType::mu(
            "y",
            GlobalType::send("A", "B", Label::new("msg"), GlobalType::var("y")),
        );

        // First type (miss)
        let result1 = projector.project(&g1, "A").unwrap();

        // α-equivalent type should hit cache
        let result2 = projector.project(&g2, "A").unwrap();

        assert_eq!(result1, result2);

        let metrics = projector.metrics();
        assert_eq!(metrics.misses, 1);
        assert_eq!(metrics.hits, 1);
    }

    #[test]
    fn test_memoized_projector_different_roles() {
        let mut projector = MemoizedProjector::new();

        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

        // Different roles have different projections
        let a_proj = projector.project(&g, "A").unwrap();
        let b_proj = projector.project(&g, "B").unwrap();

        assert!(matches!(a_proj, LocalTypeR::Send { .. }));
        assert!(matches!(b_proj, LocalTypeR::Recv { .. }));

        // Both should be cache misses (different keys)
        let metrics = projector.metrics();
        assert_eq!(metrics.misses, 2);
        assert_eq!(metrics.hits, 0);

        // Now they should both hit
        projector.project(&g, "A").unwrap();
        projector.project(&g, "B").unwrap();

        let metrics = projector.metrics();
        assert_eq!(metrics.hits, 2);
    }

    #[test]
    fn test_memoized_projector_project_all() {
        let mut projector = MemoizedProjector::new();

        let g = GlobalType::send("A", "B", Label::new("msg"), GlobalType::End);

        let projections = projector.project_all(&g).unwrap();
        assert_eq!(projections.len(), 2);

        // Calling again should use cache
        projector.project_all(&g).unwrap();

        let metrics = projector.metrics();
        assert_eq!(metrics.hits, 2);
        assert_eq!(metrics.misses, 2);
    }

    #[test]
    fn test_memoized_projector_clear() {
        let mut projector = MemoizedProjector::new();

        let g = GlobalType::End;
        projector.project(&g, "A").unwrap();
        assert_eq!(projector.cache_size(), 1);

        projector.clear();
        assert_eq!(projector.cache_size(), 0);
    }

    #[test]
    fn test_memoized_projector_error_cached() {
        let mut projector = MemoizedProjector::new();

        // Empty branches cause projection error
        let g = GlobalType::Comm {
            sender: "A".to_string(),
            receiver: "B".to_string(),
            branches: vec![],
        };

        // First call (miss, error)
        let result1 = projector.project(&g, "A");
        assert!(result1.is_err());

        // Second call (hit, same error)
        let result2 = projector.project(&g, "A");
        assert!(result2.is_err());

        let metrics = projector.metrics();
        assert_eq!(metrics.misses, 1);
        assert_eq!(metrics.hits, 1);
    }
}
