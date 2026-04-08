//! Domain-extension boundary for weighted graph search.

use crate::cost::SearchCost;

/// Domain behavior required by the canonical search machine.
pub trait SearchDomain {
    /// Canonically ordered node identifier.
    type Node: Clone + Ord + Send + Sync + core::fmt::Debug + 'static;
    /// Edge metadata retained for reconstruction and diagnostics.
    type EdgeMeta: Clone + Send + Sync + core::fmt::Debug + 'static;
    /// Search-cost domain.
    type Cost: SearchCost;
    /// Frozen graph epoch identifier.
    type GraphEpoch: Clone + Ord + Send + Sync + core::fmt::Debug + 'static;
    /// Stable snapshot identifier derived from one epoch.
    type SnapshotId: Clone + Ord + Send + Sync + core::fmt::Debug + 'static;
    /// Domain evaluation error.
    type Error;

    /// Enumerate deterministic successors for one node under one frozen epoch.
    ///
    /// # Errors
    ///
    /// Returns an error if successor enumeration fails for the provided epoch
    /// and node.
    fn successors(
        &self,
        epoch: &Self::GraphEpoch,
        node: &Self::Node,
        out: &mut Vec<(Self::Node, Self::EdgeMeta, Self::Cost)>,
    ) -> Result<(), Self::Error>;

    /// Compute a deterministic heuristic for one node/goal pair under one
    /// frozen epoch.
    fn heuristic(
        &self,
        epoch: &Self::GraphEpoch,
        node: &Self::Node,
        goal: &Self::Node,
    ) -> Self::Cost;

    /// Return the stable snapshot identity for the provided epoch.
    fn snapshot_id(&self, epoch: &Self::GraphEpoch) -> Self::SnapshotId;
}
