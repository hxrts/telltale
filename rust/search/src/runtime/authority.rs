use std::collections::BTreeSet;

use serde::{Deserialize, Serialize};

use crate::cost::SearchCost;
use crate::domain::{SearchDomain, SearchQuery};
use crate::machine::Proposal;

/// Machine authority surface touched by speculative proposals.
#[derive(Clone, Copy, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub enum AuthoritySurface {
    /// Incumbent publication state.
    Incumbent,
    /// Replay-visible batch descriptor.
    BatchWindow,
    /// Replay-visible phase state.
    Phase,
    /// Replay-visible graph epoch state.
    GraphEpoch,
}

/// Read summary for one proposal.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct AuthorityReadSet<N>
where
    N: Ord,
{
    /// Target nodes read by the proposal.
    pub target_nodes: BTreeSet<N>,
    /// Non-node authority surfaces read by the proposal.
    pub surfaces: BTreeSet<AuthoritySurface>,
}

/// Write summary for one proposal.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub struct AuthorityWriteSet<N>
where
    N: Ord,
{
    /// Target nodes written by the proposal.
    pub target_nodes: BTreeSet<N>,
    /// Non-node authority surfaces written by the proposal.
    pub surfaces: BTreeSet<AuthoritySurface>,
}

impl<N> Default for AuthorityReadSet<N>
where
    N: Ord,
{
    fn default() -> Self {
        Self {
            target_nodes: BTreeSet::new(),
            surfaces: BTreeSet::new(),
        }
    }
}

/// Downstream hook for deriving proposal authority surfaces.
///
/// The generic crate validates independence over these surfaces, but it does
/// not require one hard-coded `(from, to, goal)` interpretation.
pub trait SearchAuthorityPolicy: SearchDomain {
    /// Derive the proposal read surface for one transition under one query.
    #[must_use]
    fn proposal_read_set(
        &self,
        _query: &SearchQuery<Self::Node>,
        from: &Self::Node,
        to: &Self::Node,
    ) -> AuthorityReadSet<Self::Node> {
        default_proposal_read_set(from, to)
    }

    /// Derive the proposal write surface for one transition under one query.
    #[must_use]
    fn proposal_write_set(
        &self,
        query: &SearchQuery<Self::Node>,
        to: &Self::Node,
    ) -> AuthorityWriteSet<Self::Node> {
        default_proposal_write_set(query, to)
    }
}

impl<D: SearchDomain> SearchAuthorityPolicy for D {}

impl<N> Default for AuthorityWriteSet<N>
where
    N: Ord,
{
    fn default() -> Self {
        Self {
            target_nodes: BTreeSet::new(),
            surfaces: BTreeSet::new(),
        }
    }
}

/// Determine whether two proposals are independent on the canonical machine
/// authority surface.
///
/// This relation is intentionally about committed search state only. Replay
/// artifacts such as normalized commit traces are excluded because canonical
/// proposal normalization removes worker-local ordering from the authoritative
/// state transition.
#[must_use]
pub fn proposals_independent<N>(
    left: &Proposal<N, impl Clone, impl SearchCost>,
    right: &Proposal<N, impl Clone, impl SearchCost>,
) -> bool
where
    N: Clone + Ord,
{
    left.write_set
        .target_nodes
        .is_disjoint(&right.write_set.target_nodes)
        && left
            .write_set
            .target_nodes
            .is_disjoint(&right.read_set.target_nodes)
        && right
            .write_set
            .target_nodes
            .is_disjoint(&left.read_set.target_nodes)
        && left
            .write_set
            .surfaces
            .is_disjoint(&right.write_set.surfaces)
        && left
            .write_set
            .surfaces
            .is_disjoint(&right.read_set.surfaces)
        && right
            .write_set
            .surfaces
            .is_disjoint(&left.read_set.surfaces)
}

/// Derive the default proposal read surface used by the built-in runtime.
#[must_use]
pub fn default_proposal_read_set<N>(from: &N, to: &N) -> AuthorityReadSet<N>
where
    N: Clone + Ord,
{
    let mut target_nodes = BTreeSet::new();
    target_nodes.insert(from.clone());
    target_nodes.insert(to.clone());
    let mut surfaces = BTreeSet::new();
    surfaces.insert(AuthoritySurface::BatchWindow);
    surfaces.insert(AuthoritySurface::GraphEpoch);
    surfaces.insert(AuthoritySurface::Phase);
    AuthorityReadSet {
        target_nodes,
        surfaces,
    }
}

/// Derive the default proposal write surface used by the built-in runtime.
#[must_use]
pub fn default_proposal_write_set<N>(query: &SearchQuery<N>, to: &N) -> AuthorityWriteSet<N>
where
    N: Clone + Ord,
{
    let mut target_nodes = BTreeSet::new();
    target_nodes.insert(to.clone());
    let mut surfaces = BTreeSet::new();
    if query.accepts(to) {
        surfaces.insert(AuthoritySurface::Incumbent);
    }
    AuthorityWriteSet {
        target_nodes,
        surfaces,
    }
}
