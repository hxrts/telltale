//! Domain-extension boundary for weighted graph search.

use core::cmp::Ordering;

use serde::{Deserialize, Serialize};

use crate::cost::SearchCost;

/// Generic search query accepted by the search substrate.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum SearchQuery<N> {
    /// Traditional single-goal path search from one start to one goal.
    SingleGoal {
        /// Canonical start node for the query.
        start: N,
        /// Canonical terminal goal node for the query.
        goal: N,
    },
    /// Search from one start to any terminal in a deterministic goal set.
    MultiGoal {
        /// Canonical start node for the query.
        start: N,
        /// Canonical accepted goal set in deterministic order.
        goals: Vec<N>,
    },
    /// Search from one start to a deterministic candidate set.
    ///
    /// The optional heuristic anchor lets downstream callers steer heuristic
    /// evaluation without forcing the selected result to be tied to one
    /// distinguished candidate.
    CandidateSet {
        /// Canonical start node for the query.
        start: N,
        /// Canonical accepted candidate set in deterministic order.
        candidates: Vec<N>,
        /// Optional distinguished anchor for heuristic evaluation.
        heuristic_anchor: Option<N>,
    },
}

impl<N> SearchQuery<N>
where
    N: Clone + Ord,
{
    /// Construct one single-goal query.
    #[must_use]
    pub fn single_goal(start: N, goal: N) -> Self {
        Self::SingleGoal { start, goal }
    }

    /// Construct one normalized multi-goal query.
    ///
    /// # Panics
    ///
    /// Panics if `goals` is empty after canonical deduplication.
    #[must_use]
    pub fn multi_goal(start: N, mut goals: Vec<N>) -> Self {
        goals.sort();
        goals.dedup();
        assert!(
            !goals.is_empty(),
            "multi-goal queries require at least one accepted goal"
        );
        Self::MultiGoal { start, goals }
    }

    /// Construct one normalized candidate-set query.
    ///
    /// # Panics
    ///
    /// Panics if `candidates` is empty after canonical deduplication.
    #[must_use]
    pub fn candidate_set(start: N, mut candidates: Vec<N>, heuristic_anchor: Option<N>) -> Self {
        candidates.sort();
        candidates.dedup();
        assert!(
            !candidates.is_empty(),
            "candidate-set queries require at least one accepted candidate"
        );
        Self::CandidateSet {
            start,
            candidates,
            heuristic_anchor,
        }
    }

    /// Borrow the canonical start node for the query.
    #[must_use]
    pub fn start(&self) -> &N {
        match self {
            Self::SingleGoal { start, .. }
            | Self::MultiGoal { start, .. }
            | Self::CandidateSet { start, .. } => start,
        }
    }

    /// Borrow the accepted terminal set in canonical deterministic order.
    #[must_use]
    pub fn accepted_nodes(&self) -> &[N] {
        match self {
            Self::SingleGoal { goal, .. } => core::slice::from_ref(goal),
            Self::MultiGoal { goals, .. } => goals,
            Self::CandidateSet { candidates, .. } => candidates,
        }
    }

    /// Return whether the provided node satisfies the query's terminal
    /// condition.
    #[must_use]
    pub fn accepts(&self, node: &N) -> bool {
        self.accepted_nodes().binary_search(node).is_ok()
    }

    /// Borrow one deterministic primary target retained for compatibility with
    /// route-oriented artifacts during the migration.
    #[must_use]
    pub fn primary_target(&self) -> &N {
        self.accepted_nodes()
            .first()
            .expect("search queries must have at least one accepted node")
    }

    /// Borrow the optional distinguished heuristic anchor for the query.
    #[must_use]
    pub fn heuristic_anchor(&self) -> Option<&N> {
        match self {
            Self::CandidateSet {
                heuristic_anchor, ..
            } => heuristic_anchor.as_ref(),
            _ => None,
        }
    }
}

/// Reseeding policy applied when the graph epoch changes.
#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum SearchReseedingPolicy {
    /// Clear machine state and reseed only from the canonical start node.
    StartOnly,
    /// Preserve the live open/inconsistent frontier and the parent closure
    /// needed to reconstruct witnesses from those seeds.
    PreserveOpenAndIncons,
}

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

    /// Compute a deterministic heuristic for one node/query pair under one
    /// frozen epoch.
    ///
    /// Domains may override this when their query semantics require something
    /// richer than min-over-target anchors. The default keeps existing
    /// single-goal heuristic behavior and lifts it to multi-goal/candidate-set
    /// queries deterministically.
    fn query_heuristic(
        &self,
        epoch: &Self::GraphEpoch,
        node: &Self::Node,
        query: &SearchQuery<Self::Node>,
    ) -> Self::Cost {
        if let Some(anchor) = query.heuristic_anchor() {
            return self.heuristic(epoch, node, anchor);
        }
        query
            .accepted_nodes()
            .iter()
            .map(|goal| self.heuristic(epoch, node, goal))
            .min()
            .unwrap_or_else(Self::Cost::zero)
    }

    /// Return whether one node satisfies the query's terminal/success
    /// condition under this domain's semantics.
    ///
    /// The default lifts directly from the query object. Domains may override
    /// this to treat the query as a selector seed rather than the full success
    /// definition.
    fn accepts_terminal(&self, query: &SearchQuery<Self::Node>, node: &Self::Node) -> bool {
        query.accepts(node)
    }

    /// Reconstruct the witness exported for one selected solution.
    ///
    /// The default implementation reconstructs one canonical parent chain from
    /// `target` back to `start`, yielding the usual path witness. Domains may
    /// override this to export a different selector witness while still using
    /// the same canonical machine.
    fn reconstruct_selection_witness(
        &self,
        start: &Self::Node,
        target: &Self::Node,
        parent_of: &dyn Fn(&Self::Node) -> Option<Self::Node>,
    ) -> Option<Vec<Self::Node>> {
        let mut witness = vec![target.clone()];
        let mut cursor = target.clone();
        while &cursor != start {
            cursor = parent_of(&cursor)?;
            witness.push(cursor.clone());
        }
        witness.reverse();
        Some(witness)
    }

    /// Compare two selected-solution candidates under this domain's result
    /// semantics.
    ///
    /// The default is "lowest cost, then canonical witness order".
    fn compare_selected_solutions(
        &self,
        left_cost: Self::Cost,
        left_witness: &[Self::Node],
        right_cost: Self::Cost,
        right_witness: &[Self::Node],
    ) -> Ordering {
        left_cost
            .cmp(&right_cost)
            .then_with(|| left_witness.cmp(right_witness))
    }

    /// Return the stable snapshot identity for the provided epoch.
    fn snapshot_id(&self, epoch: &Self::GraphEpoch) -> Self::SnapshotId;
}
