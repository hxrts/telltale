//! Canonical serial search machine and invariant checks.

use std::collections::{BTreeMap, BTreeSet};

use crate::admission::{SearchFairnessAssumption, SearchSchedulerProfile};
use crate::cost::{EpsilonMilli, SearchCost};
use crate::domain::SearchDomain;
use crate::observe::{NormalizedCommitRecord, SearchObservationArtifact};
use crate::runtime::{AuthorityReadSet, AuthorityWriteSet};

/// Stable ordering key for one frontier entry.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FrontierScore {
    /// Weighted `f` score.
    pub weighted_f: u128,
    /// Canonical `g` ordering component.
    pub g_cost: u128,
}

/// One canonical frontier entry.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FrontierEntry<N, C> {
    /// Target node.
    pub node: N,
    /// Canonical `g` score.
    pub g_score: C,
    /// Cached canonical frontier score.
    pub frontier_score: FrontierScore,
}

/// One extracted batch from the frozen `OPEN` frontier.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CanonicalBatch<N, G, S, C> {
    /// Frozen graph epoch for this batch.
    pub epoch: G,
    /// Frozen snapshot identity for this batch.
    pub snapshot_id: S,
    /// Search phase identifier.
    pub phase: u64,
    /// Minimum frontier score of the batch window.
    pub min_score: FrontierScore,
    /// Extracted frontier entries.
    pub entries: Vec<FrontierEntry<N, C>>,
}

/// Summary of machine-visible budget/accounting state.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SearchBudgetState {
    /// Number of expanded frontier entries.
    pub expansions: u64,
    /// Number of extracted canonical batches.
    pub batches: u64,
}

/// Summary of exact progress versus scheduler effort.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SearchTraceState {
    /// Canonical commit steps that changed search-visible state.
    pub productive_steps: u64,
    /// Total host-loop step attempts.
    pub total_scheduler_steps: u64,
}

/// Parent witness used for reconstruction and parent-score coherence checks.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParentRecord<N, E, C> {
    /// Canonical parent node.
    pub from: N,
    /// Edge metadata from parent to child.
    pub edge: E,
    /// Edge cost from parent to child.
    pub edge_cost: C,
}

/// Current best known goal solution.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Incumbent<N, C> {
    /// Canonical goal cost.
    pub cost: C,
    /// Canonical reconstructed path.
    pub path: Vec<N>,
}

/// Proposal kind emitted by expansion work.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ProposalKind {
    /// Standard relaxation proposal.
    Relax,
}

/// One speculative proposal normalized and committed by the canonical machine.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Proposal<N: Ord, E, C> {
    /// Index of the originating entry within the canonical batch.
    pub batch_index: usize,
    /// Source node.
    pub from: N,
    /// Target node.
    pub to: N,
    /// Edge metadata.
    pub edge: E,
    /// Cost of the proposed edge traversal.
    pub edge_cost: C,
    /// Candidate resulting `g` score.
    pub tentative_g: C,
    /// Proposal class.
    pub kind: ProposalKind,
    /// Authority surfaces read by the proposal.
    pub read_set: AuthorityReadSet<N>,
    /// Authority surfaces written by the proposal.
    pub write_set: AuthorityWriteSet<N>,
}

/// Canonical state owned by the search machine.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SearchState<N, E, G, S, C> {
    /// Frontier entries indexed by node.
    pub open: BTreeMap<N, FrontierEntry<N, C>>,
    /// Closed nodes for the active phase.
    pub closed: BTreeSet<N>,
    /// Improved closed nodes awaiting future rebuild handling.
    pub incons: BTreeSet<N>,
    /// Best-known path cost by node.
    pub g_score: BTreeMap<N, C>,
    /// Canonical parent relation for non-start nodes.
    pub parent: BTreeMap<N, ParentRecord<N, E, C>>,
    /// Current incumbent solution.
    pub incumbent: Option<Incumbent<N, C>>,
    /// Current epsilon.
    pub epsilon: EpsilonMilli,
    /// Current search phase.
    pub phase: u64,
    /// Budget/accounting summary.
    pub budget_state: SearchBudgetState,
    /// Trace/accounting summary.
    pub trace_state: SearchTraceState,
    /// Frozen graph epoch.
    pub graph_epoch: G,
    /// Frozen snapshot identity.
    pub graph_snapshot_id: S,
    /// Last extracted canonical batch.
    pub last_batch: Option<CanonicalBatch<N, G, S, C>>,
    /// Canonical normalized commit trace for the current run.
    pub normalized_commit_trace: Vec<NormalizedCommitRecord<N, C>>,
    /// Graph epoch trace for the current run.
    pub graph_epoch_trace: Vec<G>,
}

/// Invariant violation raised by the canonical machine.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SearchInvariantViolation {
    /// A node appeared in both `OPEN` and `CLOSED`.
    OpenClosedOverlap,
    /// A node appeared in `INCONS` without already being closed.
    InconsNotClosed,
    /// The recorded parent relation does not agree with stored path costs.
    ParentScoreMismatch,
    /// The incumbent does not match canonical reconstruction from the parent
    /// relation.
    IncumbentMismatch,
    /// The last extracted batch violated min-key window legality.
    IllegalBatchWindow,
}

/// Search-machine error surface.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SearchError<E> {
    /// Domain evaluation error.
    Domain(E),
    /// Canonical invariant violation.
    InvariantViolation(SearchInvariantViolation),
}

/// Deterministic serial search machine over one frozen graph epoch.
pub struct SearchMachine<D: SearchDomain> {
    pub(crate) domain: D,
    pub(crate) start: D::Node,
    pub(crate) goal: D::Node,
    pub(crate) state: SearchState<D::Node, D::EdgeMeta, D::GraphEpoch, D::SnapshotId, D::Cost>,
}

impl<D: SearchDomain> SearchMachine<D> {
    /// Create a new canonical serial search machine.
    #[must_use]
    pub fn new(
        domain: D,
        epoch: D::GraphEpoch,
        start: D::Node,
        goal: D::Node,
        epsilon: EpsilonMilli,
    ) -> Self {
        let snapshot_id = domain.snapshot_id(&epoch);
        let mut state = SearchState {
            open: BTreeMap::new(),
            closed: BTreeSet::new(),
            incons: BTreeSet::new(),
            g_score: BTreeMap::new(),
            parent: BTreeMap::new(),
            incumbent: None,
            epsilon,
            phase: 0,
            budget_state: SearchBudgetState::default(),
            trace_state: SearchTraceState::default(),
            graph_epoch: epoch,
            graph_snapshot_id: snapshot_id,
            last_batch: None,
            normalized_commit_trace: Vec::new(),
            graph_epoch_trace: Vec::new(),
        };
        state.graph_epoch_trace.push(state.graph_epoch.clone());
        let start_score = Self::frontier_entry_for(
            &domain,
            &state.graph_epoch,
            &goal,
            epsilon,
            &start,
            D::Cost::zero(),
        );
        state.g_score.insert(start.clone(), D::Cost::zero());
        state.open.insert(start.clone(), start_score);
        Self {
            domain,
            start,
            goal,
            state,
        }
    }

    /// Borrow the canonical state.
    #[must_use]
    pub fn state(
        &self,
    ) -> &SearchState<D::Node, D::EdgeMeta, D::GraphEpoch, D::SnapshotId, D::Cost> {
        &self.state
    }

    /// Extract the next legal min-key batch from `OPEN`.
    #[must_use]
    pub fn next_batch(
        &mut self,
    ) -> Option<CanonicalBatch<D::Node, D::GraphEpoch, D::SnapshotId, D::Cost>> {
        let sorted = self.sorted_open_entries();
        let min_score = sorted.first()?.frontier_score;
        let batch_entries = sorted
            .into_iter()
            .take_while(|entry| entry.frontier_score == min_score)
            .collect::<Vec<_>>();

        for entry in &batch_entries {
            self.state.open.remove(&entry.node);
            self.state.closed.insert(entry.node.clone());
        }

        let batch = CanonicalBatch {
            epoch: self.state.graph_epoch.clone(),
            snapshot_id: self.state.graph_snapshot_id.clone(),
            phase: self.state.phase,
            min_score,
            entries: batch_entries,
        };
        self.state.last_batch = Some(batch.clone());
        Some(batch)
    }

    /// Expand one canonical batch into speculative proposals.
    ///
    /// # Errors
    ///
    /// Returns an error if the domain fails to enumerate successors.
    pub fn expand_batch(
        &self,
        batch: &CanonicalBatch<D::Node, D::GraphEpoch, D::SnapshotId, D::Cost>,
    ) -> Result<Vec<Proposal<D::Node, D::EdgeMeta, D::Cost>>, SearchError<D::Error>> {
        let mut proposals = Vec::new();
        for (batch_index, entry) in batch.entries.iter().enumerate() {
            let mut successors = Vec::new();
            self.domain
                .successors(&batch.epoch, &entry.node, &mut successors)
                .map_err(SearchError::Domain)?;
            successors.sort_by(|left, right| left.0.cmp(&right.0));
            for (to, edge, edge_cost) in successors {
                proposals.push(Proposal {
                    batch_index,
                    from: entry.node.clone(),
                    to,
                    edge,
                    edge_cost,
                    tentative_g: entry.g_score.saturating_add(edge_cost),
                    kind: ProposalKind::Relax,
                    read_set: AuthorityReadSet::default(),
                    write_set: AuthorityWriteSet::default(),
                });
            }
        }
        Ok(proposals)
    }

    /// Normalize proposals into canonical commit order.
    pub fn normalize_proposals(&self, proposals: &mut [Proposal<D::Node, D::EdgeMeta, D::Cost>]) {
        proposals.sort_by(|left, right| {
            left.to
                .cmp(&right.to)
                .then(left.tentative_g.cmp(&right.tentative_g))
                .then(left.from.cmp(&right.from))
                .then(left.batch_index.cmp(&right.batch_index))
                .then(left.kind.cmp(&right.kind))
        });
    }

    /// Commit one normalized proposal slice.
    pub fn commit_proposals(
        &mut self,
        proposals: &[Proposal<D::Node, D::EdgeMeta, D::Cost>],
    ) -> bool {
        let mut changed = false;
        for proposal in proposals {
            if self.proposal_improves_state(proposal) {
                self.apply_proposal(proposal);
                changed = true;
            }
        }
        if changed {
            self.refresh_incumbent();
        }
        changed
    }

    /// Execute one canonical serial step.
    ///
    /// # Errors
    ///
    /// Returns an error if domain evaluation fails or if one canonical
    /// invariant is violated after the step.
    pub fn step_once(&mut self) -> Result<bool, SearchError<D::Error>> {
        let Some(batch) = self.next_batch() else {
            return Ok(false);
        };
        self.state.trace_state.total_scheduler_steps += 1;

        let mut proposals = self.expand_batch(&batch)?;
        self.normalize_proposals(&mut proposals);
        let changed = self.commit_proposals(&proposals);

        self.state.budget_state.expansions += batch.entries.len() as u64;
        self.state.budget_state.batches += 1;
        if changed {
            self.state.trace_state.productive_steps += 1;
        }

        self.check_invariants()
            .map_err(SearchError::InvariantViolation)?;
        Ok(true)
    }

    /// Run until the frontier becomes empty.
    ///
    /// # Errors
    ///
    /// Returns an error if domain evaluation fails or if one canonical
    /// invariant is violated.
    pub fn run_to_completion(&mut self) -> Result<(), SearchError<D::Error>> {
        while self.step_once()? {}
        Ok(())
    }

    /// Derive one observation artifact from the current canonical machine
    /// state.
    #[must_use]
    pub fn observation_artifact(
        &self,
        scheduler_profile: SearchSchedulerProfile,
        fairness_assumptions: Vec<SearchFairnessAssumption>,
    ) -> SearchObservationArtifact<D::Node, D::GraphEpoch, D::Cost> {
        SearchObservationArtifact {
            incumbent_cost: self
                .state
                .incumbent
                .as_ref()
                .map(|incumbent| incumbent.cost),
            incumbent_path: self
                .state
                .incumbent
                .as_ref()
                .map(|incumbent| incumbent.path.clone()),
            normalized_commit_trace: self.state.normalized_commit_trace.clone(),
            replay_checkpoints: Vec::new(),
            graph_epoch_trace: self.state.graph_epoch_trace.clone(),
            scheduler_profile,
            fairness_assumptions,
            productive_steps: self.state.trace_state.productive_steps,
            total_scheduler_steps: self.state.trace_state.total_scheduler_steps,
        }
    }

    /// Reconstruct one canonical path from the start node to the target node.
    #[must_use]
    pub fn reconstruct_path(&self, target: &D::Node) -> Option<Vec<D::Node>> {
        let _ = self.state.g_score.get(target)?;
        let mut path = vec![target.clone()];
        let mut cursor = target.clone();
        while cursor != self.start {
            let parent = self.state.parent.get(&cursor)?;
            cursor = parent.from.clone();
            path.push(cursor.clone());
        }
        path.reverse();
        Some(path)
    }

    /// Check the explicit canonical invariant set.
    ///
    /// # Errors
    ///
    /// Returns an invariant violation if the canonical state is inconsistent.
    pub fn check_invariants(&self) -> Result<(), SearchInvariantViolation> {
        if self
            .state
            .open
            .keys()
            .any(|node| self.state.closed.contains(node))
        {
            return Err(SearchInvariantViolation::OpenClosedOverlap);
        }

        if self
            .state
            .incons
            .iter()
            .any(|node| !self.state.closed.contains(node))
        {
            return Err(SearchInvariantViolation::InconsNotClosed);
        }

        for (node, parent) in &self.state.parent {
            let from_cost = self
                .state
                .g_score
                .get(&parent.from)
                .ok_or(SearchInvariantViolation::ParentScoreMismatch)?;
            let expected = from_cost.saturating_add(parent.edge_cost);
            let actual = self
                .state
                .g_score
                .get(node)
                .ok_or(SearchInvariantViolation::ParentScoreMismatch)?;
            if expected != *actual {
                return Err(SearchInvariantViolation::ParentScoreMismatch);
            }
        }

        if let Some(incumbent) = &self.state.incumbent {
            let goal_cost = self
                .state
                .g_score
                .get(&self.goal)
                .ok_or(SearchInvariantViolation::IncumbentMismatch)?;
            let goal_path = self
                .reconstruct_path(&self.goal)
                .ok_or(SearchInvariantViolation::IncumbentMismatch)?;
            if incumbent.cost != *goal_cost || incumbent.path != goal_path {
                return Err(SearchInvariantViolation::IncumbentMismatch);
            }
        }

        if let Some(batch) = &self.state.last_batch {
            let all_same_min_key = batch
                .entries
                .iter()
                .all(|entry| entry.frontier_score == batch.min_score);
            if !all_same_min_key || batch.epoch != self.state.graph_epoch {
                return Err(SearchInvariantViolation::IllegalBatchWindow);
            }
        }

        Ok(())
    }

    pub(crate) fn frontier_entry_for(
        domain: &D,
        epoch: &D::GraphEpoch,
        goal: &D::Node,
        epsilon: EpsilonMilli,
        node: &D::Node,
        g_score: D::Cost,
    ) -> FrontierEntry<D::Node, D::Cost> {
        let heuristic = domain.heuristic(epoch, node, goal);
        FrontierEntry {
            node: node.clone(),
            g_score,
            frontier_score: FrontierScore {
                weighted_f: epsilon.weighted_f(g_score, heuristic),
                g_cost: g_score.order_key(),
            },
        }
    }

    fn sorted_open_entries(&self) -> Vec<FrontierEntry<D::Node, D::Cost>> {
        let mut entries = self.state.open.values().cloned().collect::<Vec<_>>();
        entries.sort_by(|left, right| {
            left.frontier_score
                .cmp(&right.frontier_score)
                .then(left.node.cmp(&right.node))
        });
        entries
    }

    fn proposal_improves_state(&self, proposal: &Proposal<D::Node, D::EdgeMeta, D::Cost>) -> bool {
        match self.state.g_score.get(&proposal.to).copied() {
            None => true,
            Some(current) if proposal.tentative_g < current => true,
            Some(current) if proposal.tentative_g == current => {
                self.equal_cost_parent_better(proposal)
            }
            Some(_) => false,
        }
    }

    fn equal_cost_parent_better(&self, proposal: &Proposal<D::Node, D::EdgeMeta, D::Cost>) -> bool {
        self.state
            .parent
            .get(&proposal.to)
            .is_some_and(|current| proposal.from < current.from)
    }

    fn apply_proposal(&mut self, proposal: &Proposal<D::Node, D::EdgeMeta, D::Cost>) {
        self.state
            .g_score
            .insert(proposal.to.clone(), proposal.tentative_g);
        self.state.parent.insert(
            proposal.to.clone(),
            ParentRecord {
                from: proposal.from.clone(),
                edge: proposal.edge.clone(),
                edge_cost: proposal.edge_cost,
            },
        );

        if self.state.closed.contains(&proposal.to) {
            self.state.incons.insert(proposal.to.clone());
            self.state.open.remove(&proposal.to);
        } else {
            self.state.incons.remove(&proposal.to);
            let entry = Self::frontier_entry_for(
                &self.domain,
                &self.state.graph_epoch,
                &self.goal,
                self.state.epsilon,
                &proposal.to,
                proposal.tentative_g,
            );
            self.state.open.insert(proposal.to.clone(), entry);
        }
        self.state
            .normalized_commit_trace
            .push(NormalizedCommitRecord {
                node: proposal.to.clone(),
                g_score: proposal.tentative_g,
            });
    }

    fn refresh_incumbent(&mut self) {
        let Some(goal_cost) = self.state.g_score.get(&self.goal).copied() else {
            return;
        };
        let Some(path) = self.reconstruct_path(&self.goal) else {
            return;
        };
        match &self.state.incumbent {
            None => {
                self.state.incumbent = Some(Incumbent {
                    cost: goal_cost,
                    path,
                })
            }
            Some(current) if goal_cost < current.cost => {
                self.state.incumbent = Some(Incumbent {
                    cost: goal_cost,
                    path,
                });
            }
            Some(current) if goal_cost == current.cost && path < current.path => {
                self.state.incumbent = Some(Incumbent {
                    cost: goal_cost,
                    path,
                });
            }
            Some(_) => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone, Debug, Default)]
    struct TestDomain {
        edges: BTreeMap<u8, Vec<(u8, &'static str, u64)>>,
        heuristics: BTreeMap<u8, u64>,
    }

    impl SearchDomain for TestDomain {
        type Node = u8;
        type EdgeMeta = &'static str;
        type Cost = u64;
        type GraphEpoch = u64;
        type SnapshotId = &'static str;
        type Error = &'static str;

        fn successors(
            &self,
            _epoch: &Self::GraphEpoch,
            node: &Self::Node,
            out: &mut Vec<(Self::Node, Self::EdgeMeta, Self::Cost)>,
        ) -> Result<(), Self::Error> {
            if let Some(edges) = self.edges.get(node) {
                out.extend(edges.iter().cloned());
            }
            Ok(())
        }

        fn heuristic(
            &self,
            _epoch: &Self::GraphEpoch,
            node: &Self::Node,
            _goal: &Self::Node,
        ) -> Self::Cost {
            *self.heuristics.get(node).unwrap_or(&0)
        }

        fn snapshot_id(&self, _epoch: &Self::GraphEpoch) -> Self::SnapshotId {
            "epoch-1"
        }
    }

    fn make_domain(edges: &[(u8, u8, &'static str, u64)], heuristics: &[(u8, u64)]) -> TestDomain {
        let mut domain = TestDomain::default();
        for (from, to, edge, cost) in edges {
            domain
                .edges
                .entry(*from)
                .or_default()
                .push((*to, *edge, *cost));
        }
        for (node, heuristic) in heuristics {
            domain.heuristics.insert(*node, *heuristic);
        }
        domain
    }

    #[test]
    fn canonical_batch_extracts_only_min_key_window() {
        let domain = make_domain(&[(0, 1, "0-1", 1), (0, 2, "0-2", 1), (0, 3, "0-3", 3)], &[]);
        let mut machine = SearchMachine::new(domain, 1, 0, 9, EpsilonMilli::one());
        assert!(machine.step_once().expect("step from start"));
        let batch = machine.next_batch().expect("min-key batch");
        let nodes = batch
            .entries
            .iter()
            .map(|entry| entry.node)
            .collect::<Vec<_>>();
        assert_eq!(nodes, vec![1, 2]);
    }

    #[test]
    fn canonical_parent_tie_break_prefers_lower_source_node() {
        let domain = make_domain(
            &[
                (0, 1, "0-1", 1),
                (0, 2, "0-2", 1),
                (1, 3, "1-3", 1),
                (2, 3, "2-3", 1),
            ],
            &[],
        );
        let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
        machine.run_to_completion().expect("run to completion");
        let path = machine.reconstruct_path(&3).expect("path to goal");
        assert_eq!(path, vec![0, 1, 3]);
        let parent = machine.state.parent.get(&3).expect("goal parent");
        assert_eq!(parent.from, 1);
    }

    #[test]
    fn incumbent_tracks_canonical_reconstruction() {
        let domain = make_domain(
            &[
                (0, 1, "0-1", 1),
                (1, 3, "1-3", 1),
                (0, 2, "0-2", 5),
                (2, 3, "2-3", 1),
            ],
            &[],
        );
        let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli::one());
        machine.run_to_completion().expect("run to completion");
        let incumbent = machine.state.incumbent.as_ref().expect("incumbent");
        assert_eq!(incumbent.cost, 2);
        assert_eq!(incumbent.path, vec![0, 1, 3]);
    }

    #[test]
    fn invariants_hold_after_each_serial_step() {
        let domain = make_domain(
            &[
                (0, 1, "0-1", 1),
                (0, 2, "0-2", 2),
                (1, 3, "1-3", 2),
                (2, 3, "2-3", 1),
                (3, 4, "3-4", 1),
            ],
            &[(1, 1), (2, 0), (3, 0)],
        );
        let mut machine = SearchMachine::new(domain, 1, 0, 4, EpsilonMilli(2_000));
        while machine.step_once().expect("serial step") {
            machine.check_invariants().expect("invariants hold");
        }
    }

    #[test]
    fn observation_artifact_reflects_canonical_state() {
        let domain = make_domain(&[(0, 1, "0-1", 1), (1, 2, "1-2", 1)], &[]);
        let mut machine = SearchMachine::new(domain, 7, 0, 2, EpsilonMilli::one());
        machine.run_to_completion().expect("run to completion");
        let artifact = machine.observation_artifact(
            SearchSchedulerProfile::CanonicalSerial,
            vec![SearchFairnessAssumption::DeterministicSchedulerConfluence],
        );
        assert_eq!(artifact.incumbent_cost, Some(2));
        assert_eq!(artifact.incumbent_path, Some(vec![0, 1, 2]));
        assert_eq!(artifact.graph_epoch_trace, vec![7]);
        assert_eq!(artifact.productive_steps, 2);
        assert_eq!(artifact.total_scheduler_steps, 3);
    }
}
