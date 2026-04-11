//! Canonical serial search machine and invariant checks.

use std::collections::{BTreeMap, BTreeSet};

use crate::admission::{SearchFairnessAssumption, SearchSchedulerProfile};
use crate::cost::{EpsilonMilli, SearchCost};
use crate::domain::{SearchDomain, SearchQuery};
use crate::observe::{
    IncumbentPublicationRecord, NormalizedCommitRecord, SearchObservationAccumulator,
    SearchObservationArtifact,
};
use crate::runtime::{AuthorityReadSet, AuthorityWriteSet};

type MachineState<D> = SearchState<
    <D as SearchDomain>::Node,
    <D as SearchDomain>::EdgeMeta,
    <D as SearchDomain>::GraphEpoch,
    <D as SearchDomain>::SnapshotId,
    <D as SearchDomain>::Cost,
>;

type MachineBatch<D> = CanonicalBatch<
    <D as SearchDomain>::Node,
    <D as SearchDomain>::GraphEpoch,
    <D as SearchDomain>::SnapshotId,
    <D as SearchDomain>::Cost,
>;

type MachineProposal<D> =
    Proposal<<D as SearchDomain>::Node, <D as SearchDomain>::EdgeMeta, <D as SearchDomain>::Cost>;

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

/// Current best known selected solution.
///
/// For built-in path-search queries, `witness` is the canonical reconstructed
/// path to the currently selected terminal. Domains may override the witness
/// reconstruction policy while still using the same canonical machine.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SelectedSolution<N, C> {
    /// Canonical selected-solution cost.
    pub cost: C,
    /// Canonical selected-solution witness for path-style queries.
    pub witness: Vec<N>,
}

/// Historical incumbent vocabulary retained alongside the generic
/// selected-solution name during migration.
pub type Incumbent<N, C> = SelectedSolution<N, C>;

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
    pub incumbent: Option<SelectedSolution<N, C>>,
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
    pub(crate) query: SearchQuery<D::Node>,
    pub(crate) state: MachineState<D>,
    pub(crate) observation: SearchObservationAccumulator<D::Node, D::GraphEpoch, D::Cost>,
    pub(crate) last_batch: Option<MachineBatch<D>>,
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
        Self::new_with_query(
            domain,
            epoch,
            SearchQuery::single_goal(start, goal),
            epsilon,
        )
    }

    /// Create a new canonical serial search machine for one generalized query.
    #[must_use]
    pub fn new_with_query(
        domain: D,
        epoch: D::GraphEpoch,
        query: SearchQuery<D::Node>,
        epsilon: EpsilonMilli,
    ) -> Self {
        let snapshot_id = domain.snapshot_id(&epoch);
        let start = query.start().clone();
        let goal = query.primary_target().clone();
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
            graph_epoch: epoch.clone(),
            graph_snapshot_id: snapshot_id,
        };
        let start_score = Self::frontier_entry_for(
            &domain,
            &state.graph_epoch,
            &query,
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
            query,
            state,
            observation: SearchObservationAccumulator {
                normalized_commit_trace: Vec::new(),
                replay_checkpoints: Vec::new(),
                graph_epoch_trace: vec![epoch],
                reseed_policy_trace: Vec::new(),
                selected_result_publication_trace: Vec::new(),
            },
            last_batch: None,
        }
    }

    /// Borrow the canonical state.
    #[must_use]
    pub fn state(&self) -> &MachineState<D> {
        &self.state
    }

    /// Borrow the generalized query driving the machine.
    #[must_use]
    pub fn query(&self) -> &SearchQuery<D::Node> {
        &self.query
    }

    /// Borrow the current selected solution, if one has been published.
    #[must_use]
    pub fn selected_solution(&self) -> Option<&SelectedSolution<D::Node, D::Cost>> {
        self.state.incumbent.as_ref()
    }

    /// Borrow the accumulated observation records.
    #[must_use]
    pub(crate) fn observation(
        &self,
    ) -> &SearchObservationAccumulator<D::Node, D::GraphEpoch, D::Cost> {
        &self.observation
    }

    pub(crate) fn observation_mut(
        &mut self,
    ) -> &mut SearchObservationAccumulator<D::Node, D::GraphEpoch, D::Cost> {
        &mut self.observation
    }

    /// Extract the next legal min-key batch from `OPEN`.
    #[must_use]
    pub fn next_batch(&self) -> Option<MachineBatch<D>> {
        let sorted = self.sorted_open_entries();
        let min_score = sorted.first()?.frontier_score;
        let batch_entries = sorted
            .into_iter()
            .take_while(|entry| entry.frontier_score == min_score)
            .collect::<Vec<_>>();

        let batch = CanonicalBatch {
            epoch: self.state.graph_epoch.clone(),
            snapshot_id: self.state.graph_snapshot_id.clone(),
            phase: self.state.phase,
            min_score,
            entries: batch_entries,
        };
        Some(batch)
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

    /// Expand one canonical batch into speculative proposals.
    ///
    /// # Errors
    ///
    /// Returns an error if the domain fails to enumerate successors.
    pub fn expand_batch(
        &self,
        batch: &CanonicalBatch<D::Node, D::GraphEpoch, D::SnapshotId, D::Cost>,
    ) -> Result<Vec<MachineProposal<D>>, SearchError<D::Error>> {
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
    pub fn normalize_proposals(
        &self,
        proposals: &mut Vec<Proposal<D::Node, D::EdgeMeta, D::Cost>>,
    ) {
        let mut best_by_target = BTreeMap::new();
        for proposal in proposals.drain(..) {
            match best_by_target.entry(proposal.to.clone()) {
                std::collections::btree_map::Entry::Vacant(slot) => {
                    slot.insert(proposal);
                }
                std::collections::btree_map::Entry::Occupied(mut slot) => {
                    if Self::canonical_proposal_cmp(&proposal, slot.get()).is_lt() {
                        slot.insert(proposal);
                    }
                }
            }
        }
        *proposals = best_by_target.into_values().collect();
    }

    /// Commit one normalized proposal slice.
    pub fn commit_proposals(
        &mut self,
        proposals: &[Proposal<D::Node, D::EdgeMeta, D::Cost>],
    ) -> bool {
        let mut changed = false;
        let mut goal_changed = false;
        for proposal in proposals {
            if self.proposal_improves_state(proposal) {
                goal_changed |= self.apply_proposal(proposal);
                changed = true;
            }
        }
        if goal_changed {
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
    ///
    /// # Panics
    ///
    /// Panics if the extracted batch entry count does not fit in `u64`.
    pub fn step_once(&mut self) -> Result<bool, SearchError<D::Error>> {
        let Some(batch) = self.next_batch() else {
            return Ok(false);
        };

        let mut proposals = self.expand_batch(&batch)?;
        self.state.trace_state.total_scheduler_steps += 1;
        self.activate_batch(&batch);
        self.normalize_proposals(&mut proposals);
        let changed = self.commit_proposals(&proposals);

        self.state.budget_state.expansions +=
            u64::try_from(batch.entries.len()).expect("batch entry count must fit in u64");
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

    /// Lower epsilon and rebuild the frontier for ARA*-style refinement.
    ///
    /// # Panics
    ///
    /// Panics if `next_epsilon` is greater than the current epsilon.
    pub fn decrease_epsilon_and_rebuild(&mut self, next_epsilon: EpsilonMilli) {
        assert!(
            next_epsilon <= self.state.epsilon,
            "epsilon increases are not legal in canonical refinement"
        );
        if next_epsilon == self.state.epsilon {
            return;
        }
        self.state.phase += 1;
        self.state.epsilon = next_epsilon;
        self.state.closed.clear();

        let rebuild_nodes = self
            .state
            .open
            .keys()
            .cloned()
            .chain(self.state.incons.iter().cloned())
            .collect::<BTreeSet<_>>();
        self.state.open.clear();
        self.state.incons.clear();
        self.last_batch = None;

        for node in rebuild_nodes {
            let g_score = *self
                .state
                .g_score
                .get(&node)
                .expect("rebuild nodes must have canonical g scores");
            let entry = Self::frontier_entry_for(
                &self.domain,
                &self.state.graph_epoch,
                &self.query,
                self.state.epsilon,
                &node,
                g_score,
            );
            self.state.open.insert(node, entry);
        }
    }

    /// Derive one observation artifact from the current canonical machine
    /// state.
    #[must_use]
    pub fn observation_artifact(
        &self,
        scheduler_profile: SearchSchedulerProfile,
        fairness_assumptions: BTreeSet<SearchFairnessAssumption>,
    ) -> SearchObservationArtifact<D::Node, D::GraphEpoch, D::Cost> {
        SearchObservationArtifact {
            selected_result_cost: self
                .state
                .incumbent
                .as_ref()
                .map(|incumbent| incumbent.cost),
            selected_result_witness: self
                .state
                .incumbent
                .as_ref()
                .map(|incumbent| incumbent.witness.clone()),
            canonical_parent_map: self
                .state
                .parent
                .iter()
                .map(|(node, parent)| (node.clone(), parent.from.clone()))
                .collect(),
            selected_result_publication_trace: self
                .observation
                .selected_result_publication_trace
                .clone(),
            normalized_commit_trace: self.observation.normalized_commit_trace.clone(),
            replay_checkpoints: self.observation.replay_checkpoints.clone(),
            graph_epoch_trace: self.observation.graph_epoch_trace.clone(),
            reseed_policy_trace: self.observation.reseed_policy_trace.clone(),
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
                .selected_result_terminal()
                .and_then(|node| self.state.g_score.get(node))
                .ok_or(SearchInvariantViolation::IncumbentMismatch)?;
            let goal_path = self
                .selected_result_terminal()
                .and_then(|node| self.reconstruct_path(node))
                .ok_or(SearchInvariantViolation::IncumbentMismatch)?;
            if incumbent.cost != *goal_cost || incumbent.witness != goal_path {
                return Err(SearchInvariantViolation::IncumbentMismatch);
            }
        }

        if let Some(batch) = &self.last_batch {
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
        query: &SearchQuery<D::Node>,
        epsilon: EpsilonMilli,
        node: &D::Node,
        g_score: D::Cost,
    ) -> FrontierEntry<D::Node, D::Cost> {
        let heuristic = domain.query_heuristic(epoch, node, query);
        FrontierEntry {
            node: node.clone(),
            g_score,
            frontier_score: FrontierScore {
                weighted_f: epsilon.weighted_f(g_score, heuristic),
                g_cost: g_score.order_key(),
            },
        }
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

    fn apply_proposal(&mut self, proposal: &Proposal<D::Node, D::EdgeMeta, D::Cost>) -> bool {
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
                &self.query,
                self.state.epsilon,
                &proposal.to,
                proposal.tentative_g,
            );
            self.state.open.insert(proposal.to.clone(), entry);
        }
        self.observation
            .normalized_commit_trace
            .push(NormalizedCommitRecord {
                node: proposal.to.clone(),
                parent: Some(proposal.from.clone()),
                g_score: proposal.tentative_g,
            });
        self.query.accepts(&proposal.to)
    }

    fn refresh_incumbent(&mut self) {
        let Some((selected_cost, path)) = self.best_selected_solution() else {
            return;
        };
        match &self.state.incumbent {
            None => {
                self.state.incumbent = Some(Incumbent {
                    cost: selected_cost,
                    witness: path.clone(),
                });
                self.observation.selected_result_publication_trace.push(
                    IncumbentPublicationRecord {
                        cost: selected_cost,
                        witness: path,
                    },
                );
            }
            Some(current) if selected_cost < current.cost => {
                self.state.incumbent = Some(SelectedSolution {
                    cost: selected_cost,
                    witness: path.clone(),
                });
                self.observation.selected_result_publication_trace.push(
                    IncumbentPublicationRecord {
                        cost: selected_cost,
                        witness: path,
                    },
                );
            }
            Some(current)
                if self.domain.compare_selected_solutions(
                    selected_cost,
                    &path,
                    current.cost,
                    &current.witness,
                ) == core::cmp::Ordering::Less =>
            {
                self.state.incumbent = Some(SelectedSolution {
                    cost: selected_cost,
                    witness: path.clone(),
                });
                self.observation.selected_result_publication_trace.push(
                    IncumbentPublicationRecord {
                        cost: selected_cost,
                        witness: path,
                    },
                );
            }
            Some(_) => {}
        }
    }

    /// Activate one extracted batch by moving its entries from `OPEN` into the
    /// current phase's closed set.
    pub fn activate_batch(&mut self, batch: &MachineBatch<D>) {
        for entry in &batch.entries {
            self.state.open.remove(&entry.node);
            self.state.closed.insert(entry.node.clone());
        }
        self.last_batch = Some(batch.clone());
    }

    fn selected_result_terminal(&self) -> Option<&D::Node> {
        self.state
            .incumbent
            .as_ref()
            .and_then(|incumbent| incumbent.witness.last())
    }

    fn best_selected_solution(&self) -> Option<(D::Cost, Vec<D::Node>)> {
        self.query
            .accepted_nodes()
            .iter()
            .filter_map(|node| {
                if !self.domain.accepts_terminal(&self.query, node) {
                    return None;
                }
                let cost = self.state.g_score.get(node).copied()?;
                let witness =
                    self.domain
                        .reconstruct_selection_witness(&self.start, node, &|cursor| {
                            self.state
                                .parent
                                .get(cursor)
                                .map(|parent| parent.from.clone())
                        })?;
                Some((cost, witness))
            })
            .min_by(|left, right| {
                self.domain
                    .compare_selected_solutions(left.0, &left.1, right.0, &right.1)
            })
    }

    fn canonical_proposal_cmp(
        left: &Proposal<D::Node, D::EdgeMeta, D::Cost>,
        right: &Proposal<D::Node, D::EdgeMeta, D::Cost>,
    ) -> std::cmp::Ordering {
        left.to
            .cmp(&right.to)
            .then(left.tentative_g.cmp(&right.tentative_g))
            .then(left.from.cmp(&right.from))
            .then(left.batch_index.cmp(&right.batch_index))
            .then(left.kind.cmp(&right.kind))
    }
}
