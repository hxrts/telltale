use std::num::{NonZeroU64, NonZeroUsize};

#[cfg(feature = "multi-thread")]
use rayon::prelude::*;

use crate::cost::SearchCost;
use crate::domain::SearchDomain;
use crate::machine::{CanonicalBatch, Proposal, ProposalKind};

use super::authority::{proposal_read_set, proposal_write_set};

type RuntimeProposalVec<D> = Vec<
    Proposal<<D as SearchDomain>::Node, <D as SearchDomain>::EdgeMeta, <D as SearchDomain>::Cost>,
>;

/// Runtime executor for speculative proposal generation.
pub trait ProposalExecutor<D: SearchDomain> {
    /// Generate speculative proposals for one frozen batch.
    ///
    /// # Errors
    ///
    /// Returns an error if the domain fails during successor enumeration.
    fn generate(
        &self,
        domain: &D,
        batch: &CanonicalBatch<D::Node, D::GraphEpoch, D::SnapshotId, D::Cost>,
        goal: &D::Node,
    ) -> Result<RuntimeProposalVec<D>, D::Error>;
}

/// Serial executor over a canonical batch.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SerialProposalExecutor;

impl<D: SearchDomain> ProposalExecutor<D> for SerialProposalExecutor {
    fn generate(
        &self,
        domain: &D,
        batch: &CanonicalBatch<D::Node, D::GraphEpoch, D::SnapshotId, D::Cost>,
        goal: &D::Node,
    ) -> Result<RuntimeProposalVec<D>, D::Error> {
        let mut proposals = Vec::new();
        for (batch_index, entry) in batch.entries.iter().enumerate() {
            let mut successors = Vec::new();
            domain.successors(&batch.epoch, &entry.node, &mut successors)?;
            successors.sort_by(|left, right| left.0.cmp(&right.0));
            for (to, edge, edge_cost) in successors {
                proposals.push(Proposal {
                    batch_index,
                    from: entry.node.clone(),
                    to: to.clone(),
                    edge,
                    edge_cost,
                    tentative_g: entry.g_score.saturating_add(edge_cost),
                    kind: ProposalKind::Relax,
                    read_set: proposal_read_set(&entry.node, &to),
                    write_set: proposal_write_set(&to, goal),
                });
            }
        }
        let _ = goal;
        Ok(proposals)
    }
}

/// Native parallel executor over a canonical batch.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NativeParallelExecutor {
    batch_width: NonZeroU64,
    chunk_size: NonZeroUsize,
}

/// Native parallel executor construction error.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NativeParallelExecutorError {
    /// The configured batch width does not fit on the current platform.
    BatchWidthOverflow(u64),
    /// The current build does not include native multi-thread support.
    MissingMultiThreadFeature,
}

impl NativeParallelExecutor {
    /// Create one native parallel executor with an explicit non-zero batch width.
    ///
    /// # Errors
    ///
    /// Returns an error if the requested width does not fit on the current
    /// platform.
    #[cfg(feature = "multi-thread")]
    pub fn new(batch_width: NonZeroU64) -> Result<Self, NativeParallelExecutorError> {
        let chunk_size = usize::try_from(batch_width.get())
            .ok()
            .and_then(NonZeroUsize::new)
            .ok_or(NativeParallelExecutorError::BatchWidthOverflow(
                batch_width.get(),
            ))?;
        Ok(Self {
            batch_width,
            chunk_size,
        })
    }

    /// Create one native parallel executor with an explicit non-zero batch width.
    ///
    /// # Errors
    ///
    /// Returns an error when the current build omits native multi-thread
    /// support.
    #[cfg(not(feature = "multi-thread"))]
    pub fn new(batch_width: NonZeroU64) -> Result<Self, NativeParallelExecutorError> {
        let _ = batch_width;
        Err(NativeParallelExecutorError::MissingMultiThreadFeature)
    }

    /// Report the configured batch width.
    #[must_use]
    pub fn batch_width(&self) -> u64 {
        self.batch_width.get()
    }
}

#[cfg(feature = "multi-thread")]
impl<D> ProposalExecutor<D> for NativeParallelExecutor
where
    D: SearchDomain + Sync,
    D::Node: Sync,
    D::EdgeMeta: Send,
    D::GraphEpoch: Sync,
    D::Error: Send,
{
    fn generate(
        &self,
        domain: &D,
        batch: &CanonicalBatch<D::Node, D::GraphEpoch, D::SnapshotId, D::Cost>,
        goal: &D::Node,
    ) -> Result<RuntimeProposalVec<D>, D::Error> {
        let _ = goal;
        let indexed_entries = batch
            .entries
            .iter()
            .cloned()
            .enumerate()
            .collect::<Vec<_>>();
        let mut results = indexed_entries
            .par_chunks(self.chunk_size.get())
            .map(|chunk| {
                let mut proposals = Vec::new();
                for (batch_index, entry) in chunk {
                    let mut successors = Vec::new();
                    domain.successors(&batch.epoch, &entry.node, &mut successors)?;
                    successors.sort_by(|left, right| left.0.cmp(&right.0));
                    proposals.extend(successors.into_iter().map(|(to, edge, edge_cost)| {
                        Proposal {
                            batch_index: *batch_index,
                            from: entry.node.clone(),
                            to: to.clone(),
                            edge,
                            edge_cost,
                            tentative_g: entry.g_score.saturating_add(edge_cost),
                            kind: ProposalKind::Relax,
                            read_set: proposal_read_set(&entry.node, &to),
                            write_set: proposal_write_set(&to, goal),
                        }
                    }));
                }
                Ok::<_, D::Error>(proposals)
            })
            .collect::<Vec<_>>();

        let mut proposals = Vec::new();
        for result in results.drain(..) {
            proposals.extend(result?);
        }
        Ok(proposals)
    }
}

#[cfg(not(feature = "multi-thread"))]
impl<D: SearchDomain> ProposalExecutor<D> for NativeParallelExecutor {
    fn generate(
        &self,
        domain: &D,
        batch: &CanonicalBatch<D::Node, D::GraphEpoch, D::SnapshotId, D::Cost>,
        goal: &D::Node,
    ) -> Result<RuntimeProposalVec<D>, D::Error> {
        let _ = (domain, batch, goal);
        panic!("NativeParallelExecutor requires the `multi-thread` feature");
    }
}
