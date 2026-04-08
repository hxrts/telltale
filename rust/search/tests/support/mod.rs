#![allow(dead_code, missing_docs)]

use std::collections::BTreeMap;

use telltale_search::SearchDomain;

#[derive(Clone, Debug, Default)]
pub(crate) struct FixtureDomain {
    pub(crate) edges: BTreeMap<u8, Vec<(u8, &'static str, u64)>>,
    pub(crate) heuristics: BTreeMap<(u64, u8), u64>,
    pub(crate) fail_node: Option<u8>,
}

impl SearchDomain for FixtureDomain {
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
        if self.fail_node == Some(*node) {
            return Err("boom");
        }
        if let Some(edges) = self.edges.get(node) {
            out.extend(edges.iter().cloned());
        }
        Ok(())
    }

    fn heuristic(
        &self,
        epoch: &Self::GraphEpoch,
        node: &Self::Node,
        _goal: &Self::Node,
    ) -> Self::Cost {
        *self.heuristics.get(&(*epoch, *node)).unwrap_or(&0)
    }

    fn snapshot_id(&self, epoch: &Self::GraphEpoch) -> Self::SnapshotId {
        if *epoch == 1 {
            "epoch-1"
        } else {
            "epoch-2"
        }
    }
}

impl FixtureDomain {
    pub(crate) fn edge(&mut self, from: u8, to: u8, label: &'static str, cost: u64) {
        self.edges.entry(from).or_default().push((to, label, cost));
    }

    pub(crate) fn heuristic_value(&mut self, epoch: u64, node: u8, value: u64) {
        self.heuristics.insert((epoch, node), value);
    }
}
