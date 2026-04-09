#![allow(missing_docs)]

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use telltale_search::{
    run_with_executor, EpsilonMilli, SearchDomain, SearchFairnessAssumption, SearchMachine,
    SearchRunConfig, SearchSchedulerProfile, SerialProposalExecutor,
};

use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Default)]
struct BenchDomain {
    edges: BTreeMap<u32, Vec<(u32, &'static str, u64)>>,
}

impl SearchDomain for BenchDomain {
    type Node = u32;
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
        _node: &Self::Node,
        _goal: &Self::Node,
    ) -> Self::Cost {
        0
    }

    fn snapshot_id(&self, _epoch: &Self::GraphEpoch) -> Self::SnapshotId {
        "bench-epoch"
    }
}

fn chain_domain(length: u32) -> BenchDomain {
    let mut domain = BenchDomain::default();
    for node in 0..length {
        domain
            .edges
            .entry(node)
            .or_default()
            .push((node + 1, "chain", 1));
    }
    domain
}

fn fan_in_domain(width: u32) -> BenchDomain {
    let mut domain = BenchDomain::default();
    for node in 1..=width {
        domain.edges.entry(0).or_default().push((node, "fan", 1));
        domain
            .edges
            .entry(node)
            .or_default()
            .push((width + 1, "goal", u64::from(node)));
    }
    domain
}

fn run_serial(domain: BenchDomain, start: u32, goal: u32) {
    let mut machine = SearchMachine::new(domain, 1, start, goal, EpsilonMilli::one());
    let _ = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        SearchRunConfig {
            scheduler_profile: SearchSchedulerProfile::CanonicalSerial,
            batch_width: 1,
            fairness_assumptions: BTreeSet::from([
                SearchFairnessAssumption::DeterministicSchedulerConfluence,
            ]),
        },
    )
    .expect("benchmark search run");
}

fn criterion_benchmark(c: &mut Criterion) {
    c.bench_function("serial_chain_256", |b| {
        b.iter(|| run_serial(black_box(chain_domain(256)), 0, 256))
    });
    c.bench_function("serial_fan_in_128", |b| {
        b.iter(|| run_serial(black_box(fan_in_domain(128)), 0, 129))
    });
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
