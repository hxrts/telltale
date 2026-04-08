//! Reduced Rust/Lean parity checks for `telltale-search`.
#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::expect_used)]

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde::Deserialize;
use telltale_search::{
    commit_epoch_reconfiguration, proposals_independent, replay_observation, run_with_executor,
    AuthorityReadSet, AuthoritySurface, AuthorityWriteSet, EpochReconfigurationRequest,
    EpsilonMilli, Proposal, ProposalKind, ReplayExpectation, SearchDomain,
    SearchFairnessAssumption, SearchMachine, SearchSchedulerProfile, SerialProposalExecutor,
};

#[derive(Debug, Deserialize)]
struct SearchParityFixture {
    schema_version: String,
    canonical_batch_nodes: Vec<u8>,
    independent_targets: Vec<u8>,
    replay_epoch_trace: Vec<u64>,
    replay_phase_trace: Vec<u64>,
    barrier_before_epoch: u64,
    barrier_after_epoch: u64,
    barrier_phase_delta: u64,
    fairness_bundle: Vec<String>,
}

#[derive(Clone, Debug, Default)]
struct TestDomain {
    edges: BTreeMap<u8, Vec<(u8, &'static str, u64)>>,
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
        _node: &Self::Node,
        _goal: &Self::Node,
    ) -> Self::Cost {
        0
    }

    fn snapshot_id(&self, epoch: &Self::GraphEpoch) -> Self::SnapshotId {
        if *epoch == 1 {
            "epoch-1"
        } else {
            "epoch-2"
        }
    }
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root")
        .to_path_buf()
}

fn search_fixture() -> SearchParityFixture {
    let root = repo_root();
    let build = Command::new("lake")
        .arg("--dir")
        .arg("lean")
        .arg("build")
        .arg("search_parity_runner")
        .current_dir(&root)
        .output()
        .expect("build search parity runner");
    assert!(
        build.status.success(),
        "lake build failed: {}",
        String::from_utf8_lossy(&build.stderr)
    );
    let run = Command::new("./lean/.lake/build/bin/search_parity_runner")
        .current_dir(&root)
        .output()
        .expect("run search parity runner");
    assert!(
        run.status.success(),
        "runner failed: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    serde_json::from_slice(&run.stdout).expect("parse search parity fixture")
}

fn make_domain() -> TestDomain {
    let mut domain = TestDomain::default();
    domain.edges.insert(0, vec![(1, "0-1", 1), (2, "0-2", 1)]);
    domain.edges.insert(1, vec![(4, "1-4", 1)]);
    domain.edges.insert(2, vec![(5, "2-5", 1)]);
    domain
}

#[test]
fn lean_fixture_matches_batch_independence_replay_and_barrier_surfaces() {
    let fixture = search_fixture();
    assert_eq!(fixture.schema_version, "search_parity_v1");

    let domain = make_domain();
    let mut machine = SearchMachine::new(domain.clone(), 1, 0, 5, EpsilonMilli::one());
    machine.step_once().expect("first canonical step");
    let batch = machine.next_batch().expect("second batch");
    assert_eq!(
        batch
            .entries
            .iter()
            .map(|entry| entry.node)
            .collect::<Vec<_>>(),
        fixture.canonical_batch_nodes
    );

    let left = Proposal {
        batch_index: 0,
        from: 1,
        to: fixture.independent_targets[0],
        edge: "1-4",
        edge_cost: 1_u64,
        tentative_g: 2_u64,
        kind: ProposalKind::Relax,
        read_set: AuthorityReadSet {
            target_nodes: [1, fixture.independent_targets[0]].into_iter().collect(),
            surfaces: [
                AuthoritySurface::BatchWindow,
                AuthoritySurface::GraphEpoch,
                AuthoritySurface::Phase,
            ]
            .into_iter()
            .collect(),
        },
        write_set: AuthorityWriteSet {
            target_nodes: [fixture.independent_targets[0]].into_iter().collect(),
            surfaces: Default::default(),
        },
    };
    let right = Proposal {
        batch_index: 1,
        from: 2,
        to: fixture.independent_targets[1],
        edge: "2-5",
        edge_cost: 1_u64,
        tentative_g: 2_u64,
        kind: ProposalKind::Relax,
        read_set: AuthorityReadSet {
            target_nodes: [2, fixture.independent_targets[1]].into_iter().collect(),
            surfaces: [
                AuthoritySurface::BatchWindow,
                AuthoritySurface::GraphEpoch,
                AuthoritySurface::Phase,
            ]
            .into_iter()
            .collect(),
        },
        write_set: AuthorityWriteSet {
            target_nodes: [fixture.independent_targets[1]].into_iter().collect(),
            surfaces: Default::default(),
        },
    };
    assert!(proposals_independent(&left, &right));

    let mut replay_machine = SearchMachine::new(domain, 1, 0, 5, EpsilonMilli::one());
    let (report, replay) = run_with_executor(
        &mut replay_machine,
        &SerialProposalExecutor,
        SearchSchedulerProfile::CanonicalSerial,
        1,
        vec![SearchFairnessAssumption::EventualLiveBatchService],
    )
    .expect("canonical run");
    let replayed = replay_observation(
        &replay,
        &ReplayExpectation {
            expected_epochs: fixture.replay_epoch_trace.clone(),
            expected_phases: fixture.replay_phase_trace.clone(),
            required_fairness: vec![SearchFairnessAssumption::EventualLiveBatchService],
        },
    )
    .expect("replay fixture");
    assert_eq!(replayed, report.observation);

    let mut barrier_machine = SearchMachine::new(
        make_domain(),
        fixture.barrier_before_epoch,
        0,
        5,
        EpsilonMilli::one(),
    );
    let before_phase = barrier_machine.state().phase;
    commit_epoch_reconfiguration(
        &mut barrier_machine,
        EpochReconfigurationRequest {
            next_epoch: fixture.barrier_after_epoch,
        },
    );
    assert_eq!(
        barrier_machine.state().graph_epoch,
        fixture.barrier_after_epoch
    );
    assert_eq!(
        barrier_machine.state().phase - before_phase,
        fixture.barrier_phase_delta
    );
    assert_eq!(fixture.fairness_bundle, vec!["EventualLiveBatchService"]);
}
