#![allow(clippy::expect_used, missing_docs)]

mod support;

use support::FixtureDomain;
use telltale_search::{
    EpsilonMilli, SearchError, SearchFairnessAssumption, SearchMachine, SearchSchedulerProfile,
};

fn make_domain(edges: &[(u8, u8, &'static str, u64)], heuristics: &[(u8, u64)]) -> FixtureDomain {
    let mut domain = FixtureDomain::default();
    for (from, to, edge, cost) in edges {
        domain.edge(*from, *to, edge, *cost);
    }
    for (node, heuristic) in heuristics {
        domain.heuristic_value(1, *node, *heuristic);
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
    let parent = machine.state().parent.get(&3).expect("goal parent");
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
    let incumbent = machine.state().incumbent.as_ref().expect("incumbent");
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
        [SearchFairnessAssumption::DeterministicSchedulerConfluence]
            .into_iter()
            .collect(),
    );
    assert_eq!(artifact.incumbent_cost, Some(2));
    assert_eq!(artifact.incumbent_path, Some(vec![0, 1, 2]));
    assert_eq!(artifact.graph_epoch_trace, vec![7]);
    assert_eq!(artifact.productive_steps, 2);
    assert_eq!(artifact.total_scheduler_steps, 3);
}

#[test]
fn failed_expansion_leaves_canonical_state_unchanged() {
    let domain = FixtureDomain {
        fail_node: Some(0),
        ..Default::default()
    };
    let mut machine = SearchMachine::new(domain, 1, 0, 2, EpsilonMilli::one());
    let before = machine.state().clone();
    let err = machine.step_once().expect_err("expansion must fail");
    assert_eq!(err, SearchError::Domain("boom"));
    assert_eq!(machine.state(), &before);
}

#[test]
fn epsilon_decrease_rebuilds_open_from_open_and_incons() {
    let domain = make_domain(
        &[
            (0, 1, "0-1", 1),
            (0, 2, "0-2", 2),
            (1, 3, "1-3", 5),
            (2, 3, "2-3", 1),
        ],
        &[(1, 0), (2, 100), (3, 0)],
    );
    let mut machine = SearchMachine::new(domain, 1, 0, 3, EpsilonMilli(3_000));
    machine.step_once().expect("start expansion");
    machine.step_once().expect("expand node 1");
    machine.step_once().expect("expand closed goal candidate");
    machine.step_once().expect("improve closed node via node 2");
    assert!(machine.state().incons.contains(&3));
    let prior_phase = machine.state().phase;
    machine.decrease_epsilon_and_rebuild(EpsilonMilli::one());
    assert_eq!(machine.state().phase, prior_phase + 1);
    assert!(machine.state().closed.is_empty());
    assert!(machine.state().incons.is_empty());
    assert!(machine.state().open.contains_key(&3));
    assert_eq!(machine.state().epsilon, EpsilonMilli::one());
}

#[test]
fn unreachable_goal_leaves_incumbent_empty() {
    let domain = make_domain(&[(0, 1, "0-1", 1), (1, 2, "1-2", 1)], &[]);
    let mut machine = SearchMachine::new(domain, 1, 0, 9, EpsilonMilli::one());
    machine.run_to_completion().expect("run to completion");
    assert!(machine.state().incumbent.is_none());
    assert_eq!(machine.reconstruct_path(&9), None);
}

#[test]
fn long_chain_search_reaches_the_tail_goal() {
    let mut domain = FixtureDomain::default();
    for node in 0_u8..31 {
        domain.edge(node, node + 1, "chain", 1);
    }
    let mut machine = SearchMachine::new(domain, 1, 0, 31, EpsilonMilli::one());
    machine.run_to_completion().expect("run to completion");
    let incumbent = machine.state().incumbent.as_ref().expect("incumbent");
    assert_eq!(incumbent.cost, 31);
    assert_eq!(incumbent.path.len(), 32);
    assert_eq!(incumbent.path.first(), Some(&0));
    assert_eq!(incumbent.path.last(), Some(&31));
}

#[test]
fn dense_shared_successor_preserves_the_best_parent() {
    let domain = make_domain(
        &[
            (0, 1, "0-1", 1),
            (0, 2, "0-2", 1),
            (0, 3, "0-3", 1),
            (1, 4, "1-4", 5),
            (2, 4, "2-4", 2),
            (3, 4, "3-4", 3),
        ],
        &[],
    );
    let mut machine = SearchMachine::new(domain, 1, 0, 4, EpsilonMilli::one());
    machine.run_to_completion().expect("run to completion");
    let incumbent = machine.state().incumbent.as_ref().expect("incumbent");
    assert_eq!(incumbent.cost, 3);
    assert_eq!(incumbent.path, vec![0, 2, 4]);
    assert_eq!(machine.state().parent.get(&4).expect("parent").from, 2);
}
