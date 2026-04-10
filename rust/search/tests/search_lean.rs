//! Reduced Rust/Lean parity checks for `telltale-search`.
#![cfg(not(target_arch = "wasm32"))]
#![allow(clippy::expect_used, missing_docs)]

mod support;

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde::Deserialize;
use support::FixtureDomain;
use telltale_search::{
    commit_epoch_reconfiguration, proposals_independent, replay_observation, run_with_executor,
    search_theorem_pack_artifact, AuthorityReadSet, AuthoritySurface, AuthorityWriteSet,
    EpochReconfigurationRequest, EpsilonMilli, Proposal, ProposalKind, ReplayExpectation,
    SearchFairnessAssumption, SearchFairnessCertificateClass, SearchFairnessClaimClass,
    SearchMachine, SearchRunConfig, SearchSchedulerProfile, SerialProposalExecutor,
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
    canonical_service_bound_steps: u64,
    profile_claims: SearchProfileClaims,
    profile_certificates: SearchProfileClaims,
    threaded_commit_trace_refines_canonical: bool,
    threaded_state_slice_refines_canonical: bool,
    threaded_observation_equivalent_to_canonical: bool,
    threaded_multi_step_state_trace_refines_canonical: bool,
    threaded_multi_step_observation_trace_refines_canonical: bool,
    threaded_state_artifact_refines_canonical: bool,
    threaded_multi_step_state_artifact_trace_refines_canonical: bool,
    certified_window_trace_valid: bool,
    fairness_inventory: Vec<SearchInventoryEntry>,
    theorem_pack_inventory: Vec<SearchInventoryEntry>,
    theorem_pack_inventory_classes: Vec<SearchInventoryClassEntry>,
    theorem_pack_service_bound_steps: u64,
    theorem_pack_goal_window_discovery_suffix_bound_steps: u64,
    theorem_pack_gate: String,
}

#[derive(Debug, Deserialize)]
struct SearchProfileClaims {
    canonical_serial: String,
    threaded_exact_single_lane: String,
    batched_parallel_exact: String,
    batched_parallel_envelope_bounded: String,
}

#[derive(Debug, Deserialize)]
struct SearchInventoryEntry {
    name: String,
    present: bool,
}

#[derive(Debug, Deserialize)]
struct SearchInventoryClassEntry {
    name: String,
    support_class: String,
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

fn make_domain() -> FixtureDomain {
    let mut domain = FixtureDomain::default();
    domain.edge(0, 1, "0-1", 1);
    domain.edge(0, 2, "0-2", 1);
    domain.edge(1, 4, "1-4", 1);
    domain.edge(2, 5, "2-5", 1);
    domain
}

fn assert_batch_and_independence_contracts(fixture: &SearchParityFixture, domain: &FixtureDomain) {
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
}

fn assert_replay_contracts(fixture: &SearchParityFixture, domain: FixtureDomain) {
    let mut replay_machine = SearchMachine::new(domain, 1, 0, 5, EpsilonMilli::one());
    let (report, replay) = run_with_executor(
        &mut replay_machine,
        &SerialProposalExecutor,
        SearchRunConfig {
            scheduler_profile: SearchSchedulerProfile::CanonicalSerial,
            batch_width: 1,
            fairness_assumptions: BTreeSet::from([
                SearchFairnessAssumption::DeterministicSchedulerConfluence,
                SearchFairnessAssumption::EventualLiveBatchService,
            ]),
        },
    )
    .expect("canonical run");
    assert_eq!(
        report.fairness.claim_class,
        SearchFairnessClaimClass::ExactOneStep
    );
    assert_eq!(
        report.fairness.certificate.class,
        SearchFairnessCertificateClass::CurrentMinKeyBatch
    );
    assert_eq!(report.fairness.certificate.service_bound_steps, Some(1));
    assert!(report.fairness.exact_commit_trace_refines_canonical);
    assert!(report.fairness.exact_state_slice_refines_canonical);
    assert!(report.fairness.exact_observation_equivalent_to_canonical);
    assert_eq!(
        report.fairness.certificate.certified_batch_nodes,
        replay
            .rounds
            .first()
            .expect("representative replay round")
            .batch_nodes
    );
    assert_eq!(
        report.fairness.certificate.certified_normalized_commits,
        replay
            .rounds
            .first()
            .expect("representative replay round")
            .commits
    );
    assert_eq!(
        report.fairness.certificate.certified_epoch,
        replay.rounds.first().map(|round| round.epoch)
    );
    assert_eq!(
        report.fairness.certificate.certified_phase,
        replay.rounds.first().map(|round| round.phase)
    );
    let replayed = replay_observation(
        &replay,
        &ReplayExpectation {
            expected_epochs: fixture.replay_epoch_trace.clone(),
            expected_snapshots: replay
                .rounds
                .iter()
                .map(|round| round.snapshot_id)
                .collect(),
            expected_phases: fixture.replay_phase_trace.clone(),
            expected_batch_nodes: replay
                .rounds
                .iter()
                .map(|round| round.batch_nodes.clone())
                .collect(),
            required_fairness: BTreeSet::from([
                SearchFairnessAssumption::DeterministicSchedulerConfluence,
                SearchFairnessAssumption::EventualLiveBatchService,
            ]),
        },
    )
    .expect("replay fixture");
    assert_eq!(replayed, report.observation);
}

fn assert_barrier_contracts(fixture: &SearchParityFixture) {
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

#[allow(clippy::too_many_lines, clippy::cognitive_complexity)]
fn assert_fairness_contracts(fixture: &SearchParityFixture) {
    assert_eq!(fixture.canonical_service_bound_steps, 1);
    assert_eq!(fixture.profile_claims.canonical_serial, "exact_one_step");
    assert_eq!(
        fixture.profile_claims.threaded_exact_single_lane,
        "exact_one_step_under_refinement"
    );
    assert_eq!(
        fixture.profile_claims.batched_parallel_exact,
        "premised_window_bounded"
    );
    assert_eq!(
        fixture.profile_claims.batched_parallel_envelope_bounded,
        "premise_only"
    );
    assert_eq!(
        fixture.profile_certificates.canonical_serial,
        "current_min_key_batch"
    );
    assert_eq!(
        fixture.profile_certificates.threaded_exact_single_lane,
        "current_min_key_batch_via_threaded_refinement"
    );
    assert_eq!(
        fixture.profile_certificates.batched_parallel_exact,
        "certified_current_min_key_window"
    );
    assert_eq!(
        fixture
            .profile_certificates
            .batched_parallel_envelope_bounded,
        "none"
    );
    assert!(fixture.threaded_commit_trace_refines_canonical);
    assert!(fixture.threaded_state_slice_refines_canonical);
    assert!(fixture.threaded_observation_equivalent_to_canonical);
    assert!(fixture.threaded_multi_step_state_trace_refines_canonical);
    assert!(fixture.threaded_multi_step_observation_trace_refines_canonical);
    assert!(fixture.threaded_state_artifact_refines_canonical);
    assert!(fixture.threaded_multi_step_state_artifact_trace_refines_canonical);
    assert!(fixture.certified_window_trace_valid);
    assert_eq!(fixture.theorem_pack_service_bound_steps, 1);
    assert_eq!(
        fixture.theorem_pack_goal_window_discovery_suffix_bound_steps,
        1
    );
    assert_eq!(fixture.theorem_pack_gate, "just check-search-fairness");
    let inventory = fixture
        .fairness_inventory
        .iter()
        .map(|entry| (entry.name.as_str(), entry.present))
        .collect::<std::collections::BTreeMap<_, _>>();
    assert_eq!(
        inventory.get("search_canonical_serial_exact_one_step_fairness"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_canonical_serial_dynamic_liveness_under_stability"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_executable_canonical_step_preserves_invariants"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_executable_trace_refines_canonical_machine_trace"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_executable_step_artifact_refines_canonical_step_artifact"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_canonical_machine_step_preserves_invariants"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_canonical_machine_trace_currently_min_priority_eventually_serviced"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_canonical_machine_step_artifact_refines_runtime_boundary"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_canonical_machine_state_artifact_is_runtime_projection"),
        Some(&true)
    );
    assert_eq!(
        inventory
            .get("search_fixed_phase_canonical_serial_terminates_under_finite_reachable_bound"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_rebuild_aware_canonical_serial_terminates_under_phase_work_measure"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_bounded_strict_preemption_eventually_becomes_min"),
        Some(&true)
    );
    assert_eq!(
        inventory.get(
            "search_canonical_serial_nonmin_entry_eventually_serviced_under_bounded_strict_preemption"
        ),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_finite_better_entry_exhaustion_eventually_becomes_min"),
        Some(&true)
    );
    assert_eq!(
        inventory.get(
            "search_canonical_serial_nonmin_entry_eventually_serviced_under_finite_better_entry_exhaustion"
        ),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_canonical_serial_goal_reached_from_ready_witness_path"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_canonical_machine_goal_reached_from_ready_witness_path"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_canonical_machine_goal_reached_from_graph_reachability"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_goal_reachability_connects_to_incumbent_publication"),
        Some(&true)
    );
    assert_eq!(
        inventory
            .get("search_eventual_optimal_goal_publication_under_admissible_consistent_heuristic"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_threaded_exact_single_lane_refines_canonical_one_step"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_threaded_exact_single_lane_commit_trace_refines_canonical"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_threaded_exact_single_lane_state_slice_refines_canonical"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_threaded_exact_single_lane_observation_slice_refines_canonical"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_threaded_exact_single_lane_observation_equivalent_to_canonical"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_threaded_exact_single_lane_multi_step_state_trace_refines_canonical"),
        Some(&true)
    );
    assert_eq!(
        inventory.get(
            "search_threaded_exact_single_lane_multi_step_observation_trace_refines_canonical"
        ),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_threaded_exact_single_lane_state_artifact_refines_canonical"),
        Some(&true)
    );
    assert_eq!(
        inventory.get(
            "search_threaded_exact_single_lane_multi_step_state_artifact_trace_refines_canonical"
        ),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_threaded_exact_single_lane_exact_one_step_fairness"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_canonical_serial_goal_window_service_has_exact_suffix_bound"),
        Some(&true)
    );
    assert_eq!(
        inventory
            .get("search_threaded_exact_single_lane_goal_window_service_has_exact_suffix_bound"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_batched_parallel_exact_certified_window_fairness"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_batched_parallel_exact_bounded_dynamic_starvation_freedom"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_batched_parallel_exact_certified_window_trace_valid"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_batched_parallel_envelope_design_boundary_explicit"),
        Some(&true)
    );
    assert_eq!(
        inventory.get("search_batched_parallel_envelope_unconditional_fairness"),
        Some(&false)
    );
    let theorem_pack_inventory = fixture
        .theorem_pack_inventory
        .iter()
        .map(|entry| (entry.name.as_str(), entry.present))
        .collect::<std::collections::BTreeMap<_, _>>();
    assert_eq!(theorem_pack_inventory, inventory);
    let rust_theorem_pack = search_theorem_pack_artifact();
    assert_eq!(
        rust_theorem_pack
            .inventory
            .iter()
            .map(|entry| (entry.name.as_str(), entry.present))
            .collect::<std::collections::BTreeMap<_, _>>(),
        theorem_pack_inventory
    );
    let theorem_pack_inventory_classes = fixture
        .theorem_pack_inventory_classes
        .iter()
        .map(|entry| (entry.name.as_str(), entry.support_class.as_str()))
        .collect::<std::collections::BTreeMap<_, _>>();
    assert_eq!(
        theorem_pack_inventory_classes.get("search_canonical_serial_exact_one_step_fairness"),
        Some(&"executable_semantics")
    );
    assert_eq!(
        theorem_pack_inventory_classes
            .get("search_executable_trace_refines_canonical_machine_trace"),
        Some(&"refinement_corollary")
    );
    assert_eq!(
        theorem_pack_inventory_classes
            .get("search_rebuild_aware_canonical_serial_terminates_under_phase_work_measure"),
        Some(&"premise_scoped")
    );
    assert_eq!(
        rust_theorem_pack
            .inventory_support_classes
            .iter()
            .map(|entry| {
                let support_class = match entry.support_class {
                    telltale_search::SearchTheoremSupportClass::ExecutableSemantics => {
                        "executable_semantics"
                    }
                    telltale_search::SearchTheoremSupportClass::RefinementCorollary => {
                        "refinement_corollary"
                    }
                    telltale_search::SearchTheoremSupportClass::PremiseScoped => "premise_scoped",
                };
                (entry.name.as_str(), support_class)
            })
            .collect::<std::collections::BTreeMap<_, _>>(),
        theorem_pack_inventory_classes
    );
    assert_eq!(
        rust_theorem_pack.canonical_service_bound_steps,
        fixture.theorem_pack_service_bound_steps
    );
    assert_eq!(
        rust_theorem_pack.canonical_goal_window_discovery_suffix_bound_steps,
        fixture.theorem_pack_goal_window_discovery_suffix_bound_steps
    );
    assert_eq!(rust_theorem_pack.gate, fixture.theorem_pack_gate);
}

#[test]
fn lean_fixture_matches_batch_independence_replay_and_barrier_surfaces() {
    let fixture = search_fixture();
    assert_eq!(fixture.schema_version, "search_parity_v10");

    let domain = make_domain();
    assert_batch_and_independence_contracts(&fixture, &domain);
    assert_replay_contracts(&fixture, domain);
    assert_barrier_contracts(&fixture);
    assert_fairness_contracts(&fixture);
}
