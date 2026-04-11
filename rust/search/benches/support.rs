#![allow(dead_code, missing_docs)]

use std::collections::{BTreeMap, BTreeSet};
#[cfg(feature = "multi-thread")]
use std::num::NonZeroU64;

#[cfg(feature = "multi-thread")]
use telltale_search::NativeParallelExecutor;
use telltale_search::{
    full_state_artifact_for_machine, run_with_executor, EpsilonMilli, ProposalExecutor,
    SearchDomain, SearchExecutionPolicy, SearchFairnessAssumption, SearchMachine, SearchQuery,
    SearchRunConfig, SearchSchedulerProfile, SerialProposalExecutor,
};

#[derive(Clone, Copy, Debug)]
enum HeuristicModel {
    Zero,
    GridScaled { width: u32, divisor: u32 },
}

#[derive(Clone, Debug)]
pub(crate) struct BenchDomain {
    edges: BTreeMap<u32, Vec<(u32, &'static str, u64)>>,
    heuristic: HeuristicModel,
}

impl Default for BenchDomain {
    fn default() -> Self {
        Self {
            edges: BTreeMap::new(),
            heuristic: HeuristicModel::Zero,
        }
    }
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
        node: &Self::Node,
        goal: &Self::Node,
    ) -> Self::Cost {
        match self.heuristic {
            HeuristicModel::Zero => 0,
            HeuristicModel::GridScaled { width, divisor } => {
                let (x, y) = decode_grid_node(*node, width);
                let (goal_x, goal_y) = decode_grid_node(*goal, width);
                let manhattan = x.abs_diff(goal_x) + y.abs_diff(goal_y);
                u64::from(manhattan / divisor.max(1))
            }
        }
    }

    fn snapshot_id(&self, _epoch: &Self::GraphEpoch) -> Self::SnapshotId {
        "bench-epoch"
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct SearchBenchCounters {
    pub expansions: u64,
    pub batches: u64,
    pub productive_steps: u64,
    pub total_scheduler_steps: u64,
    pub phase_count: u64,
    pub rebuild_count: u64,
    pub frontier_peak_size: u64,
    pub proposals_generated: u64,
    pub proposals_after_normalization: u64,
    pub normalized_duplicate_targets_dropped: u64,
    pub rejected_normalized_proposals: u64,
    pub proposals_committed: u64,
    pub decrease_key_commits: u64,
    pub incumbent_publication_count: u64,
}

impl SearchBenchCounters {
    #[must_use]
    pub(crate) fn render(&self, label: &str) -> String {
        format!(
            concat!(
                "search-bench case={label}",
                " expansions={expansions}",
                " batches={batches}",
                " productive_steps={productive_steps}",
                " total_scheduler_steps={total_scheduler_steps}",
                " phase_count={phase_count}",
                " rebuild_count={rebuild_count}",
                " frontier_peak_size={frontier_peak_size}",
                " proposals_generated={proposals_generated}",
                " proposals_after_normalization={proposals_after_normalization}",
                " duplicates_dropped={normalized_duplicate_targets_dropped}",
                " rejected_normalized_proposals={rejected_normalized_proposals}",
                " proposals_committed={proposals_committed}",
                " decrease_key_commits={decrease_key_commits}",
                " incumbent_publications={incumbent_publication_count}",
            ),
            label = label,
            expansions = self.expansions,
            batches = self.batches,
            productive_steps = self.productive_steps,
            total_scheduler_steps = self.total_scheduler_steps,
            phase_count = self.phase_count,
            rebuild_count = self.rebuild_count,
            frontier_peak_size = self.frontier_peak_size,
            proposals_generated = self.proposals_generated,
            proposals_after_normalization = self.proposals_after_normalization,
            normalized_duplicate_targets_dropped = self.normalized_duplicate_targets_dropped,
            rejected_normalized_proposals = self.rejected_normalized_proposals,
            proposals_committed = self.proposals_committed,
            decrease_key_commits = self.decrease_key_commits,
            incumbent_publication_count = self.incumbent_publication_count,
        )
    }
}

pub(crate) fn chain_domain(length: u32) -> BenchDomain {
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

pub(crate) fn fan_in_domain(width: u32) -> BenchDomain {
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

pub(crate) fn duplicate_pressure_domain(branches: u32, shared_targets: u32) -> BenchDomain {
    let mut domain = BenchDomain::default();
    let shared_base = branches + 1;
    let goal = shared_base + shared_targets;
    for branch in 1..=branches {
        domain
            .edges
            .entry(0)
            .or_default()
            .push((branch, "branch", 1));
        for offset in 0..shared_targets {
            let target = shared_base + offset;
            let cost = u64::from(((branch + offset) % 9) + 1);
            domain
                .edges
                .entry(branch)
                .or_default()
                .push((target, "shared", cost));
        }
    }
    for offset in 0..shared_targets {
        domain
            .edges
            .entry(shared_base + offset)
            .or_default()
            .push((goal, "goal", 1));
    }
    domain
}

pub(crate) fn selector_candidate_domain(candidates: u32) -> (BenchDomain, Vec<u32>) {
    let mut domain = BenchDomain::default();
    let candidate_base = candidates + 1;
    let mut accepted = Vec::new();
    for branch in 1..=candidates {
        let candidate = candidate_base + branch - 1;
        accepted.push(candidate);
        domain
            .edges
            .entry(0)
            .or_default()
            .push((branch, "branch", 1));
        domain.edges.entry(branch).or_default().push((
            candidate,
            "candidate",
            u64::from((branch % 11) + 1),
        ));
    }
    (domain, accepted)
}

pub(crate) fn grid_domain(width: u32, height: u32, heuristic_divisor: u32) -> BenchDomain {
    let mut domain = BenchDomain {
        heuristic: HeuristicModel::GridScaled {
            width,
            divisor: heuristic_divisor.max(1),
        },
        ..BenchDomain::default()
    };

    for y in 0..height {
        for x in 0..width {
            let node = encode_grid_node(x, y, width);
            if x + 1 < width {
                domain.edges.entry(node).or_default().push((
                    encode_grid_node(x + 1, y, width),
                    "right",
                    1,
                ));
            }
            if y + 1 < height {
                domain.edges.entry(node).or_default().push((
                    encode_grid_node(x, y + 1, width),
                    "down",
                    1,
                ));
            }
            if x > 0 {
                domain.edges.entry(node).or_default().push((
                    encode_grid_node(x - 1, y, width),
                    "left",
                    1,
                ));
            }
            if y > 0 {
                domain.edges.entry(node).or_default().push((
                    encode_grid_node(x, y - 1, width),
                    "up",
                    1,
                ));
            }
        }
    }

    domain
}

pub(crate) fn grid_goal(width: u32, height: u32) -> u32 {
    encode_grid_node(width - 1, height - 1, width)
}

pub(crate) fn print_case_metrics(label: &str, counters: &SearchBenchCounters) {
    eprintln!("{}", counters.render(label));
}

pub(crate) fn run_serial(domain: BenchDomain, start: u32, goal: u32) {
    let mut machine = SearchMachine::new(domain, 1, start, goal, EpsilonMilli::one());
    let _ = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        SearchRunConfig::new(
            SearchExecutionPolicy::new(SearchSchedulerProfile::CanonicalSerial, 1),
            BTreeSet::from([SearchFairnessAssumption::DeterministicSchedulerConfluence]),
        ),
    )
    .expect("benchmark search run");
}

pub(crate) fn run_selector_serial(domain: BenchDomain, start: u32, candidates: Vec<u32>) {
    let query = SearchQuery::candidate_set(start, candidates, None);
    let mut machine = SearchMachine::new_with_query(domain, 1, query, EpsilonMilli::one());
    let _ = run_with_executor(
        &mut machine,
        &SerialProposalExecutor,
        SearchRunConfig::new(
            SearchExecutionPolicy::new(SearchSchedulerProfile::CanonicalSerial, 1),
            BTreeSet::from([SearchFairnessAssumption::DeterministicSchedulerConfluence]),
        ),
    )
    .expect("selector benchmark search run");
}

pub(crate) fn run_rebuild_heavy_serial(
    domain: BenchDomain,
    start: u32,
    goal: u32,
    steps_per_phase: u64,
    schedule: &[EpsilonMilli],
) {
    let mut machine = SearchMachine::new(domain, 1, start, goal, EpsilonMilli(3_000));
    for next_epsilon in schedule {
        for _ in 0..steps_per_phase {
            if !machine.step_once().expect("benchmark search step") {
                return;
            }
        }
        machine.decrease_epsilon_and_rebuild(*next_epsilon);
    }
    machine
        .run_to_completion()
        .expect("benchmark search completion");
}

#[cfg(feature = "multi-thread")]
pub(crate) fn run_threaded_exact_single_lane(domain: BenchDomain, start: u32, goal: u32) {
    let executor = NativeParallelExecutor::new(NonZeroU64::new(1).expect("non-zero batch width"))
        .expect("native parallel executor");
    let mut machine = SearchMachine::new(domain, 1, start, goal, EpsilonMilli::one());
    let _ = run_with_executor(
        &mut machine,
        &executor,
        SearchRunConfig::new(
            SearchExecutionPolicy::new(SearchSchedulerProfile::ThreadedExactSingleLane, 1),
            BTreeSet::from([SearchFairnessAssumption::DeterministicSchedulerConfluence]),
        ),
    )
    .expect("benchmark threaded search run");
}

pub(crate) fn capture_serial_metrics(
    domain: BenchDomain,
    start: u32,
    goal: u32,
) -> SearchBenchCounters {
    capture_profiled_run(
        domain,
        start,
        goal,
        EpsilonMilli::one(),
        &SerialProposalExecutor,
        None,
    )
}

pub(crate) fn capture_selector_serial_metrics(
    domain: BenchDomain,
    start: u32,
    candidates: Vec<u32>,
) -> SearchBenchCounters {
    capture_profiled_query_run(
        domain,
        SearchQuery::candidate_set(start, candidates, None),
        EpsilonMilli::one(),
        &SerialProposalExecutor,
        None,
    )
}

pub(crate) fn capture_rebuild_metrics(
    domain: BenchDomain,
    start: u32,
    goal: u32,
    steps_per_phase: u64,
    schedule: &[EpsilonMilli],
) -> SearchBenchCounters {
    capture_profiled_run(
        domain,
        start,
        goal,
        EpsilonMilli(3_000),
        &SerialProposalExecutor,
        Some((steps_per_phase, schedule)),
    )
}

#[cfg(feature = "multi-thread")]
pub(crate) fn capture_threaded_exact_single_lane_metrics(
    domain: BenchDomain,
    start: u32,
    goal: u32,
) -> SearchBenchCounters {
    let executor = NativeParallelExecutor::new(NonZeroU64::new(1).expect("non-zero batch width"))
        .expect("native parallel executor");
    capture_profiled_run(domain, start, goal, EpsilonMilli::one(), &executor, None)
}

pub(crate) fn prepare_frontier_machine(
    domain: BenchDomain,
    start: u32,
    goal: u32,
    warmup_steps: u64,
) -> SearchMachine<BenchDomain> {
    let mut machine = SearchMachine::new(domain, 1, start, goal, EpsilonMilli::one());
    for _ in 0..warmup_steps {
        if !machine.step_once().expect("warmup search step") {
            break;
        }
    }
    machine
}

pub(crate) fn run_machine_only(domain: BenchDomain, start: u32, goal: u32) {
    let mut machine = SearchMachine::new(domain, 1, start, goal, EpsilonMilli::one());
    machine
        .run_to_completion()
        .expect("machine-only benchmark search completion");
}

pub(crate) fn export_observation_artifact(domain: BenchDomain, start: u32, goal: u32) {
    let mut machine = SearchMachine::new(domain, 1, start, goal, EpsilonMilli::one());
    machine
        .run_to_completion()
        .expect("artifact benchmark search completion");
    let _ = machine.observation_artifact(
        SearchSchedulerProfile::CanonicalSerial,
        BTreeSet::from([SearchFairnessAssumption::DeterministicSchedulerConfluence]),
    );
}

pub(crate) fn export_full_state_artifact(domain: BenchDomain, start: u32, goal: u32) {
    let mut machine = SearchMachine::new(domain, 1, start, goal, EpsilonMilli::one());
    machine
        .run_to_completion()
        .expect("artifact benchmark search completion");
    let _ = full_state_artifact_for_machine(&machine);
}

pub(crate) fn invariant_check_frontier(
    domain: BenchDomain,
    start: u32,
    goal: u32,
    warmup_steps: u64,
) {
    let machine = prepare_frontier_machine(domain, start, goal, warmup_steps);
    machine
        .check_invariants()
        .expect("invariant check benchmark");
}

fn capture_profiled_run<X>(
    domain: BenchDomain,
    start: u32,
    goal: u32,
    initial_epsilon: EpsilonMilli,
    executor: &X,
    rebuild_plan: Option<(u64, &[EpsilonMilli])>,
) -> SearchBenchCounters
where
    X: ProposalExecutor<BenchDomain>,
{
    capture_profiled_query_run(
        domain,
        SearchQuery::single_goal(start, goal),
        initial_epsilon,
        executor,
        rebuild_plan,
    )
}

fn capture_profiled_query_run<X>(
    domain: BenchDomain,
    query: SearchQuery<u32>,
    initial_epsilon: EpsilonMilli,
    executor: &X,
    rebuild_plan: Option<(u64, &[EpsilonMilli])>,
) -> SearchBenchCounters
where
    X: ProposalExecutor<BenchDomain>,
{
    let domain_for_executor = domain.clone();
    let mut machine = SearchMachine::new_with_query(domain, 1, query, initial_epsilon);
    let mut counters = SearchBenchCounters {
        frontier_peak_size: 1,
        phase_count: 1,
        ..SearchBenchCounters::default()
    };
    let mut schedule_index = 0usize;
    let mut phase_steps = 0u64;

    loop {
        let Some(batch) = machine.next_batch() else {
            break;
        };

        let mut proposals = executor
            .generate(&domain_for_executor, &batch, machine.query())
            .expect("profiled benchmark search run");
        let raw_proposals = u64::try_from(proposals.len()).expect("proposal length must fit");
        let pre_scores = machine.state().g_score.clone();
        let pre_parents = machine
            .state()
            .parent
            .iter()
            .map(|(node, parent)| (node.clone(), parent.from.clone()))
            .collect::<BTreeMap<_, _>>();
        let pre_incumbent = machine.state().incumbent.clone();

        counters.total_scheduler_steps += 1;
        counters.expansions += u64::try_from(batch.entries.len()).expect("batch length must fit");
        counters.batches += 1;
        counters.proposals_generated += raw_proposals;

        machine.activate_batch(&batch);
        machine.normalize_proposals(&mut proposals);

        let normalized_proposals =
            u64::try_from(proposals.len()).expect("proposal length must fit");
        counters.proposals_after_normalization += normalized_proposals;
        counters.normalized_duplicate_targets_dropped += raw_proposals - normalized_proposals;

        machine.commit_proposals(&proposals);

        let committed_nodes = machine
            .state()
            .g_score
            .iter()
            .filter(|(node, score)| {
                pre_scores.get(*node).copied() != Some(**score)
                    || pre_parents.get(*node)
                        != machine.state().parent.get(*node).map(|parent| &parent.from)
            })
            .map(|(node, _)| node.clone())
            .collect::<Vec<_>>();
        let committed_count =
            u64::try_from(committed_nodes.len()).expect("committed count must fit");

        counters.proposals_committed += committed_count;
        counters.rejected_normalized_proposals += normalized_proposals - committed_count;
        counters.decrease_key_commits += u64::try_from(
            committed_nodes
                .iter()
                .filter(|node| pre_scores.contains_key(*node))
                .count(),
        )
        .expect("decrease-key count must fit");
        if committed_count > 0 {
            counters.productive_steps += 1;
        }
        if machine.state().incumbent != pre_incumbent {
            counters.incumbent_publication_count += 1;
        }
        counters.frontier_peak_size = counters
            .frontier_peak_size
            .max(u64::try_from(machine.state().open.len()).expect("frontier size must fit"));

        phase_steps += 1;
        if let Some((steps_per_phase, schedule)) = rebuild_plan {
            if phase_steps >= steps_per_phase && schedule_index < schedule.len() {
                machine.decrease_epsilon_and_rebuild(schedule[schedule_index]);
                counters.rebuild_count += 1;
                counters.phase_count = machine.state().phase + 1;
                counters.frontier_peak_size = counters.frontier_peak_size.max(
                    u64::try_from(machine.state().open.len()).expect("frontier size must fit"),
                );
                schedule_index += 1;
                phase_steps = 0;
            }
        }
    }

    counters.phase_count = counters.phase_count.max(machine.state().phase + 1);
    counters
}

fn encode_grid_node(x: u32, y: u32, width: u32) -> u32 {
    y * width + x
}

fn decode_grid_node(node: u32, width: u32) -> (u32, u32) {
    (node % width, node / width)
}
