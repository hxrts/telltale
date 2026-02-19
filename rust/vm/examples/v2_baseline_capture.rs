#![allow(missing_docs)]

#[cfg(not(feature = "multi-thread"))]
fn main() {
    eprintln!("error: example requires --features multi-thread");
    std::process::exit(2);
}

#[cfg(feature = "multi-thread")]
mod app {
    use std::collections::BTreeMap;
    use std::time::Instant;

    use serde::Serialize;
    use telltale_types::{GlobalType, Label, LocalTypeR};
    use telltale_vm::coroutine::Value;
    use telltale_vm::determinism::{DeterminismMode, EffectDeterminismTier};
    use telltale_vm::effect::EffectHandler;
    use telltale_vm::envelope_diff::EnvelopeDiffArtifactV1;
    use telltale_vm::loader::CodeImage;
    use telltale_vm::threaded::ThreadedVM;
    use telltale_vm::verification::{DefaultVerificationModel, HashTag, VerificationModel};
    use telltale_vm::vm::{RuntimeTuningProfile, StepResult, VMConfig, VM};

    const SCHEMA_VERSION: u32 = 1;
    const DISJOINT_SESSIONS: usize = 96;
    const CONTENDED_SESSIONS: usize = 48;
    const DISJOINT_CANONICAL_CONCURRENCY: usize = 1;
    const DISJOINT_THREADED_WORKERS: usize = 8;
    const CONTENDED_CANONICAL_CONCURRENCY: usize = 1;
    const CONTENDED_THREADED_WORKERS: usize = 2;
    const M1_STRESS_CANONICAL_CONCURRENCY: usize = 1;
    const M1_STRESS_THREADED_WORKERS: usize = 8;
    const MAX_ROUNDS: usize = 4096;

    #[derive(Debug, Clone, Copy, Serialize)]
    #[serde(rename_all = "snake_case")]
    enum WorkloadMode {
        Disjoint,
        Contended,
    }

    #[derive(Debug, Clone, Copy)]
    struct PassthroughHandler;

    impl EffectHandler for PassthroughHandler {
        fn handle_send(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &[Value],
        ) -> Result<Value, String> {
            Ok(Value::Nat(1))
        }

        fn handle_recv(
            &self,
            _role: &str,
            _partner: &str,
            _label: &str,
            _state: &mut Vec<Value>,
            _payload: &Value,
        ) -> Result<(), String> {
            Ok(())
        }

        fn handle_choose(
            &self,
            _role: &str,
            _partner: &str,
            labels: &[String],
            _state: &[Value],
        ) -> Result<String, String> {
            labels
                .first()
                .cloned()
                .ok_or_else(|| "no labels available".to_string())
        }

        fn step(&self, _role: &str, _state: &mut Vec<Value>) -> Result<(), String> {
            Ok(())
        }
    }

    #[derive(Debug, Serialize)]
    struct WorkloadProfile {
        mode: WorkloadMode,
        tuning_profile: RuntimeTuningProfile,
        sessions: usize,
        canonical_concurrency: usize,
        threaded_workers: usize,
        footprint_guided_wave_widening: bool,
        max_rounds: usize,
    }

    #[derive(Debug, Serialize)]
    struct EngineMetrics {
        elapsed_ms: u128,
        steps: usize,
        throughput_steps_per_sec: f64,
        throughput_sessions_per_sec: f64,
        p50_step_latency_us: u128,
        p99_step_latency_us: u128,
        mean_wave_width: f64,
        max_wave_width: usize,
        lock_contention_events_per_1k_steps: f64,
        mutex_lock_contention_events_per_1k_steps: f64,
        planner_conflict_events_per_1k_steps: f64,
    }

    #[derive(Debug, Serialize)]
    struct BaselineArtifact {
        schema_version: u32,
        workload: WorkloadProfile,
        canonical: EngineMetrics,
        threaded: EngineMetrics,
        canonical_replay_fragment_hash: String,
        threaded_replay_fragment_hash: String,
        envelope_diff_artifact: EnvelopeDiffArtifactV1,
        artifact_hash: String,
    }

    pub(super) fn run() -> Result<(), String> {
        let (output_path, workload_mode, tuning_profile) = parse_cli();
        let sessions = match workload_mode {
            WorkloadMode::Disjoint => DISJOINT_SESSIONS,
            WorkloadMode::Contended => CONTENDED_SESSIONS,
        };
        let tuning = workload_tuning(workload_mode, tuning_profile);
        let handler = PassthroughHandler;

        let mut canonical_vm = VM::new(tuning.config.clone());
        for i in 0..sessions {
            canonical_vm
                .load_choreography(&build_workload_image(workload_mode, i))
                .map_err(|err| format!("canonical load failed: {err}"))?;
        }
        let canonical = run_canonical_metrics(
            &mut canonical_vm,
            &handler,
            tuning.canonical_concurrency,
            sessions,
        )?;

        let mut threaded_vm =
            ThreadedVM::with_workers(tuning.config.clone(), tuning.threaded_workers);
        for i in 0..sessions {
            threaded_vm
                .load_choreography(&build_workload_image(workload_mode, i))
                .map_err(|err| format!("threaded load failed: {err}"))?;
        }
        let threaded = run_threaded_metrics(
            &mut threaded_vm,
            &handler,
            tuning.threaded_workers,
            sessions,
        )?;

        let canonical_fragment = canonical_vm.canonical_replay_fragment();
        let threaded_fragment = threaded_vm.canonical_replay_fragment();

        let envelope_diff_artifact = EnvelopeDiffArtifactV1::from_replay_fragments(
            "native_single_thread",
            "native_threaded",
            &canonical_fragment,
            &threaded_fragment,
            canonical.max_wave_width,
            threaded.max_wave_width,
            threaded.max_wave_width.max(canonical.max_wave_width),
            EffectDeterminismTier::EnvelopeBoundedNondeterministic,
        );

        let canonical_replay_fragment_hash = stable_hash_hex(&canonical_fragment);
        let threaded_replay_fragment_hash = stable_hash_hex(&threaded_fragment);

        let mut artifact = BaselineArtifact {
            schema_version: SCHEMA_VERSION,
            workload: WorkloadProfile {
                mode: workload_mode,
                tuning_profile,
                sessions,
                canonical_concurrency: tuning.canonical_concurrency,
                threaded_workers: tuning.threaded_workers,
                footprint_guided_wave_widening: tuning.config.footprint_guided_wave_widening,
                max_rounds: MAX_ROUNDS,
            },
            canonical,
            threaded,
            canonical_replay_fragment_hash,
            threaded_replay_fragment_hash,
            envelope_diff_artifact,
            artifact_hash: String::new(),
        };

        artifact.artifact_hash = stable_hash_hex(&artifact);
        let encoded = serde_json::to_vec_pretty(&artifact)
            .map_err(|err| format!("artifact serialization failed: {err}"))?;

        if let Some(path) = output_path {
            std::fs::write(&path, encoded)
                .map_err(|err| format!("failed to write artifact to `{path}`: {err}"))?;
        } else {
            println!(
                "{}",
                String::from_utf8(encoded)
                    .map_err(|err| format!("artifact utf8 encoding failed: {err}"))?
            );
        }

        Ok(())
    }

    fn run_canonical_metrics(
        vm: &mut VM,
        handler: &dyn EffectHandler,
        concurrency: usize,
        sessions: usize,
    ) -> Result<EngineMetrics, String> {
        let mut round_latencies_us = Vec::new();
        let mut rounds = 0usize;
        let mut total_wave_width = 0usize;
        let mut max_wave_width = 0usize;
        let mut previous_steps = vm.scheduler_step_count();
        let mut completed = false;
        let started = Instant::now();

        for _ in 0..MAX_ROUNDS {
            rounds += 1;
            let round_started = Instant::now();
            let result = vm
                .step_round(handler, concurrency)
                .map_err(|err| format!("canonical step_round failed: {err}"))?;
            round_latencies_us.push(round_started.elapsed().as_micros());

            let current_steps = vm.scheduler_step_count();
            let wave_width = current_steps.saturating_sub(previous_steps);
            previous_steps = current_steps;
            total_wave_width = total_wave_width.saturating_add(wave_width);
            max_wave_width = max_wave_width.max(wave_width);

            match result {
                StepResult::AllDone => {
                    completed = true;
                    break;
                }
                StepResult::Continue => {}
                StepResult::Stuck => return Err("canonical run became stuck".to_string()),
            }
        }

        if !completed {
            return Err(format!("canonical run exceeded max rounds ({MAX_ROUNDS})"));
        }

        let elapsed = started.elapsed();
        let elapsed_ms = elapsed.as_millis();
        let elapsed_secs = elapsed.as_secs_f64().max(f64::EPSILON);
        let steps = vm.scheduler_step_count();
        Ok(EngineMetrics {
            elapsed_ms,
            steps,
            throughput_steps_per_sec: steps as f64 / elapsed_secs,
            throughput_sessions_per_sec: sessions as f64 / elapsed_secs,
            p50_step_latency_us: percentile_us(&round_latencies_us, 50),
            p99_step_latency_us: percentile_us(&round_latencies_us, 99),
            mean_wave_width: if rounds == 0 {
                0.0
            } else {
                total_wave_width as f64 / rounds as f64
            },
            max_wave_width,
            lock_contention_events_per_1k_steps: 0.0,
            mutex_lock_contention_events_per_1k_steps: 0.0,
            planner_conflict_events_per_1k_steps: 0.0,
        })
    }

    fn run_threaded_metrics(
        vm: &mut ThreadedVM,
        handler: &dyn EffectHandler,
        concurrency: usize,
        sessions: usize,
    ) -> Result<EngineMetrics, String> {
        let mut round_latencies_us = Vec::new();
        let mut rounds = 0usize;
        let mut total_wave_width = 0usize;
        let mut max_wave_width = 0usize;
        let mut completed = false;
        let started = Instant::now();

        for _ in 0..MAX_ROUNDS {
            rounds += 1;
            let lane_trace_before = vm.lane_trace().len();

            let round_started = Instant::now();
            let result = vm
                .step_round(handler, concurrency)
                .map_err(|err| format!("threaded step_round failed: {err}"))?;
            round_latencies_us.push(round_started.elapsed().as_micros());

            let wave_width = vm.lane_trace().len().saturating_sub(lane_trace_before);
            total_wave_width = total_wave_width.saturating_add(wave_width);
            max_wave_width = max_wave_width.max(wave_width);

            match result {
                StepResult::AllDone => {
                    completed = true;
                    break;
                }
                StepResult::Continue => {}
                StepResult::Stuck => return Err("threaded run became stuck".to_string()),
            }
        }

        if !completed {
            return Err(format!("threaded run exceeded max rounds ({MAX_ROUNDS})"));
        }

        let elapsed = started.elapsed();
        let elapsed_ms = elapsed.as_millis();
        let elapsed_secs = elapsed.as_secs_f64().max(f64::EPSILON);
        let steps = vm.lane_trace().len();
        let contention = vm.contention_metrics().clone();
        Ok(EngineMetrics {
            elapsed_ms,
            steps,
            throughput_steps_per_sec: steps as f64 / elapsed_secs,
            throughput_sessions_per_sec: sessions as f64 / elapsed_secs,
            p50_step_latency_us: percentile_us(&round_latencies_us, 50),
            p99_step_latency_us: percentile_us(&round_latencies_us, 99),
            mean_wave_width: if rounds == 0 {
                0.0
            } else {
                total_wave_width as f64 / rounds as f64
            },
            max_wave_width: max_wave_width.max(contention.max_wave_width),
            lock_contention_events_per_1k_steps: if steps == 0 {
                0.0
            } else {
                contention.lock_contention_events as f64 * 1000.0 / steps as f64
            },
            mutex_lock_contention_events_per_1k_steps: if steps == 0 {
                0.0
            } else {
                contention.mutex_lock_contention_events as f64 * 1000.0 / steps as f64
            },
            planner_conflict_events_per_1k_steps: if steps == 0 {
                0.0
            } else {
                contention.planner_conflict_events as f64 * 1000.0 / steps as f64
            },
        })
    }

    fn percentile_us(values: &[u128], percentile: usize) -> u128 {
        if values.is_empty() {
            return 0;
        }
        let mut sorted = values.to_vec();
        sorted.sort_unstable();
        let p = percentile.clamp(0, 100) as f64 / 100.0;
        let idx = ((sorted.len() - 1) as f64 * p).round() as usize;
        sorted[idx]
    }

    #[derive(Debug, Clone)]
    struct WorkloadTuning {
        config: VMConfig,
        canonical_concurrency: usize,
        threaded_workers: usize,
    }

    fn workload_tuning(mode: WorkloadMode, profile: RuntimeTuningProfile) -> WorkloadTuning {
        if profile == RuntimeTuningProfile::M1StressReference
            && matches!(mode, WorkloadMode::Contended)
        {
            return WorkloadTuning {
                config: VMConfig {
                    determinism_mode: DeterminismMode::ModuloCommutativity,
                    effect_determinism_tier: EffectDeterminismTier::EnvelopeBoundedNondeterministic,
                    footprint_guided_wave_widening: true,
                    runtime_tuning_profile: profile,
                    ..VMConfig::default()
                },
                canonical_concurrency: M1_STRESS_CANONICAL_CONCURRENCY,
                threaded_workers: M1_STRESS_THREADED_WORKERS,
            };
        }

        match mode {
            WorkloadMode::Disjoint => WorkloadTuning {
                config: VMConfig {
                    determinism_mode: DeterminismMode::ModuloCommutativity,
                    effect_determinism_tier: EffectDeterminismTier::EnvelopeBoundedNondeterministic,
                    footprint_guided_wave_widening: true,
                    runtime_tuning_profile: profile,
                    ..VMConfig::default()
                },
                canonical_concurrency: DISJOINT_CANONICAL_CONCURRENCY,
                threaded_workers: DISJOINT_THREADED_WORKERS,
            },
            WorkloadMode::Contended => WorkloadTuning {
                config: VMConfig {
                    determinism_mode: DeterminismMode::ModuloCommutativity,
                    effect_determinism_tier: EffectDeterminismTier::EnvelopeBoundedNondeterministic,
                    footprint_guided_wave_widening: false,
                    runtime_tuning_profile: profile,
                    ..VMConfig::default()
                },
                canonical_concurrency: CONTENDED_CANONICAL_CONCURRENCY,
                threaded_workers: CONTENDED_THREADED_WORKERS,
            },
        }
    }

    fn simple_send_recv_image(label: &str) -> CodeImage {
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".to_string(),
                branches: vec![(Label::new(label), None, LocalTypeR::End)],
            },
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".to_string(),
                branches: vec![(Label::new(label), None, LocalTypeR::End)],
            },
        );
        let global = GlobalType::send("A", "B", Label::new(label), GlobalType::End);
        CodeImage::from_local_types(&local_types, &global)
    }

    fn contended_ring_image(tag: usize) -> CodeImage {
        let roles = ["A", "B", "C", "D"];
        let label = format!("c{tag}");
        let mut local_types = BTreeMap::new();
        local_types.insert(
            "A".to_string(),
            LocalTypeR::Send {
                partner: "B".to_string(),
                branches: vec![(
                    Label::new(&label),
                    None,
                    LocalTypeR::Recv {
                        partner: "D".to_string(),
                        branches: vec![(Label::new(&label), None, LocalTypeR::End)],
                    },
                )],
            },
        );
        local_types.insert(
            "B".to_string(),
            LocalTypeR::Recv {
                partner: "A".to_string(),
                branches: vec![(
                    Label::new(&label),
                    None,
                    LocalTypeR::Send {
                        partner: "C".to_string(),
                        branches: vec![(Label::new(&label), None, LocalTypeR::End)],
                    },
                )],
            },
        );
        local_types.insert(
            "C".to_string(),
            LocalTypeR::Recv {
                partner: "B".to_string(),
                branches: vec![(
                    Label::new(&label),
                    None,
                    LocalTypeR::Send {
                        partner: "D".to_string(),
                        branches: vec![(Label::new(&label), None, LocalTypeR::End)],
                    },
                )],
            },
        );
        local_types.insert(
            "D".to_string(),
            LocalTypeR::Recv {
                partner: "C".to_string(),
                branches: vec![(
                    Label::new(&label),
                    None,
                    LocalTypeR::Send {
                        partner: "A".to_string(),
                        branches: vec![(Label::new(&label), None, LocalTypeR::End)],
                    },
                )],
            },
        );

        let global = GlobalType::send(
            roles[0],
            roles[1],
            Label::new(&label),
            GlobalType::send(
                roles[1],
                roles[2],
                Label::new(&label),
                GlobalType::send(
                    roles[2],
                    roles[3],
                    Label::new(&label),
                    GlobalType::send(roles[3], roles[0], Label::new(&label), GlobalType::End),
                ),
            ),
        );
        CodeImage::from_local_types(&local_types, &global)
    }

    fn build_workload_image(mode: WorkloadMode, idx: usize) -> CodeImage {
        match mode {
            WorkloadMode::Disjoint => simple_send_recv_image(&format!("m{idx}")),
            WorkloadMode::Contended => contended_ring_image(idx),
        }
    }

    fn parse_cli() -> (Option<String>, WorkloadMode, RuntimeTuningProfile) {
        let mut args = std::env::args().skip(1);
        let mut output = None;
        let mut workload = WorkloadMode::Disjoint;
        let mut profile = RuntimeTuningProfile::Standard;
        while let Some(arg) = args.next() {
            if arg == "--output" {
                output = args.next();
            } else if arg == "--workload" {
                let value = args.next().unwrap_or_else(|| "disjoint".to_string());
                workload = match value.as_str() {
                    "disjoint" => WorkloadMode::Disjoint,
                    "contended" => WorkloadMode::Contended,
                    _ => WorkloadMode::Disjoint,
                };
            } else if arg == "--tuning-profile" {
                let value = args.next().unwrap_or_else(|| "standard".to_string());
                profile = match value.as_str() {
                    "m1_stress_reference" => RuntimeTuningProfile::M1StressReference,
                    _ => RuntimeTuningProfile::Standard,
                };
            }
        }
        (output, workload, profile)
    }

    fn stable_hash_hex<T: Serialize>(value: &T) -> String {
        let bytes = serde_json::to_vec(value).unwrap_or_else(|_| b"{}".to_vec());
        let digest = DefaultVerificationModel::hash(HashTag::Value, &bytes);
        let mut out = String::with_capacity(digest.0.len() * 2);
        for byte in digest.0 {
            use std::fmt::Write as _;
            let _ = write!(&mut out, "{byte:02x}");
        }
        out
    }
}

#[cfg(feature = "multi-thread")]
fn main() {
    if let Err(err) = app::run() {
        eprintln!("error: {err}");
        std::process::exit(1);
    }
}
