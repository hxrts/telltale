#![allow(clippy::expect_used)]
//! Composition stress tests: concurrent protocol execution and runtime metrics.

use std::time::Instant;

use telltale_types::{GlobalType, Label, LocalTypeR};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::EffectHandler;
use telltale_vm::loader::CodeImage;
use telltale_vm::threaded::{ContentionMetrics, ThreadedVM};
use telltale_vm::vm::{StepResult, VMConfig};

#[derive(Debug, Clone, Copy)]
struct StressHandler;

impl EffectHandler for StressHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        Ok(Value::Label(label.to_string()))
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

#[derive(Debug, Clone)]
struct StressReport {
    rounds: usize,
    total_duration_ns: u128,
    p95_step_ns: u128,
    p99_step_ns: u128,
    throughput_events_per_sec: f64,
    peak_rss_bytes: Option<u64>,
    bytes_per_protocol: Option<u64>,
    bytes_per_session: Option<u64>,
    bytes_per_coroutine: Option<u64>,
    metrics: ContentionMetrics,
    faults: usize,
}

fn simple_image(label: &str) -> CodeImage {
    let mut local_types = std::collections::BTreeMap::new();
    local_types.insert(
        "A".to_string(),
        LocalTypeR::send("B", Label::new(label), LocalTypeR::End),
    );
    local_types.insert(
        "B".to_string(),
        LocalTypeR::recv("A", Label::new(label), LocalTypeR::End),
    );
    let global = GlobalType::send("A", "B", Label::new(label), GlobalType::End);
    CodeImage::from_local_types(&local_types, &global)
}

fn percentile_ns(samples: &[u128], p: f64) -> u128 {
    if samples.is_empty() {
        return 0;
    }
    let mut sorted = samples.to_vec();
    sorted.sort_unstable();
    let idx = ((sorted.len() as f64 - 1.0) * p).round() as usize;
    sorted[idx]
}

#[cfg(target_os = "linux")]
fn current_rss_bytes() -> Option<u64> {
    let status = std::fs::read_to_string("/proc/self/status").ok()?;
    for line in status.lines() {
        if let Some(rest) = line.strip_prefix("VmRSS:") {
            let kb = rest.split_whitespace().next()?.parse::<u64>().ok()?;
            return Some(kb.saturating_mul(1024));
        }
    }
    None
}

#[cfg(not(target_os = "linux"))]
fn current_rss_bytes() -> Option<u64> {
    None
}

fn run_stress(protocols: usize, workers: usize) -> StressReport {
    let mut vm = ThreadedVM::with_workers(VMConfig::default(), workers);
    for i in 0..protocols {
        vm.load_choreography(&simple_image(&format!("m{i}")))
            .expect("load choreography");
    }

    let mut durations = Vec::new();
    let mut peak_rss = current_rss_bytes().unwrap_or(0);
    let mut rounds = 0usize;
    let max_rounds = 4096usize;
    let handler = StressHandler;
    for _ in 0..max_rounds {
        rounds += 1;
        let t0 = Instant::now();
        let outcome = vm
            .step_round(&handler, workers.max(1))
            .expect("threaded step");
        durations.push(t0.elapsed().as_nanos());
        if let Some(rss) = current_rss_bytes() {
            peak_rss = peak_rss.max(rss);
        }

        match outcome {
            StepResult::AllDone => break,
            StepResult::Continue => {}
            StepResult::Stuck => panic!("stress workload became stuck"),
        }
    }

    let total_duration_ns: u128 = durations.iter().sum();
    let trace_len = vm.trace().len() as f64;
    let throughput = if total_duration_ns == 0 {
        0.0
    } else {
        trace_len / (total_duration_ns as f64 / 1_000_000_000.0)
    };

    let protocols_u64 = protocols as u64;
    let sessions_u64 = protocols as u64;
    let coroutines_u64 = (protocols * 2) as u64;
    let peak = if peak_rss == 0 { None } else { Some(peak_rss) };

    StressReport {
        rounds,
        total_duration_ns,
        p95_step_ns: percentile_ns(&durations, 0.95),
        p99_step_ns: percentile_ns(&durations, 0.99),
        throughput_events_per_sec: throughput,
        peak_rss_bytes: peak,
        bytes_per_protocol: peak.map(|rss| rss / protocols_u64.max(1)),
        bytes_per_session: peak.map(|rss| rss / sessions_u64.max(1)),
        bytes_per_coroutine: peak.map(|rss| rss / coroutines_u64.max(1)),
        metrics: vm.contention_metrics().clone(),
        faults: vm
            .trace()
            .iter()
            .filter(|ev| matches!(ev, telltale_vm::vm::ObsEvent::Faulted { .. }))
            .count(),
    }
}

#[test]
fn composed_workload_reports_memory_latency_and_safety_metrics() {
    let report = run_stress(64, 8);
    assert_eq!(report.faults, 0, "stress run should not fault");
    assert!(report.rounds > 0);
    assert!(report.total_duration_ns > 0);
    assert!(report.p95_step_ns > 0);
    assert!(
        report.p99_step_ns >= report.p95_step_ns,
        "p99 latency should not be below p95"
    );
    assert!(
        report.throughput_events_per_sec > 0.0,
        "throughput should be positive"
    );
    assert!(report.metrics.max_ready_queue_depth > 0);
    assert!(
        report.metrics.max_wave_width > 1,
        "multi-worker run should execute multi-lane waves"
    );

    if let Some(peak_rss) = report.peak_rss_bytes {
        assert!(peak_rss > 0);
        assert!(report.bytes_per_protocol.unwrap_or(0) > 0);
        assert!(report.bytes_per_session.unwrap_or(0) > 0);
        assert!(report.bytes_per_coroutine.unwrap_or(0) > 0);
    }
}

#[test]
fn composed_workload_scales_with_lane_count_proxy() {
    let single = run_stress(64, 1);
    let multi = run_stress(64, 8);

    assert!(
        multi.rounds <= single.rounds,
        "multi-lane run should not require more rounds than single-lane"
    );
    assert!(
        multi.metrics.max_wave_width > single.metrics.max_wave_width,
        "multi-lane run should increase parallel wave width"
    );
}

#[test]
fn tier1_throughput_budget_stays_within_15_percent() {
    let single = run_stress(64, 1);
    let multi = run_stress(64, 8);
    assert!(
        single.throughput_events_per_sec > 0.0 && multi.throughput_events_per_sec > 0.0,
        "throughput samples must be positive"
    );
    let ratio = multi.throughput_events_per_sec / single.throughput_events_per_sec;
    assert!(
        ratio >= 0.85,
        "throughput regression exceeded 15% budget: multi/single={ratio:.3}"
    );
}
