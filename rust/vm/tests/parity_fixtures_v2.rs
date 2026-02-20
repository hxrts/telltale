#![cfg(not(target_arch = "wasm32"))]
#![cfg(feature = "multi-thread")]
#![allow(missing_docs)]
//! Lean/Rust parity fixtures for speculation, scheduler, and failure-envelope scenarios.

#[allow(dead_code, unreachable_pub)]
mod helpers;

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};

use helpers::{PassthroughHandler, ScenarioSpec};
use telltale_types::{GlobalType, LocalTypeR};
use telltale_vm::coroutine::Value;
use telltale_vm::effect::{EffectHandler, SendDecision, SendDecisionInput, TopologyPerturbation};
use telltale_vm::instr::{ImmValue, Instr};
use telltale_vm::loader::CodeImage;
use telltale_vm::threaded::ThreadedVM;
use telltale_vm::vm::{ObsEvent, ThreadedRoundSemantics, VMConfig, VM};
use telltale_vm::{
    EffectDeterminismTier, EnvelopeDiffArtifactV1, FailureVisibleDiffClass,
    SchedulerPermutationClass,
};

fn threaded_wave_config() -> VMConfig {
    VMConfig {
        threaded_round_semantics: ThreadedRoundSemantics::WaveParallelExtension,
        ..VMConfig::default()
    }
}

fn speculation_fixture_image() -> CodeImage {
    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);

    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![
            Instr::Set {
                dst: 1,
                val: ImmValue::Nat(7),
            },
            Instr::Fork { ghost: 1 },
            Instr::Join,
            Instr::Fork { ghost: 1 },
            Instr::Abort,
            Instr::Halt,
        ],
    );
    CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    }
}

#[derive(Debug)]
struct TopologyOnceHandler {
    emitted: AtomicBool,
}

impl TopologyOnceHandler {
    fn new() -> Self {
        Self {
            emitted: AtomicBool::new(false),
        }
    }
}

impl EffectHandler for TopologyOnceHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        label: &str,
        _state: &[Value],
    ) -> Result<Value, String> {
        Ok(Value::Str(label.to_string()))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> Result<SendDecision, String> {
        Ok(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)))
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

    fn topology_events(&self, _tick: u64) -> Result<Vec<TopologyPerturbation>, String> {
        if self.emitted.swap(true, Ordering::Relaxed) {
            return Ok(Vec::new());
        }
        Ok(vec![
            TopologyPerturbation::Crash {
                site: "A".to_string(),
            },
            TopologyPerturbation::Partition {
                from: "A".to_string(),
                to: "B".to_string(),
            },
        ])
    }
}

#[test]
fn speculation_fixture_matches_between_cooperative_and_threaded() {
    let cfg = VMConfig {
        speculation_enabled: true,
        ..VMConfig::default()
    };
    let bootstrap = ScenarioSpec::simple("X", "Y", "bootstrap").to_code_image();
    let image = speculation_fixture_image();

    let mut coop = VM::new(cfg.clone());
    coop.load_choreography(&bootstrap)
        .expect("load cooperative bootstrap image");
    let coop_sid = coop
        .load_choreography(&image)
        .expect("load cooperative image");
    coop.run(&PassthroughHandler, 64)
        .expect("cooperative speculation run");

    let mut threaded = ThreadedVM::with_workers(cfg, 2);
    threaded
        .load_choreography(&bootstrap)
        .expect("load threaded bootstrap image");
    let threaded_sid = threaded
        .load_choreography(&image)
        .expect("load threaded image");
    threaded
        .run_concurrent(&PassthroughHandler, 64, 2)
        .expect("threaded speculation run");

    let coop_spec_events: Vec<_> = coop
        .trace()
        .iter()
        .filter(|event| {
            matches!(
                event,
                ObsEvent::Forked { .. } | ObsEvent::Joined { .. } | ObsEvent::Aborted { .. }
            )
        })
        .map(|event| match event {
            ObsEvent::Forked { session, ghost, .. } => ("forked", *session, Some(*ghost)),
            ObsEvent::Joined { session, .. } => ("joined", *session, None),
            ObsEvent::Aborted { session, .. } => ("aborted", *session, None),
            _ => unreachable!("filtered to speculation events"),
        })
        .collect();
    let threaded_spec_events: Vec<_> = threaded
        .trace()
        .iter()
        .filter(|event| {
            matches!(
                event,
                ObsEvent::Forked { .. } | ObsEvent::Joined { .. } | ObsEvent::Aborted { .. }
            )
        })
        .map(|event| match event {
            ObsEvent::Forked { session, ghost, .. } => ("forked", *session, Some(*ghost)),
            ObsEvent::Joined { session, .. } => ("joined", *session, None),
            ObsEvent::Aborted { session, .. } => ("aborted", *session, None),
            _ => unreachable!("filtered to speculation events"),
        })
        .collect();

    assert_eq!(coop_spec_events, threaded_spec_events);
    assert!(
        threaded_spec_events
            .iter()
            .all(|(_, session, _)| *session == threaded_sid),
        "threaded speculation events must use the concrete session id"
    );
    assert!(
        coop_spec_events
            .iter()
            .all(|(_, session, _)| *session == coop_sid),
        "cooperative speculation events must use the concrete session id"
    );
}

#[test]
fn canonical_parity_is_exact_at_concurrency_one() {
    let images = vec![
        ScenarioSpec::simple("A", "B", "m1").to_code_image(),
        ScenarioSpec::simple("A", "B", "m2").to_code_image(),
        ScenarioSpec::simple("A", "B", "m3").to_code_image(),
    ];
    let mut coop = VM::new(VMConfig::default());
    let mut threaded = ThreadedVM::with_workers(threaded_wave_config(), 4);
    for image in &images {
        coop.load_choreography(image)
            .expect("load cooperative image");
        threaded
            .load_choreography(image)
            .expect("load threaded image");
    }

    coop.run_concurrent(&PassthroughHandler, 256, 1)
        .expect("cooperative n=1 run");
    threaded
        .run_concurrent(&PassthroughHandler, 256, 1)
        .expect("threaded n=1 run");

    assert_eq!(
        coop.canonical_replay_fragment(),
        threaded.canonical_replay_fragment(),
        "concurrency=1 must remain exact-match canonical parity"
    );
}

#[test]
fn envelope_bounded_parity_holds_for_n_gt_1() {
    let images: Vec<_> = (0..8)
        .map(|i| ScenarioSpec::simple("A", "B", &format!("m{i}")).to_code_image())
        .collect();
    let cfg = VMConfig {
        effect_determinism_tier: EffectDeterminismTier::EnvelopeBoundedNondeterministic,
        threaded_round_semantics: ThreadedRoundSemantics::WaveParallelExtension,
        ..VMConfig::default()
    };
    let mut coop = VM::new(cfg.clone());
    let mut threaded = ThreadedVM::with_workers(cfg.clone(), 4);
    for image in &images {
        coop.load_choreography(image)
            .expect("load cooperative image");
        threaded
            .load_choreography(image)
            .expect("load threaded image");
    }

    coop.run_concurrent(&PassthroughHandler, 512, 1)
        .expect("cooperative baseline run");
    threaded
        .run_concurrent(&PassthroughHandler, 512, 4)
        .expect("threaded n>1 run");

    let baseline = coop.canonical_replay_fragment();
    let candidate = threaded.canonical_replay_fragment();
    let artifact = EnvelopeDiffArtifactV1::from_replay_fragments(
        "cooperative",
        "threaded",
        &baseline,
        &candidate,
        1,
        threaded.contention_metrics().max_wave_width,
        4,
        cfg.effect_determinism_tier,
    );

    assert!(
        matches!(
            artifact.envelope_diff.scheduler_permutation_class,
            SchedulerPermutationClass::Exact
                | SchedulerPermutationClass::SessionNormalizedPermutation
        ),
        "n>1 threaded parity must remain within declared scheduler envelope"
    );
    assert!(
        artifact
            .envelope_diff
            .wave_width_bound
            .within_declared_bound(),
        "threaded wave width must remain within declared envelope bound"
    );
    assert!(matches!(
        artifact.envelope_diff.failure_visible_diff_class,
        FailureVisibleDiffClass::Exact | FailureVisibleDiffClass::EnvelopeBounded
    ));
}

#[test]
fn envelope_bounded_parity_detects_wave_width_bound_violation() {
    let images: Vec<_> = (0..8)
        .map(|i| ScenarioSpec::simple("A", "B", &format!("m{i}")).to_code_image())
        .collect();
    let cfg = VMConfig {
        effect_determinism_tier: EffectDeterminismTier::EnvelopeBoundedNondeterministic,
        threaded_round_semantics: ThreadedRoundSemantics::WaveParallelExtension,
        ..VMConfig::default()
    };
    let mut coop = VM::new(cfg.clone());
    let mut threaded = ThreadedVM::with_workers(cfg.clone(), 4);
    for image in &images {
        coop.load_choreography(image)
            .expect("load cooperative image");
        threaded
            .load_choreography(image)
            .expect("load threaded image");
    }
    coop.run_concurrent(&PassthroughHandler, 512, 1)
        .expect("cooperative baseline run");
    threaded
        .run_concurrent(&PassthroughHandler, 512, 4)
        .expect("threaded n>1 run");

    let artifact = EnvelopeDiffArtifactV1::from_replay_fragments(
        "cooperative",
        "threaded",
        &coop.canonical_replay_fragment(),
        &threaded.canonical_replay_fragment(),
        1,
        threaded.contention_metrics().max_wave_width,
        1,
        cfg.effect_determinism_tier,
    );

    assert!(
        artifact
            .envelope_diff
            .wave_width_bound
            .candidate_max_wave_width
            > 1,
        "fixture requires multi-wave execution to validate bound rejection"
    );
    assert!(
        !artifact
            .envelope_diff
            .wave_width_bound
            .within_declared_bound(),
        "under-declared bound must be reported as a violation"
    );
}

#[test]
fn failure_envelope_fixture_matches_cross_runtime() {
    let image = ScenarioSpec::simple("A", "B", "m").to_code_image();
    let handler = TopologyOnceHandler::new();
    let mut coop = VM::new(VMConfig::default());
    coop.load_choreography(&image)
        .expect("load cooperative image");
    coop.run_concurrent(&handler, 64, 1)
        .expect("cooperative run");

    let mut threaded = ThreadedVM::with_workers(threaded_wave_config(), 2);
    threaded
        .load_choreography(&image)
        .expect("load threaded image");
    threaded
        .run_concurrent(&handler, 64, 2)
        .expect("threaded run");

    let artifact = EnvelopeDiffArtifactV1::from_replay_fragments(
        "cooperative",
        "threaded",
        &coop.canonical_replay_fragment(),
        &threaded.canonical_replay_fragment(),
        1,
        threaded.contention_metrics().max_wave_width,
        2,
        EffectDeterminismTier::StrictDeterministic,
    );

    assert!(matches!(
        artifact.envelope_diff.failure_visible_diff_class,
        FailureVisibleDiffClass::Exact | FailureVisibleDiffClass::EnvelopeBounded
    ));
}
