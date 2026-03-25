//! Lean/Rust parity fixtures for speculation, scheduler, and failure-envelope scenarios.
#![cfg(not(target_arch = "wasm32"))]
#![cfg(feature = "multi-thread")]
#![allow(missing_docs)]

#[allow(dead_code, unreachable_pub)]
#[path = "support/mod.rs"]
mod test_support;

use std::collections::BTreeMap;
use std::sync::atomic::{AtomicBool, Ordering};

use telltale_machine::coroutine::{Fault, Value};
use telltale_machine::model::effects::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
    TopologyPerturbation,
};
use telltale_machine::instr::{ImmValue, Instr};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::ThreadedProtocolMachine;
use telltale_machine::{
    CommunicationReplayMode, EffectDeterminismTier, EnvelopeDiffArtifactV1,
    FailureVisibleDiffClass, SchedulerPermutationClass,
};
use telltale_machine::{
    ObsEvent, ProtocolMachine, ProtocolMachineConfig, ProtocolMachineError, ThreadedRoundSemantics,
};
use telltale_types::{GlobalType, LocalTypeR};
use test_support::{PassthroughHandler, ScenarioSpec};

fn threaded_wave_config() -> ProtocolMachineConfig {
    ProtocolMachineConfig {
        threaded_round_semantics: ThreadedRoundSemantics::WaveParallelExtension,
        ..ProtocolMachineConfig::default()
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
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Str(label.to_string()))
    }

    fn send_decision(&self, input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(input.payload.unwrap_or(Value::Unit)))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> EffectResult<String> {
        match labels.first().cloned() {
            Some(label) => EffectResult::success(label),
            None => EffectResult::failure(EffectFailure::invalid_input("no labels available")),
        }
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn topology_events(&self, _tick: u64) -> EffectResult<Vec<TopologyPerturbation>> {
        if self.emitted.swap(true, Ordering::Relaxed) {
            return EffectResult::success(Vec::new());
        }
        EffectResult::success(vec![
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

#[derive(Debug, Clone, Copy)]
struct OversizedPayloadHandler;

impl EffectHandler for OversizedPayloadHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Str("x".repeat(256)))
    }

    fn send_decision(&self, _input: SendDecisionInput<'_>) -> EffectResult<SendDecision> {
        EffectResult::success(SendDecision::Deliver(Value::Str("x".repeat(256))))
    }

    fn handle_recv(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &mut Vec<Value>,
        _payload: &Value,
    ) -> EffectResult<()> {
        EffectResult::success(())
    }

    fn handle_choose(
        &self,
        _role: &str,
        _partner: &str,
        labels: &[String],
        _state: &[Value],
    ) -> EffectResult<String> {
        match labels.first().cloned() {
            Some(label) => EffectResult::success(label),
            None => EffectResult::failure(EffectFailure::invalid_input("no labels available")),
        }
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }
}

#[test]
fn speculation_fixture_matches_between_cooperative_and_threaded() {
    let cfg = ProtocolMachineConfig {
        speculation_enabled: true,
        ..ProtocolMachineConfig::default()
    };
    let bootstrap = ScenarioSpec::simple("X", "Y", "bootstrap").to_code_image();
    let image = speculation_fixture_image();

    let mut coop = ProtocolMachine::new(cfg.clone());
    coop.load_choreography(&bootstrap)
        .expect("load cooperative bootstrap image");
    let coop_sid = coop
        .load_choreography(&image)
        .expect("load cooperative image");
    coop.run(&PassthroughHandler, 64)
        .expect("cooperative speculation run");

    let mut threaded = ThreadedProtocolMachine::with_workers(cfg, 2);
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
    let mut coop = ProtocolMachine::new(ProtocolMachineConfig::default());
    let mut threaded = ThreadedProtocolMachine::with_workers(threaded_wave_config(), 4);
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
fn communication_replay_sequence_mode_parity_at_concurrency_one() {
    let cfg = ProtocolMachineConfig {
        communication_replay_mode: CommunicationReplayMode::Sequence,
        ..ProtocolMachineConfig::default()
    };
    let image = ScenarioSpec::simple("A", "B", "m-seq").to_code_image();
    let mut coop = ProtocolMachine::new(cfg.clone());
    let mut threaded = ThreadedProtocolMachine::with_workers(
        ProtocolMachineConfig {
            threaded_round_semantics: ThreadedRoundSemantics::WaveParallelExtension,
            ..cfg
        },
        2,
    );
    coop.load_choreography(&image)
        .expect("load cooperative image");
    threaded
        .load_choreography(&image)
        .expect("load threaded image");

    coop.run_concurrent(&PassthroughHandler, 128, 1)
        .expect("cooperative sequence replay run");
    threaded
        .run_concurrent(&PassthroughHandler, 128, 1)
        .expect("threaded sequence replay run");

    assert_eq!(
        coop.canonical_replay_fragment(),
        threaded.canonical_replay_fragment(),
        "sequence replay mode must remain parity-exact at concurrency=1"
    );
}

#[test]
fn payload_size_rejection_parity_at_concurrency_one() {
    let cfg = ProtocolMachineConfig {
        max_payload_bytes: 8,
        ..ProtocolMachineConfig::default()
    };
    let image = ScenarioSpec::simple("A", "B", "oversized").to_code_image();
    let mut coop = ProtocolMachine::new(cfg.clone());
    let mut threaded = ThreadedProtocolMachine::with_workers(
        ProtocolMachineConfig {
            threaded_round_semantics: ThreadedRoundSemantics::WaveParallelExtension,
            ..cfg
        },
        2,
    );
    coop.load_choreography(&image)
        .expect("load cooperative image");
    threaded
        .load_choreography(&image)
        .expect("load threaded image");

    let coop_err = coop
        .run_concurrent(&OversizedPayloadHandler, 128, 1)
        .expect_err("cooperative run should reject oversized payload");
    let threaded_err = threaded
        .run_concurrent(&OversizedPayloadHandler, 128, 1)
        .expect_err("threaded run should reject oversized payload");

    assert!(
        matches!(
            coop_err,
            ProtocolMachineError::Fault {
                fault: Fault::TypeViolation { ref message, .. },
                ..
            } if message.contains("exceeds max_payload_bytes")
        ),
        "cooperative oversized payload error did not match payload-size rejection contract"
    );
    assert!(
        matches!(
            threaded_err,
            ProtocolMachineError::Fault {
                fault: Fault::TypeViolation { ref message, .. },
                ..
            } if message.contains("exceeds max_payload_bytes")
        ),
        "threaded oversized payload error did not match payload-size rejection contract"
    );
}

#[test]
fn envelope_bounded_parity_holds_for_n_gt_1() {
    let images: Vec<_> = (0..8)
        .map(|i| ScenarioSpec::simple("A", "B", &format!("m{i}")).to_code_image())
        .collect();
    let cfg = ProtocolMachineConfig {
        effect_determinism_tier: EffectDeterminismTier::EnvelopeBoundedNondeterministic,
        threaded_round_semantics: ThreadedRoundSemantics::WaveParallelExtension,
        ..ProtocolMachineConfig::default()
    };
    let mut coop = ProtocolMachine::new(cfg.clone());
    let mut threaded = ThreadedProtocolMachine::with_workers(cfg.clone(), 4);
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
    let cfg = ProtocolMachineConfig {
        effect_determinism_tier: EffectDeterminismTier::EnvelopeBoundedNondeterministic,
        threaded_round_semantics: ThreadedRoundSemantics::WaveParallelExtension,
        ..ProtocolMachineConfig::default()
    };
    let mut coop = ProtocolMachine::new(cfg.clone());
    let mut threaded = ThreadedProtocolMachine::with_workers(cfg.clone(), 4);
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
    let mut coop = ProtocolMachine::new(ProtocolMachineConfig::default());
    coop.load_choreography(&image)
        .expect("load cooperative image");
    coop.run_concurrent(&handler, 64, 1)
        .expect("cooperative run");

    let mut threaded = ThreadedProtocolMachine::with_workers(threaded_wave_config(), 2);
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
