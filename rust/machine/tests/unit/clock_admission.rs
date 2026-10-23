// Included inside each actual backend owner module, with access to its original clock.
use std::sync::atomic::{AtomicUsize, Ordering};
struct CountClockCallbacks(AtomicUsize);
impl EffectHandler for CountClockCallbacks {
    fn handle_effect(&self, request: EffectRequest) -> EffectOutcome {
        self.0.fetch_add(1, Ordering::SeqCst);
        match request.body {
            crate::effect::EffectRequestBody::TopologyEvents { .. } => {
                EffectOutcome::success(crate::effect::EffectResponse::TopologyEvents {
                    events: vec![],
                })
            }
            crate::effect::EffectRequestBody::OutputConditionHint { .. } => {
                EffectOutcome::success(crate::effect::EffectResponse::OutputConditionHint {
                    hint: None,
                })
            }
            _ => panic!("unexpected effect from actual Yield round"),
        }
    }
    fn handle_send(&self, _: &str, _: &str, _: &str, _: &[Value]) -> EffectResult<Value> {
        unreachable!()
    }
    fn handle_recv(
        &self,
        _: &str,
        _: &str,
        _: &str,
        _: &mut Vec<Value>,
        _: &Value,
    ) -> EffectResult<()> {
        unreachable!()
    }
    fn handle_choose(&self, _: &str, _: &str, _: &[String], _: &[Value]) -> EffectResult<String> {
        unreachable!()
    }
    fn step(&self, _: &str, _: &mut Vec<Value>) -> EffectResult<()> {
        unreachable!()
    }
}
fn clock_image() -> CodeImage {
    CodeImage {
        programs: BTreeMap::from([("A".into(), vec![Instr::Yield, Instr::Jump { target: 0 }])]),
        global_type: telltale_types::GlobalType::End,
        local_types: BTreeMap::from([("A".into(), telltale_types::LocalTypeR::End)]),
    }
}
#[test]
fn exhausted_round_refuses_before_actual_callbacks_or_runtime_state_mutation() {
    for duration_exhaustion in [false, true] {
        let mut machine = make_clock_machine();
        machine
            .load_choreography_owned(&clock_image(), "original-clock-owner")
            .unwrap();
        let handler = CountClockCallbacks(AtomicUsize::new(0));
        machine
            .step_round(&handler, 1)
            .expect("real first round populates scheduler and effects");
        let first_tick = machine.clock.tick;
        let first_callbacks = handler.0.load(Ordering::SeqCst);
        if duration_exhaustion {
            machine.clock.time = Duration::MAX;
            machine.clock.tick_duration = Duration::from_nanos(1);
        } else {
            machine.clock.tick = u64::MAX;
        }
        let before = runtime_clock_snapshot(&machine);
        let clock_before = serde_json::to_value(&machine.clock).unwrap();
        let callbacks = handler.0.load(Ordering::SeqCst);
        let observations = original_round_observations(&machine);
        let error = machine
            .step_round(&handler, 1)
            .expect_err("finite round cannot be admitted");
        let expected = if duration_exhaustion {
            crate::clock::ClockExhaustion::Duration
        } else {
            crate::clock::ClockExhaustion::Tick
        };
        let source_matches = std::error::Error::source(&error)
            .and_then(|source| source.downcast_ref::<crate::clock::ClockExhaustion>())
            == Some(&expected);
        let final_callbacks = handler.0.load(Ordering::SeqCst);
        let final_clock = serde_json::to_value(&machine.clock).unwrap();
        let final_state = runtime_clock_snapshot(&machine);
        let final_observations = original_round_observations(&machine);
        settle_clock_machine(machine);
        assert_eq!(first_tick, 1);
        assert!(first_callbacks > 0);
        assert!(
            matches!(&error, ProtocolMachineError::ClockExhausted(actual) if *actual == expected)
        );
        assert!(source_matches);
        assert_eq!(final_callbacks, callbacks);
        assert_eq!(final_clock, clock_before);
        assert_eq!(final_state, before);
        assert_eq!(final_observations, observations);
    }
}
#[test]
fn admitted_round_advances_original_simulated_time_once() {
    let mut machine = make_clock_machine();
    machine
        .load_choreography_owned(&clock_image(), "original-clock-owner")
        .unwrap();
    let handler = CountClockCallbacks(AtomicUsize::new(0));
    let duration = machine.clock.tick_duration;
    machine.step_round(&handler, 1).unwrap();
    let first = (machine.clock.tick, machine.clock.time);
    machine.step_round(&handler, 1).unwrap();
    let second = (machine.clock.tick, machine.clock.time);
    settle_clock_machine(machine);
    assert_eq!(first, (1, duration));
    assert_eq!(second, (2, duration.checked_mul(2).unwrap()));
}
