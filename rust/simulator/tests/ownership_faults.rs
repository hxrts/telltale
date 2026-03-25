//! Simulator fault scenarios covering ownership handoff and owner failure behavior.

use std::collections::BTreeMap;

use telltale_machine::buffer::EnqueueResult;
use telltale_machine::coroutine::Value;
use telltale_machine::instr::{ImmValue, Instr};
use telltale_machine::model::effects::{
    EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_machine::runtime::loader::CodeImage;
use telltale_machine::{ObsEvent, ProtocolMachine, ProtocolMachineConfig, StepResult};
use telltale_simulator::fault::{Fault, FaultInjector, FaultSchedule, ScheduledFault, Trigger};
use telltale_simulator::rng::SimRng;
use telltale_types::{GlobalType, LocalTypeR};

#[derive(Debug, Clone, Copy)]
struct NoopHandler;

impl EffectHandler for NoopHandler {
    fn handle_send(
        &self,
        _role: &str,
        _partner: &str,
        _label: &str,
        _state: &[Value],
    ) -> EffectResult<Value> {
        EffectResult::success(Value::Unit)
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
        EffectResult::success(
            labels
                .first()
                .cloned()
                .expect("labels should contain at least one branch"),
        )
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }
}

fn transfer_image() -> CodeImage {
    let mut local_types = BTreeMap::new();
    local_types.insert("A".to_string(), LocalTypeR::End);
    local_types.insert("B".to_string(), LocalTypeR::End);

    let mut programs = BTreeMap::new();
    programs.insert(
        "A".to_string(),
        vec![
            Instr::Set {
                dst: 1,
                val: ImmValue::Nat(1),
            },
            Instr::Transfer {
                endpoint: 0,
                target: 1,
                bundle: 2,
            },
            Instr::Halt,
        ],
    );
    programs.insert("B".to_string(), vec![Instr::Halt]);

    CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    }
}

fn run_faulted_transfer(schedule: FaultSchedule, max_rounds: usize) -> ProtocolMachine {
    let mut machine = ProtocolMachine::new(ProtocolMachineConfig::default());
    machine
        .load_choreography(&transfer_image())
        .expect("load transfer fixture");
    let fault = FaultInjector::new(NoopHandler, schedule, SimRng::new(7));

    for logical_step in 1..=max_rounds {
        let next_tick = machine.clock().tick + 1;
        fault
            .tick(
                next_tick,
                u64::try_from(logical_step).expect("logical step fits in u64"),
                machine.trace(),
            )
            .expect("advance fault schedule");
        fault
            .deliver(next_tick, |sid, from, to, value| {
                machine
                    .inject_message(sid, from, to, value)
                    .map_err(|err| err.to_string())
                    .map(|result| match result {
                        EnqueueResult::Ok => EnqueueResult::Ok,
                        EnqueueResult::Dropped => EnqueueResult::Dropped,
                        EnqueueResult::WouldBlock => EnqueueResult::WouldBlock,
                        EnqueueResult::Full => EnqueueResult::Full,
                    })
            })
            .expect("deliver delayed messages");
        machine.set_paused_roles(
            &fault
                .crashed_roles()
                .expect("read currently crashed simulator roles"),
        );
        match machine
            .step_round(&fault, 1)
            .expect("step transfer fixture")
        {
            StepResult::Continue => {}
            StepResult::AllDone | StepResult::Stuck => break,
        }
    }

    machine
}

#[test]
fn ownership_owner_failure_before_handoff_emits_no_transfer_event() {
    let schedule = FaultSchedule {
        faults: vec![ScheduledFault {
            fault: Fault::NodeCrash {
                role: "A".to_string(),
                duration: None,
            },
            trigger: Trigger::AtTick(1),
            duration: None,
        }],
        max_concurrent: 1,
    };
    let machine = run_faulted_transfer(schedule, 8);

    assert!(
        machine
            .trace()
            .iter()
            .all(|event| !matches!(event, ObsEvent::Transferred { .. })),
        "crashing the current owner before the transfer should suppress handoff observables"
    );
    assert!(
        machine.semantic_objects().semantic_handoffs.is_empty(),
        "owner crash before transfer should leave no semantic handoff state"
    );
}

#[test]
fn ownership_handoff_race_with_target_crash_keeps_transfer_observable() {
    let schedule = FaultSchedule {
        faults: vec![ScheduledFault {
            fault: Fault::NodeCrash {
                role: "B".to_string(),
                duration: None,
            },
            trigger: Trigger::AtTick(1),
            duration: None,
        }],
        max_concurrent: 1,
    };
    let machine = run_faulted_transfer(schedule, 8);

    assert_eq!(
        machine
            .trace()
            .iter()
            .filter(|event| matches!(event, ObsEvent::Transferred { .. }))
            .count(),
        1,
        "target crash should not erase the explicit ownership handoff observable"
    );
    assert_eq!(
        machine.semantic_objects().semantic_handoffs.len(),
        1,
        "simulator ownership race should preserve one semantic handoff artifact"
    );
}
