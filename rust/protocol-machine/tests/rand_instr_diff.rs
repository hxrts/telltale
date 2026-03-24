//! Differential randomized instruction checks between deterministic ProtocolMachine backends.
#![cfg(all(not(target_arch = "wasm32"), feature = "multi-thread"))]
#![allow(missing_docs)]

use std::collections::BTreeMap;

use telltale_types::{GlobalType, LocalTypeR};
use telltale_protocol_machine::coroutine::Value;
use telltale_protocol_machine::effect::{
    EffectFailure, EffectHandler, EffectResult, SendDecision, SendDecisionInput,
};
use telltale_protocol_machine::instr::{ImmValue, Instr};
use telltale_protocol_machine::loader::CodeImage;
use telltale_protocol_machine::ThreadedProtocolMachine;
use telltale_protocol_machine::{ObsEvent, ProtocolMachine, ProtocolMachineConfig};

#[derive(Debug, Clone, Copy)]
struct DeterministicNoopHandler;

impl EffectHandler for DeterministicNoopHandler {
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
        match labels.first().cloned() {
            Some(label) => EffectResult::success(label),
            None => EffectResult::failure(EffectFailure::invalid_input("no labels")),
        }
    }

    fn step(&self, _role: &str, _state: &mut Vec<Value>) -> EffectResult<()> {
        EffectResult::success(())
    }
}

fn lcg_next(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *state
}

fn build_random_program(seed: u64, num_regs: u16) -> Vec<Instr> {
    let mut rng = seed;
    let mut program = Vec::new();
    let body_len = 6 + usize::try_from(lcg_next(&mut rng) % 8).expect("mod 8 fits usize");
    for _ in 0..body_len {
        match lcg_next(&mut rng) % 3 {
            0 => {
                let dst = u16::try_from(lcg_next(&mut rng) % u64::from(num_regs))
                    .expect("mod num_regs fits u16");
                let val = lcg_next(&mut rng) % 1000;
                program.push(Instr::Set {
                    dst,
                    val: ImmValue::Nat(val),
                });
            }
            1 => {
                let dst = u16::try_from(lcg_next(&mut rng) % u64::from(num_regs))
                    .expect("mod num_regs fits u16");
                let src = u16::try_from(lcg_next(&mut rng) % u64::from(num_regs))
                    .expect("mod num_regs fits u16");
                program.push(Instr::Move { dst, src });
            }
            _ => {
                program.push(Instr::Yield);
            }
        }
    }
    program.push(Instr::Halt);
    program
}

fn random_lane_image(seed: u64, num_regs: u16) -> CodeImage {
    let roles = ["A", "B", "C", "D"];
    let mut programs = BTreeMap::new();
    let mut local_types = BTreeMap::new();

    for (idx, role) in roles.iter().enumerate() {
        let idx_u64 = u64::try_from(idx).expect("index fits u64");
        programs.insert(
            (*role).to_string(),
            build_random_program(seed + idx_u64 * 17, num_regs),
        );
        local_types.insert((*role).to_string(), LocalTypeR::End);
    }

    CodeImage {
        programs,
        global_type: GlobalType::End,
        local_types,
    }
}

fn observation_signature(trace: &[ObsEvent]) -> Vec<String> {
    trace
        .iter()
        .filter_map(|ev| match ev {
            ObsEvent::Opened { session, roles, .. } => {
                Some(format!("opened:{session}:{}", roles.join(",")))
            }
            ObsEvent::Halted { coro_id, .. } => Some(format!("halted:{coro_id}")),
            _ => None,
        })
        .collect()
}

#[test]
fn randomized_instruction_corpus_has_cross_target_observational_equivalence() {
    let cfg = ProtocolMachineConfig {
        num_registers: 16,
        ..ProtocolMachineConfig::default()
    };

    for seed in 0_u64..64 {
        let image = random_lane_image(seed, cfg.num_registers);

        let mut coop = ProtocolMachine::new(cfg.clone());
        coop.load_choreography(&image)
            .expect("load cooperative image");
        coop.run(&DeterministicNoopHandler, 256)
            .expect("run cooperative ProtocolMachine");

        let mut threaded = ThreadedProtocolMachine::with_workers(cfg.clone(), 4);
        threaded
            .load_choreography(&image)
            .expect("load threaded image");
        threaded
            .run(&DeterministicNoopHandler, 256)
            .expect("run threaded ProtocolMachine");

        assert_eq!(
            observation_signature(&coop.canonical_replay_fragment().obs_trace),
            observation_signature(&threaded.canonical_replay_fragment().obs_trace),
            "cross-target mismatch for seed {seed}"
        );
    }
}
