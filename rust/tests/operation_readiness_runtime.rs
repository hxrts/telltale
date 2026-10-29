//! Actual source parent and original registry-backed readiness child composition.
use std::collections::BTreeMap;
use std::num::NonZeroU64;
use std::sync::Mutex;
use telltale_machine::model::effects::{EffectHandler, EffectResult};
use telltale_machine::nominal_command::{
    NominalCommandReply, NominalCommandRequest, NominalCommandValue,
};
use telltale_machine::semantic_objects::{OperationPhase, OutstandingEffectStatus};
use telltale_machine::{ProtocolMachine, ProtocolMachineConfig};

const SOURCE: &str = r#"
effect Host
  authoritative ready : Unit -> Result String ReadinessWitness
  {
    class : authoritative
    progress : may_block
    region : session
    agreement_use : forbidden
    reentrancy : allow
  }
agreement_profile Selected
  visibility immediate
  rule no_agreement
  usable_at none
  finalized_at none
  evidence witness
operation Flow at A progress FlowProgress within bounded agreement Selected =
  begin Flow
  authoritative let result at A = check Host.ready()
  case result of
    | Ok(value) =>
        A -> B : Ready
        await Flow
        resolve Flow as Success
    | Err(reason) =>
        A -> B : Denied
        await Flow
        resolve Flow as Failure
protocol Joint uses Host =
  roles A, B
  A -> B : Start
"#;

#[derive(Default)]
struct OriginalProvider {
    calls: Mutex<Vec<u64>>,
    witness: Mutex<Option<telltale_types::ReadinessWitness>>,
}
impl EffectHandler for OriginalProvider {
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[telltale_machine::coroutine::Value],
    ) -> EffectResult<telltale_machine::coroutine::Value> {
        super::NoopHandler.handle_send(role, partner, label, state)
    }
    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<telltale_machine::coroutine::Value>,
        payload: &telltale_machine::coroutine::Value,
    ) -> EffectResult<()> {
        super::NoopHandler.handle_recv(role, partner, label, state, payload)
    }
    fn handle_choose(
        &self,
        role: &str,
        partner: &str,
        labels: &[String],
        state: &[telltale_machine::coroutine::Value],
    ) -> EffectResult<String> {
        super::NoopHandler.handle_choose(role, partner, labels, state)
    }
    fn step(&self, _: &str, _: &mut Vec<telltale_machine::coroutine::Value>) -> EffectResult<()> {
        panic!("actual readiness must use typed callback")
    }
    fn handle_nominal_command(
        &self,
        request: &NominalCommandRequest,
    ) -> EffectResult<NominalCommandReply> {
        self.calls
            .lock()
            .expect("actual callback")
            .push(request.invocation);
        match self.witness.lock().expect("resident returned data").clone() {
            None => EffectResult::blocked(),
            Some(witness) => EffectResult::success(NominalCommandReply {
                invocation: request.invocation,
                result: Ok(NominalCommandValue::Readiness(witness)),
            }),
        }
    }
}

macro_rules! joint_backend {
    ($module:ident, $make:expr, $dispose:expr) => {
        mod $module {
            use super::*;
            #[test]
            fn original_parent_cannot_resolve_an_output_refused_readiness_child() {
                let image = telltale::compile_operation_lifecycle(
                    SOURCE,
                    "Flow",
                    &BTreeMap::from([(
                        "bounded".into(),
                        NonZeroU64::new(64).expect("original SimClock window"),
                    )]),
                )
                .expect("actual joint source");
                let mut config = ProtocolMachineConfig::default();
                config.output_condition_policy =
                    telltale_machine::model::output_condition::OutputConditionPolicy::DenyAll;
                let mut machine = ($make)(config);
                let owner = machine
                    .load_choreography_owned(&image, "original-owner")
                    .expect("original owner");
                let witness = owner
                    .issue_readiness_witness(&mut machine, "Host.ready")
                    .expect("actual issuer");
                let provider = OriginalProvider {
                    calls: Mutex::new(Vec::new()),
                    witness: Mutex::new(Some(witness.clone())),
                };
                let outcome = machine.run(&provider, 64);
                let after = machine.semantic_objects();
                let unconsumed = owner.consume_readiness_witness(&mut machine, &witness);
                let calls = provider
                    .calls
                    .lock()
                    .expect("original callback count")
                    .len();
                ($dispose)(machine);
                assert!(outcome.is_err(), "real output gate refused");
                assert_eq!(calls, 1);
                assert!(
                    unconsumed.is_ok(),
                    "output refusal cannot spend original witness"
                );
                let parent = after
                    .operation_instances
                    .iter()
                    .find(|op| op.operation_id.starts_with("operation:"))
                    .expect("actual Begin");
                assert_ne!(parent.phase, OperationPhase::Succeeded);
                let child = after
                    .outstanding_effects
                    .iter()
                    .find(|effect| effect.effect_kind == "nominal_command")
                    .expect("actual child");
                assert_eq!(parent.effect_ids, vec![child.effect_id]);
                assert_ne!(parent.operation_id, child.operation_id);
                assert_ne!(child.status, OutstandingEffectStatus::Succeeded);
            }

            #[test]
            fn actual_parent_and_readiness_child_keep_original_identity_until_resolution() {
                let image = telltale::compile_operation_lifecycle(
                    SOURCE,
                    "Flow",
                    &BTreeMap::from([(
                        "bounded".into(),
                        NonZeroU64::new(64).expect("original SimClock window"),
                    )]),
                )
                .expect("actual source Begin, readiness child, Await and Resolve");
                let mut machine = ($make)(ProtocolMachineConfig::default());
                let owner = machine
                    .load_choreography_owned(&image, "original-owner")
                    .expect("original loader owner");
                let provider = OriginalProvider::default();
                for _ in 0..16 {
                    machine
                        .step_round(&provider, 1)
                        .expect("actual original round");
                    if !provider.calls.lock().expect("calls").is_empty() {
                        break;
                    }
                }
                let before = machine.semantic_objects();
                let parent = before
                    .operation_instances
                    .iter()
                    .find(|op| op.operation_id.starts_with("operation:"))
                    .expect("actual Begin")
                    .clone();
                let child = before
                    .outstanding_effects
                    .iter()
                    .find(|effect| effect.effect_kind == "nominal_command")
                    .expect("actual child")
                    .clone();
                let witness = owner
                    .issue_readiness_witness(&mut machine, "Host.ready")
                    .expect("original owner between rounds");
                *provider.witness.lock().expect("same callback result") = Some(witness.clone());
                let outcome = machine.run(&provider, 64);
                let after = machine.semantic_objects();
                let calls = provider.calls.lock().expect("actual callback IDs").clone();
                let repeated = owner.consume_readiness_witness(&mut machine, &witness);
                ($dispose)(machine);
                assert_eq!(
                    outcome.expect("same parent and child"),
                    telltale_machine::RunStatus::AllDone
                );
                assert_eq!(parent.effect_ids, vec![child.effect_id]);
                assert_ne!(
                    parent.operation_id, child.operation_id,
                    "shared child membership is not operation identity"
                );
                assert_eq!(child.status, OutstandingEffectStatus::Blocked);
                assert_eq!(child.completed_at_tick, None);
                assert_eq!(calls, vec![child.effect_id, child.effect_id]);
                let terminal = after
                    .operation_instances
                    .iter()
                    .find(|op| op.operation_id == parent.operation_id)
                    .expect("same parent");
                assert_eq!(terminal.phase, OperationPhase::Succeeded);
                assert_eq!(terminal.effect_ids, parent.effect_ids);
                let settled = after
                    .outstanding_effects
                    .iter()
                    .find(|effect| effect.effect_id == child.effect_id)
                    .expect("same child");
                assert_eq!(settled.status, OutstandingEffectStatus::Succeeded);
                assert_eq!(settled.ordering_key, child.ordering_key);
                assert!(settled
                    .completed_at_tick
                    .is_some_and(|tick| tick > child.ordering_key));
                assert!(matches!(
                    repeated,
                    Err(telltale_machine::OwnershipError::WitnessConsumed { .. })
                ));
            }
        }
    };
}
joint_backend!(cooperative, ProtocolMachine::new, |_: ProtocolMachine| {});
#[cfg(all(feature = "multi-thread", not(target_arch = "wasm32")))]
joint_backend!(
    threaded,
    |config| telltale_machine::ThreadedProtocolMachine::with_workers(config, 1),
    |machine: telltale_machine::ThreadedProtocolMachine| {
        machine
            .shutdown_worker_pool()
            .expect("actual same native worker acknowledgement");
    }
);
