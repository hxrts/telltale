//! Executable nominal-image transport for the existing Lean runner.
//!
//! The payload is made from actual machine instructions, not regenerated from
//! communication types. It transports static code and a deterministic semantic
//! test-provider script; it cannot issue or restore a Rust owned-session handle.

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use telltale_machine::instr::{Instr, InvokeAction};
use telltale_machine::model::effects::{EffectFailure, EffectOutcome, EffectResponse};
use telltale_machine::nominal_command::{NominalCommandReply, NominalCommandRequest};
use telltale_machine::runtime::loader::CodeImage;
use telltale_types::LocalTypeR;

use crate::protocol_machine_runner::{ProtocolMachineRunner, ProtocolMachineRunnerError};

/// Version of the executable nominal comparison payload, separate from the
/// communication-only choreography input schema.
pub const NOMINAL_IMAGE_SCHEMA: &str = "nominal_image.v2";

/// Deterministic semantic host outcomes for cross-language execution tests.
/// These are not native errors, physical futures, or evidence capabilities.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "snake_case", deny_unknown_fields)]
pub enum NominalHostOutcome {
    /// Return the declared typed application result. Offset zero echoes the
    /// actual request ID; a nonzero offset tests foreign-result refusal.
    Success {
        /// Declared application result, distinct from host failure.
        result: Result<bool, String>,
        /// Relative actual request ID; zero preserves the original occurrence.
        reply_offset: u64,
    },
    /// Return evidence produced by the original registry between actual rounds.
    /// The input contains no witness fields and cannot construct authority.
    Readiness {
        /// Same supported original/foreign occurrence relation as ordinary replies.
        reply_offset: u64,
    },
    /// Keep the original occurrence pending.
    Blocked,
    /// Preserve a semantic host failure as the primary outcome.
    Failure {
        /// Original semantic failure, retained without rewriting its kind/message.
        failure: EffectFailure,
    },
    /// Deliberately return a successful response of another family.
    WrongResponse,
}

impl NominalHostOutcome {
    /// Apply this test-provider decision to the actual admitted request.
    #[must_use]
    pub fn for_request(&self, request: &NominalCommandRequest) -> EffectOutcome {
        self.for_request_with_readiness(request, None)
    }

    /// Return actual provider-held evidence data; canonical commit still requires
    /// registry-issued original authority. This method never issues a witness.
    #[must_use]
    pub fn for_request_with_readiness(
        &self,
        request: &NominalCommandRequest,
        witness: Option<&telltale_types::ReadinessWitness>,
    ) -> EffectOutcome {
        match self {
            Self::Success {
                result,
                reply_offset,
            } => {
                let Some(invocation) = request.invocation.checked_add(*reply_offset) else {
                    return EffectOutcome::failure(EffectFailure::contract_violation(
                        "scripted nominal reply ID overflow",
                    ));
                };
                EffectOutcome::success(EffectResponse::NominalCommand {
                    reply: telltale_machine::nominal_command::NominalCommandReply {
                        invocation,
                        result: result
                            .clone()
                            .map(telltale_machine::nominal_command::NominalCommandValue::Bool),
                    },
                })
            }
            Self::Readiness { reply_offset } => {
                let Some(witness) = witness else {
                    return EffectOutcome::failure(EffectFailure::unavailable(
                        "original readiness result has not been issued",
                    ));
                };
                let Some(invocation) = request.invocation.checked_add(*reply_offset) else {
                    return EffectOutcome::failure(EffectFailure::contract_violation(
                        "scripted nominal reply ID overflow",
                    ));
                };
                EffectOutcome::success(EffectResponse::NominalCommand {
                    reply: telltale_machine::nominal_command::NominalCommandReply {
                        invocation,
                        result: Ok(
                            telltale_machine::nominal_command::NominalCommandValue::Readiness(
                                witness.clone(),
                            ),
                        ),
                    },
                })
            }
            Self::Blocked => EffectOutcome::blocked(),
            Self::Failure { failure } => EffectOutcome::failure(failure.clone()),
            Self::WrongResponse => EffectOutcome::success(EffectResponse::Release),
        }
    }
}

/// Actual executable role programs and their original projected types.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NominalExecutableImage {
    programs: Vec<(String, Vec<Value>)>,
    global_type: Value,
    local_types: Vec<(String, Value)>,
}

// The current selected command compiler emits unit-payload communication.
// Existing local_to_json omits explicit ValType annotations, so refuse any
// such annotation rather than silently erase it in this executable route.
// RECURSION_SAFE: structural recursion over the finite local-type AST.
fn unannotated(local: &LocalTypeR) -> bool {
    match local {
        LocalTypeR::End | LocalTypeR::Var(_) => true,
        LocalTypeR::Mu { body, .. } => unannotated(body),
        LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => branches
            .iter()
            .all(|(_, ty, continuation)| ty.is_none() && unannotated(continuation)),
    }
}

impl NominalExecutableImage {
    /// Capture actual compiled instructions, refusing unsupported bytecode or
    /// metadata that the current executable transport cannot preserve.
    ///
    /// # Errors
    /// Returns a source-shape refusal or the original JSON encoding failure.
    pub fn from_code_image(image: &CodeImage) -> Result<Self, ProtocolMachineRunnerError> {
        image
            .validate_runtime_shape()
            .map_err(ProtocolMachineRunnerError::ParseError)?;
        if image.local_types.values().any(|local| !unannotated(local)) {
            return Err(ProtocolMachineRunnerError::ParseError(
                "nominal executable transport cannot erase local payload annotations".into(),
            ));
        }
        let mut calls = 0_usize;
        let programs =
            image
                .programs
                .iter()
                .map(|(role, code)| {
                    let encoded =
                        code.iter()
                            .map(|instruction| -> Result<Value, ProtocolMachineRunnerError> {
                                Ok(match instruction {
                                    Instr::Invoke {
                                        action: InvokeAction::DeclareCommand(declaration),
                                    } => json!(["declare", serde_json::to_value(declaration)?]),
                                    Instr::Invoke {
                                        action: InvokeAction::NominalCommand(call),
                                    } => {
                                        calls += 1;
                                        json!(["command", serde_json::to_value(call)?])
                                    }
                                    Instr::Invoke {
                                        action: InvokeAction::OperationLifecycle(action),
                                    } => json!(["operation", serde_json::to_value(action)?]),
                                    Instr::Offer { chan, label } => json!(["offer", chan, label]),
                                    Instr::Choose { chan, table } => json!(["choose", chan, table]),
                                    Instr::Send { chan, val } => json!(["send", chan, val]),
                                    Instr::Receive { chan, dst } => json!(["receive", chan, dst]),
                                    Instr::Jump { target } => json!(["jump", target]),
                                    Instr::Halt => json!(["halt"]),
                                    _ => return Err(ProtocolMachineRunnerError::ParseError(
                                        "unsupported instruction in nominal executable transport"
                                            .into(),
                                    )),
                                })
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                    Ok((role.clone(), encoded))
                })
                .collect::<Result<Vec<_>, ProtocolMachineRunnerError>>()?;
        if calls != 1 {
            return Err(ProtocolMachineRunnerError::ParseError(
                "nominal executable comparison requires one actual command instruction".into(),
            ));
        }
        Ok(Self {
            programs,
            global_type: crate::global_to_json(&image.global_type),
            local_types: image
                .local_types
                .iter()
                .map(|(role, local)| (role.clone(), crate::local_to_json(local)))
                .collect(),
        })
    }
}

/// Semantic test setup intent. This is not an issued owner/witness or an
/// authorization accepted by a Rust machine. Both sides independently invoke
/// their canonical original owner admission and readiness issuer.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NominalReadinessAdmission {
    /// Label passed to the real owned loader/model ownership admission.
    pub owner_id: String,
    /// Current slice admits issuance only after the actual Blocked occurrence.
    pub issue_after_blocked: bool,
}

/// Input for the actual executable-image path in the existing Lean runner.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NominalImageRunInput {
    /// Exact executable-image schema.
    pub schema_version: String,
    /// Actual instruction image, captured from the Rust compiler artifact.
    pub image: NominalExecutableImage,
    /// Semantic provider outcomes, stored on each original model coroutine.
    pub outcomes: Vec<(String, Vec<NominalHostOutcome>)>,
    /// Stable semantic identity; never physical provider or ownership authority.
    pub handler_identity: String,
    /// Selected deterministic output policy; denial is a real commit gate, not evidence.
    pub deny_outputs: bool,
    /// Actual selected register width, matching the Rust machine configuration.
    pub num_registers: u16,
    /// Logical scheduler-round bound.
    pub max_steps: u64,
    /// Independent semantic setup for the canonical readiness producer.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub readiness_admission: Option<NominalReadinessAdmission>,
}

impl ProtocolMachineRunner {
    /// Execute nominal bytecode in the existing Lean process. Unlike the
    /// communication runner, this route must publish nominal exchanges/events.
    ///
    /// # Errors
    /// Returns the existing process error or an original JSON decoding error.
    pub fn run_nominal_image(
        &self,
        input: &NominalImageRunInput,
    ) -> Result<Value, ProtocolMachineRunnerError> {
        require_nominal_input(input)?;
        let output =
            self.run_validation_operation("runNominalImage", &serde_json::to_value(input)?)?;
        let _checked = nominal_comparison_view(&output)?;
        let expected = input
            .image
            .programs
            .iter()
            .flat_map(|(_, code)| code)
            .find_map(|instruction| {
                let fields = instruction.as_array()?;
                (fields.first()?.as_str()? == "command")
                    .then(|| fields.get(1))
                    .flatten()
            })
            .ok_or_else(|| invalid_output("actual executable nominal instruction is missing"))?;
        require_source_image_binding(input, &output)?;
        let exchanges = output["exchanges"]
            .as_array()
            .ok_or_else(|| invalid_output("missing nominal exchanges"))?;
        for exchange in exchanges {
            if exchange.get("handler_identity") != Some(&json!(input.handler_identity)) {
                return Err(invalid_output("nominal handler contract changed"));
            }
            for (actual, source) in [
                ("role", "/role"),
                ("interface", "/declaration/interface"),
                ("operation", "/declaration/operation"),
                ("may_block", "/declaration/may_block"),
            ] {
                if exchange["request"].get(actual) != expected.pointer(source) {
                    return Err(invalid_output(
                        "nominal execution does not match the actual compiled instruction",
                    ));
                }
            }
        }
        let expected_predicate = expected
            .pointer("/declaration/readiness_predicate")
            .cloned()
            .unwrap_or(Value::Null);
        if expected_predicate.is_null() != input.readiness_admission.is_none()
            || exchanges
                .iter()
                .any(|exchange| exchange["request"]["readiness_predicate"] != expected_predicate)
        {
            return Err(invalid_output(
                "readiness setup/response does not match the actual compiled declaration",
            ));
        }
        let coroutines = output["coroutines"]
            .as_array()
            .ok_or_else(|| invalid_output("missing executable coroutines"))?;
        if coroutines.len() != input.image.programs.len()
            || input.image.programs.iter().any(|(role, _)| {
                let matching: Vec<_> = coroutines
                    .iter()
                    .filter(|coro| coro["role"].as_str() == Some(role.as_str()))
                    .collect();
                matching.len() != 1
                    || matching[0]["registers"].as_array().map(Vec::len)
                        != Some(usize::from(input.num_registers))
            })
            || output["effects"][0].get("budget_ticks") != expected.get("budget_ticks")
            || output["operations"][0].get("kind") != expected.get("enclosing_operation")
            || output["operations"][0].get("profile_name")
                != expected.pointer("/agreement_profile/profile_name")
            || output["operations"][0]["requires_proof"] != json!(true)
        {
            return Err(invalid_output(
                "nominal executable source/configuration/operation binding changed",
            ));
        }
        Ok(output)
    }
}

fn require_source_image_binding(
    input: &NominalImageRunInput,
    output: &Value,
) -> Result<(), ProtocolMachineRunnerError> {
    let expected = input
        .image
        .programs
        .iter()
        .flat_map(|(role, code)| {
            code.iter()
                .enumerate()
                .filter_map(move |(pc, instruction)| {
                    (instruction[0] == "operation"
                        && instruction[1]["operation_lifecycle"] == "begin")
                        .then_some((role, pc, &instruction[1]["declaration"]))
                })
        })
        .collect::<Vec<_>>();
    let actual = output["source_operations"]
        .as_array()
        .ok_or_else(|| invalid_output("missing source operation execution observations"))?;
    if actual.len() != expected.len()
        || expected.iter().any(|(role, pc, declaration)| {
            actual
                .iter()
                .filter(|original| {
                    original["role"] == json!(role)
                        && original["original_pc"] == json!(pc)
                        && &original["declaration"] == *declaration
                })
                .count()
                != 1
        })
    {
        return Err(invalid_output(
            "source operation executable payload or original continuation was erased or changed",
        ));
    }
    Ok(())
}

fn require_nominal_input(input: &NominalImageRunInput) -> Result<(), ProtocolMachineRunnerError> {
    if input.schema_version != NOMINAL_IMAGE_SCHEMA || input.handler_identity.is_empty()
        || input.num_registers == 0 || input.max_steps == 0
        || input.outcomes.is_empty()
        || input.outcomes.iter().any(|(_, outcomes)| outcomes.is_empty() || outcomes.iter().any(|outcome|
            matches!(outcome, NominalHostOutcome::Success { reply_offset, .. } | NominalHostOutcome::Readiness { reply_offset } if *reply_offset > 1)))
    {
        return Err(ProtocolMachineRunnerError::ParseError(
            "unbound nominal executable schema or handler contract".into(),
        ));
    }
    if input
        .readiness_admission
        .as_ref()
        .is_some_and(|admission| admission.owner_id.is_empty() || !admission.issue_after_blocked)
    {
        return Err(invalid_output(
            "readiness setup requires an original owner and actual Blocked boundary",
        ));
    }
    Ok(())
}

fn status_view(status: &telltale_machine::model::effects::EffectOutcomeStatus) -> Value {
    use telltale_machine::model::effects::EffectOutcomeStatus;
    match status {
        EffectOutcomeStatus::Success => json!({"status":"success"}),
        EffectOutcomeStatus::Blocked => json!({"status":"blocked"}),
        EffectOutcomeStatus::Failure { failure } => {
            json!({"status":"failure","kind":failure.kind,"message":failure.message})
        }
    }
}

// RECURSION_SAFE: structural recursion through the finite runtime value tree.
fn value_view(value: &telltale_machine::coroutine::Value) -> Value {
    use telltale_machine::coroutine::Value as RuntimeValue;
    match value {
        RuntimeValue::Unit => json!({"kind":"unit"}),
        RuntimeValue::Bool(value) => json!({"kind":"bool","value":value}),
        RuntimeValue::Nat(value) => json!({"kind":"nat","value":value}),
        RuntimeValue::Str(value) => json!({"kind":"string","value":value}),
        RuntimeValue::Prod(left, right) => {
            json!({"kind":"prod","left":value_view(left),"right":value_view(right)})
        }
        RuntimeValue::Readiness(witness) => readiness_value_view(witness),
        RuntimeValue::Endpoint(endpoint) => {
            json!({"kind":"chan","session":endpoint.sid,"role":endpoint.role})
        }
    }
}

fn readiness_value_view(witness: &telltale_types::ReadinessWitness) -> Value {
    json!({"kind":"readiness", "witness_id":witness.witness_id, "session_id":witness.session_id,
        "owner_id":witness.owner_id, "generation":witness.generation, "scope":witness.scope,
        "predicate_ref":witness.predicate_ref})
}

fn fault_view(
    status: &telltale_machine::coroutine::CoroStatus,
) -> Result<Value, ProtocolMachineRunnerError> {
    use telltale_machine::coroutine::{CoroStatus, Fault};
    Ok(match status {
        CoroStatus::Faulted(Fault::Invoke { failure }) => {
            json!({"kind":"invoke","failure":failure})
        }
        CoroStatus::Faulted(Fault::OutOfRegisters) => json!({"kind":"out_of_registers"}),
        CoroStatus::Faulted(Fault::OutputCondition { predicate_ref }) => {
            json!({"kind":"output_condition","predicate_ref":predicate_ref})
        }
        CoroStatus::Faulted(_) => {
            return Err(invalid_output(
                "unsupported terminal fault family cannot be erased by nominal comparison",
            ))
        }
        _ => Value::Null,
    })
}

/// Capture the actual nominal execution through shared read-only runtime views.
/// Raw absolute occurrence IDs are retained here. The explicit comparison rule
/// below validates every reference before relating the two local ID namespaces.
///
/// # Errors
/// Refuses an unsupported image or a recorded request outside its actual role.
pub fn capture_nominal_execution(
    image: &CodeImage,
    coroutines: &[telltale_machine::coroutine::Coroutine],
    exchanges: &[telltale_machine::model::effects::EffectExchangeRecord],
    objects: &telltale_machine::ProtocolMachineSemanticObjects,
    trace: &[telltale_machine::ObsEvent],
) -> Result<Value, ProtocolMachineRunnerError> {
    capture_nominal_execution_with_readiness(image, coroutines, exchanges, objects, trace, None)
}

fn captured_nominal_call(
    image: &CodeImage,
) -> Result<&telltale_machine::nominal_command::NominalCommandCall, ProtocolMachineRunnerError> {
    image
        .programs
        .values()
        .flatten()
        .find_map(|instruction| match instruction {
            Instr::Invoke {
                action: InvokeAction::NominalCommand(call),
            } => Some(call.as_ref()),
            _ => None,
        })
        .ok_or_else(|| {
            ProtocolMachineRunnerError::ParseError("missing actual command instruction".into())
        })
}

fn original_nominal_issued_at(
    exchanges: &[(
        &telltale_machine::EffectExchangeRecord,
        &NominalCommandRequest,
    )],
    invocation: u64,
) -> Option<u64> {
    exchanges
        .iter()
        .find(|(_, request)| request.invocation == invocation)
        .map(|(exchange, _)| exchange.request.tick)
}

fn canonical_session_id(
    value: u64,
) -> Result<telltale_machine::SessionId, ProtocolMachineRunnerError> {
    telltale_machine::SessionId::try_from(value)
        .map_err(|_| invalid_output("parent session exceeds canonical SessionId"))
}

/// Capture actual original registry observations, not a restored authority token.
///
/// # Errors
/// Refuses missing canonical registry evidence for an authoritative instruction.
pub fn capture_nominal_execution_with_readiness(
    image: &CodeImage,
    coroutines: &[telltale_machine::coroutine::Coroutine],
    exchanges: &[telltale_machine::model::effects::EffectExchangeRecord],
    objects: &telltale_machine::ProtocolMachineSemanticObjects,
    trace: &[telltale_machine::ObsEvent],
    readiness: Option<&telltale_machine::ReadinessRegistryView>,
) -> Result<Value, ProtocolMachineRunnerError> {
    let _preserved = NominalExecutableImage::from_code_image(image)?;
    let call = captured_nominal_call(image)?;
    if call.declaration.readiness_predicate.is_some() != readiness.is_some() {
        return Err(invalid_output(
            "readiness execution requires its actual original registry view",
        ));
    }
    let nominal: Vec<_> = exchanges
        .iter()
        .filter_map(|exchange| match &exchange.request.body {
            telltale_machine::model::effects::EffectRequestBody::NominalCommand { request } => {
                Some((exchange, request))
            }
            _ => None,
        })
        .collect();
    let exchange_views: Vec<_> = nominal.iter().map(|(exchange, request)| -> Result<Value, ProtocolMachineRunnerError> {
        let response = nominal_response_view(exchange.outcome.response.as_ref())?;
        Ok(json!({"effect_id":exchange.effect_id,"issued_at":exchange.request.tick,"observed_at":exchange.ordering_key,
            "handler_identity":exchange.handler_identity,
            "request":{"invocation":request.invocation,"session":request.session,
                "coroutine":request.coroutine,"role":request.role,
                "interface":request.declaration.interface,"operation":request.declaration.operation,
                "may_block":request.declaration.may_block,"readiness_predicate":request.declaration.readiness_predicate},
            "status":status_view(&exchange.outcome.status),
            "accepted_status":status_view(&exchange.outcome.accepted_status(&exchange.request.body)),
            "response":response}))
    }).collect::<Result<Vec<_>, _>>()?;
    let source_operations = coroutines
        .iter()
        .map(|coroutine| source_operation_view(coroutine, objects))
        .collect::<Result<Vec<_>, _>>()?
        .into_iter()
        .flatten()
        .collect::<Vec<_>>();
    let coroutines: Vec<_> = coroutines.iter().map(|coroutine| -> Result<Value, ProtocolMachineRunnerError> {
        use telltale_machine::coroutine::CoroStatus;
        let status = match &coroutine.status {
            CoroStatus::Ready => "ready", CoroStatus::Blocked(_) => "blocked", CoroStatus::Done => "done",
            CoroStatus::Faulted(_) => "faulted", CoroStatus::Speculating => "speculating",
        };
        Ok(json!({"coro_id":coroutine.id,"role":coroutine.role,"pc":coroutine.pc,"status":status,
            "fault":fault_view(&coroutine.status)?, "continuation":coroutine.nominal_continuation_view(),
            "exchange_count":nominal.iter().filter(|(_, request)| request.coroutine == coroutine.id).count(),
            "registers":coroutine.regs.iter().map(value_view).collect::<Vec<_>>()}))
    }).collect::<Result<Vec<_>, _>>()?;
    let effects: Vec<_> = objects
        .outstanding_effects
        .iter()
        .filter(|effect| effect.effect_kind == "nominal_command")
        .collect();
    let effect_views: Vec<_> = effects
        .iter()
        .map(|effect| {
            json!({
        "effect_id":effect.effect_id,"status":effect.status,
        "issued_at":original_nominal_issued_at(&nominal, effect.effect_id),
        "ordering_key":effect.ordering_key,"completed_at_tick":effect.completed_at_tick,
        "budget_ticks":effect.budget_ticks})
        })
        .collect();
    let operations: Vec<_> = objects.operation_instances.iter().filter(|operation|
        effects.iter().any(|effect| operation.operation_id == effect.operation_id)).map(|operation| json!({
            "effect_ids":operation.effect_ids,"kind":operation.kind,"requires_proof":operation.requires_proof,
            "profile_name":operation.agreement_profile.as_ref().map(|profile| &profile.profile_name)})).collect();
    let invoked: Vec<_> = trace
        .iter()
        .filter_map(|event| match event {
            telltale_machine::ObsEvent::Invoked {
                tick,
                coro_id,
                role,
            } => {
                let request = nominal
                    .iter()
                    .find(|(_, request)| request.coroutine == *coro_id)?
                    .1;
                Some(json!({"tick":tick,"session":request.session,"role":role,
                "interface":call.declaration.interface,"operation":call.declaration.operation}))
            }
            _ => None,
        })
        .collect();
    Ok(
        json!({"schema_version":NOMINAL_IMAGE_SCHEMA,"coroutines":coroutines,"effects":effect_views,
        "operations":operations,"source_operations":source_operations,
        "exchanges":exchange_views,"invoked":invoked,"readiness":readiness}),
    )
}

fn source_operation_outcome(
    outcome: Option<&telltale_machine::operation_lifecycle::OperationOutcome>,
) -> Value {
    use telltale_machine::operation_lifecycle::OperationOutcome;
    match outcome {
        None => Value::Null,
        Some(OperationOutcome::Success(value)) => {
            json!({"kind":"success", "value":value.as_ref().map(value_view)})
        }
        Some(OperationOutcome::Failure(value)) => {
            json!({"kind":"failure", "value":value.as_ref().map(value_view)})
        }
        Some(OperationOutcome::Timeout(value)) => {
            json!({"kind":"timeout", "value":value.as_ref().map(value_view)})
        }
        Some(OperationOutcome::Cancelled) => json!({"kind":"cancelled"}),
    }
}

fn source_operation_view(
    coroutine: &telltale_machine::coroutine::Coroutine,
    objects: &telltale_machine::ProtocolMachineSemanticObjects,
) -> Result<Option<Value>, ProtocolMachineRunnerError> {
    let Some(original) = coroutine.operation_continuation_view() else {
        return Ok(None);
    };
    if coroutine.operation_transition_failure().is_some() {
        return Err(invalid_output(
            "source operation transition diagnostic is outside supported comparison",
        ));
    }
    let records: Vec<_> = objects
        .operation_instances
        .iter()
        .filter(|record| record.operation_id == original.operation_id)
        .collect();
    let contracts: Vec<_> = objects
        .progress_contracts
        .iter()
        .filter(|record| record.operation_id == original.operation_id)
        .collect();
    let ([record], [progress]) = (records.as_slice(), contracts.as_slice()) else {
        return Err(invalid_output(
            "source operation canonical records missing or ambiguous",
        ));
    };
    let completed = original
        .completed_children
        .iter()
        .map(|(id, outcome)| {
            Ok(json!({"effect_id":id,"status":status_view(&outcome.status),
            "response":nominal_response_view(outcome.response.as_ref())?}))
        })
        .collect::<Result<Vec<_>, ProtocolMachineRunnerError>>()?;
    let failure = original
        .execution_failure
        .as_ref()
        .map(|fault| {
            fault_view(&telltale_machine::coroutine::CoroStatus::Faulted(
                fault.clone(),
            ))
        })
        .transpose()?
        .unwrap_or(Value::Null);
    Ok(Some(json!({"coro_id":coroutine.id, "role":coroutine.role,
        "session":coroutine.session_id, "entry_pc":0,
        "operation_id":original.operation_id,"owner":original.owner,
        "declaration":original.declaration,"original_pc":original.original_pc,
        "runtime_original_pc":original.original_pc,"issued_at":original.issued_at,
        "children":original.children,"admitted_slots":original.admitted_slots,
        "completed_children":completed,"outcome":source_operation_outcome(original.outcome.as_ref()),
        "resolved":original.resolved,"invalidated":original.invalidated,
        "execution_failure":failure,"record":record,"progress":progress})))
}

fn invalid_output(message: &str) -> ProtocolMachineRunnerError {
    ProtocolMachineRunnerError::ParseError(message.into())
}

fn request_from_view(
    exchange: &Value,
) -> Result<NominalCommandRequest, ProtocolMachineRunnerError> {
    let request = exchange
        .get("request")
        .ok_or_else(|| invalid_output("missing actual nominal request"))?;
    Ok(serde_json::from_value(
        json!({"invocation":request.get("invocation"),
        "session":request.get("session"),"coroutine":request.get("coroutine"),"role":request.get("role"),
        "declaration":{"interface":request.get("interface"),"operation":request.get("operation"),
            "may_block":request.get("may_block"),"readiness_predicate":request.get("readiness_predicate")}}),
    )?)
}

fn outcome_from_view(exchange: &Value) -> Result<EffectOutcome, ProtocolMachineRunnerError> {
    use telltale_machine::model::effects::EffectOutcomeStatus;
    let status = exchange
        .get("status")
        .ok_or_else(|| invalid_output("missing raw nominal status"))?;
    let status = match status.get("status").and_then(Value::as_str) {
        Some("success") => EffectOutcomeStatus::Success,
        Some("blocked") => EffectOutcomeStatus::Blocked,
        Some("failure") => EffectOutcomeStatus::Failure {
            failure: serde_json::from_value::<EffectFailure>(json!({
            "kind":status.get("kind"),"message":status.get("message")}))?,
        },
        _ => return Err(invalid_output("unknown raw nominal status")),
    };
    let response = exchange
        .get("response")
        .ok_or_else(|| invalid_output("missing raw nominal response field"))?;
    let response = if response.is_null() {
        None
    } else {
        Some(match response.get("kind").and_then(Value::as_str) {
            Some("nominal_command") => EffectResponse::NominalCommand {
                reply: serde_json::from_value::<NominalCommandReply>(json!({
            "invocation":response.get("invocation"),"result":response.get("result")}))?,
            },
            Some("release") => EffectResponse::Release,
            _ => return Err(invalid_output("unknown raw nominal response family")),
        })
    };
    Ok(EffectOutcome { status, response })
}

fn validate_readiness_execution(output: &Value) -> Result<(), ProtocolMachineRunnerError> {
    use telltale_machine::nominal_command::NominalCommandValue;
    use telltale_machine::{AuthorityAuditRecord, OwnershipCapability};
    let observed = output
        .get("readiness")
        .ok_or_else(|| invalid_output("missing explicit readiness observation"))?;
    let exchanges = output["exchanges"]
        .as_array()
        .ok_or_else(|| invalid_output("missing exchanges"))?;
    let first = exchanges
        .first()
        .ok_or_else(|| invalid_output("missing original readiness request"))?;
    let request = request_from_view(first)?;
    let Some(_) = &request.declaration.readiness_predicate else {
        return if observed.is_null() {
            Ok(())
        } else {
            Err(invalid_output(
                "ordinary Boolean command cannot claim readiness custody",
            ))
        };
    };
    let owner: OwnershipCapability = serde_json::from_value(observed["current"].clone())?;
    let issued: Vec<telltale_types::ReadinessWitness> =
        serde_json::from_value(observed["issued"].clone())?;
    let consumed: Vec<u64> = serde_json::from_value(observed["consumed"].clone())?;
    let audit: Vec<AuthorityAuditRecord> = serde_json::from_value(observed["audit"].clone())?;
    let (witness, consumed_count) =
        observed_readiness_original(observed, &request, &owner, &issued, &consumed, &audit)?;
    for exchange in exchanges {
        if let Some(EffectResponse::NominalCommand { reply }) =
            outcome_from_view(exchange)?.response
        {
            if let Ok(NominalCommandValue::Readiness(returned)) = reply.result {
                if &returned != witness {
                    return Err(invalid_output(
                        "returned witness is not the actual issued original",
                    ));
                }
            }
        }
    }
    let coroutines = output["coroutines"]
        .as_array()
        .ok_or_else(|| invalid_output("missing readiness coroutines"))?;
    for coro in coroutines {
        validate_readiness_holder(coro, witness, &owner)?;
    }
    if output["effects"][0]["status"] == json!("succeeded") && consumed_count != 1 {
        return Err(invalid_output(
            "nominal readiness success has no actual registry consumption",
        ));
    }
    Ok(())
}

fn observed_readiness_original<'a>(
    observed: &Value,
    request: &NominalCommandRequest,
    owner: &telltale_machine::OwnershipCapability,
    issued: &[telltale_types::ReadinessWitness],
    consumed: &[u64],
    audit: &'a [telltale_machine::AuthorityAuditRecord],
) -> Result<(&'a telltale_types::ReadinessWitness, usize), ProtocolMachineRunnerError> {
    use telltale_machine::{AuthorityArtifact, AuthorityAuditEvent, OwnershipScope};
    let predicate = request
        .declaration
        .readiness_predicate
        .as_ref()
        .ok_or_else(|| invalid_output("missing source predicate"))?;
    if owner.session_id != request.session
        || owner.owner_id.is_empty()
        || owner.scope != OwnershipScope::Session
        || observed["transfer_pending"] != json!(false)
        || audit.is_empty()
        || audit.iter().any(|record| {
            record.tick.is_none() || !matches!(&record.artifact, AuthorityArtifact::Readiness(_))
        })
        || audit.windows(2).any(|pair| pair[0].tick > pair[1].tick)
    {
        return Err(invalid_output(
            "readiness lost actual owner/session/chronology binding",
        ));
    }
    let original: Vec<_> = audit
        .iter()
        .filter_map(|record| match (&record.artifact, record.event) {
            (AuthorityArtifact::Readiness(witness), AuthorityAuditEvent::Issued) => Some(witness),
            _ => None,
        })
        .collect();
    if original.len() != 1
        || observed["next_witness_id"].as_u64() != original[0].witness_id.checked_add(1)
    {
        return Err(invalid_output(
            "missing or ambiguous original canonical readiness issuance",
        ));
    }
    let witness = original[0];
    if witness.session_id != owner.session_id
        || witness.owner_id != owner.owner_id
        || witness.generation != owner.generation
        || witness.scope != owner.scope
        || &witness.predicate_ref != predicate
    {
        return Err(invalid_output(
            "readiness issuance was reconstructed from unrelated semantic fields",
        ));
    }
    let consumed_count = audit
        .iter()
        .filter(|record| {
            record.event == AuthorityAuditEvent::Consumed
                && record.artifact == AuthorityArtifact::Readiness(witness.clone())
        })
        .count();
    if !((issued == [witness.clone()] && consumed.is_empty() && consumed_count == 0)
        || (issued.is_empty() && consumed == [witness.witness_id] && consumed_count == 1))
    {
        return Err(invalid_output(
            "readiness settlement lost actual single-use registry state",
        ));
    }
    Ok((witness, consumed_count))
}

fn validate_readiness_holder(
    coro: &Value,
    original: &telltale_types::ReadinessWitness,
    owner: &telltale_machine::OwnershipCapability,
) -> Result<(), ProtocolMachineRunnerError> {
    use telltale_machine::nominal_command::NominalCommandValue;
    let holder = &coro["continuation"];
    if !holder.is_null() {
        let retained_owner: telltale_machine::OwnershipCapability =
            serde_json::from_value(holder["readiness_owner"].clone())?;
        if &retained_owner != owner {
            return Err(invalid_output(
                "retained readiness lost the original owner generation",
            ));
        }
        let returned: Option<Result<NominalCommandValue, String>> =
            serde_json::from_value(holder["returned"].clone())?;
        if let Some(Ok(NominalCommandValue::Readiness(witness))) = returned {
            if &witness != original {
                return Err(invalid_output(
                    "retained original readiness payload changed",
                ));
            }
        }
    }
    for register in coro["registers"]
        .as_array()
        .ok_or_else(|| invalid_output("missing readiness registers"))?
    {
        if register["kind"] == json!("readiness") {
            let witness: telltale_types::ReadinessWitness =
                serde_json::from_value(register.clone())?;
            if &witness != original {
                return Err(invalid_output(
                    "committed witness differs from the canonical original",
                ));
            }
        }
    }
    Ok(())
}

// This validates references in the unmodified execution view before making a
// comparison copy. Only one nominal occurrence is supported by this route.
fn require_nominal_lifecycle(
    effect: &Value,
    issued_at: u64,
) -> Result<(), ProtocolMachineRunnerError> {
    if effect.get("ordering_key").and_then(Value::as_u64) != Some(issued_at) {
        return Err(invalid_output(
            "nominal settlement refreshed original ordering key",
        ));
    }
    let completed = effect
        .get("completed_at_tick")
        .ok_or_else(|| invalid_output("missing actual completion observation"))?;
    let terminal = matches!(
        effect.get("status").and_then(Value::as_str),
        Some("succeeded" | "failed" | "cancelled" | "invalidated")
    );
    if terminal {
        if completed
            .as_u64()
            .filter(|tick| *tick >= issued_at)
            .is_none()
        {
            return Err(invalid_output(
                "terminal nominal settlement lost actual completion tick",
            ));
        }
    } else if !completed.is_null() {
        return Err(invalid_output(
            "live nominal obligation falsely acknowledges completion",
        ));
    }
    Ok(())
}

fn nominal_original_context(output: &Value) -> Result<(u64, u64), ProtocolMachineRunnerError> {
    if output.get("schema_version").and_then(Value::as_str) != Some(NOMINAL_IMAGE_SCHEMA) {
        return Err(invalid_output("missing executable nominal output schema"));
    }
    let effects = output
        .get("effects")
        .and_then(Value::as_array)
        .ok_or_else(|| invalid_output("missing nominal effects"))?;
    if effects.len() != 1 {
        return Err(invalid_output(
            "missing or ambiguous original nominal occurrence",
        ));
    }
    let id = effects[0]
        .get("effect_id")
        .and_then(Value::as_u64)
        .ok_or_else(|| invalid_output("missing original nominal ID"))?;
    let issued_at = effects[0]
        .get("issued_at")
        .and_then(Value::as_u64)
        .ok_or_else(|| invalid_output("missing original issued tick"))?;
    require_nominal_lifecycle(&effects[0], issued_at)?;
    if effects[0]
        .get("budget_ticks")
        .and_then(Value::as_u64)
        .filter(|budget| *budget > 0)
        .is_none()
    {
        return Err(invalid_output("missing selected original tick budget"));
    }
    let exchanges = output
        .get("exchanges")
        .and_then(Value::as_array)
        .ok_or_else(|| invalid_output("missing typed nominal exchanges"))?;
    if exchanges.is_empty() {
        return Err(invalid_output(
            "zero nominal exchanges cannot prove executable lowering",
        ));
    }
    let operations = output
        .get("operations")
        .and_then(Value::as_array)
        .ok_or_else(|| invalid_output("missing nominal operation"))?;
    if operations.len() != 1 || operations[0].get("effect_ids") != Some(&json!([id])) {
        return Err(invalid_output(
            "nominal operation does not retain the actual occurrence",
        ));
    }
    if operations[0].get("requires_proof") != Some(&json!(true))
        || operations[0]
            .get("kind")
            .and_then(Value::as_str)
            .filter(|name| !name.is_empty())
            .is_none()
        || operations[0]
            .get("profile_name")
            .and_then(Value::as_str)
            .filter(|name| !name.is_empty())
            .is_none()
    {
        return Err(invalid_output(
            "missing original operation/proof/profile binding",
        ));
    }
    Ok((id, issued_at))
}

fn require_nominal_coroutines(
    output: &Value,
    id: u64,
    issued_at: u64,
) -> Result<(), ProtocolMachineRunnerError> {
    let effects = output["effects"]
        .as_array()
        .ok_or_else(|| invalid_output("missing nominal effects"))?;
    let exchanges = output["exchanges"]
        .as_array()
        .ok_or_else(|| invalid_output("missing exchanges"))?;
    let coroutines = output
        .get("coroutines")
        .and_then(Value::as_array)
        .ok_or_else(|| invalid_output("missing executable continuation evidence"))?;
    if coroutines.is_empty()
        || coroutines.iter().any(|coro| {
            coro.get("coro_id").and_then(Value::as_u64).is_none()
                || coro
                    .get("role")
                    .and_then(Value::as_str)
                    .filter(|role| !role.is_empty())
                    .is_none()
                || coro.get("pc").and_then(Value::as_u64).is_none()
                || coro
                    .get("registers")
                    .and_then(Value::as_array)
                    .filter(|regs| !regs.is_empty())
                    .is_none()
                || coro.get("exchange_count").and_then(Value::as_u64).is_none()
        })
    {
        return Err(invalid_output("incomplete actual coroutine continuation"));
    }
    let total = coroutines.iter().try_fold(0_u64, |count, coro| {
        count.checked_add(coro["exchange_count"].as_u64()?)
    });
    if total != u64::try_from(exchanges.len()).ok() {
        return Err(invalid_output("nominal exchange counts changed"));
    }
    for coro in coroutines {
        let fault = coro
            .get("fault")
            .ok_or_else(|| invalid_output("missing actual terminal fault view"))?;
        if (coro["status"].as_str() == Some("faulted")) == fault.is_null() {
            return Err(invalid_output(
                "terminal fault payload was erased or invented",
            ));
        }
        let holder = coro
            .get("continuation")
            .ok_or_else(|| invalid_output("missing actual continuation view"))?;
        if !holder.is_null()
            && (holder.get("invocation").and_then(Value::as_u64) != Some(id)
                || holder.get("issued_at").and_then(Value::as_u64) != Some(issued_at)
                || holder.pointer("/call/budget_ticks") != effects[0].get("budget_ticks"))
        {
            return Err(invalid_output(
                "retained continuation lost its original occurrence/window",
            ));
        }
    }
    Ok(())
}

fn normalize_nominal_exchange(
    exchange: &Value,
    compared: &mut Value,
    coroutines: &[Value],
    id: u64,
    issued_at: u64,
    effect: &Value,
) -> Result<(), ProtocolMachineRunnerError> {
    let request = request_from_view(exchange)?;
    let outcome = outcome_from_view(exchange)?;
    let owners: Vec<_> = coroutines
        .iter()
        .filter(|coro| {
            coro["coro_id"].as_u64() == u64::try_from(request.coroutine).ok()
                && coro["role"].as_str() == Some(request.role.as_str())
        })
        .collect();
    if owners.len() != 1
        || exchange.get("issued_at").and_then(Value::as_u64) != Some(issued_at)
        || exchange
            .get("observed_at")
            .and_then(Value::as_u64)
            .filter(|tick| *tick >= issued_at)
            .is_none()
        || exchange
            .get("handler_identity")
            .and_then(Value::as_str)
            .filter(|identity| !identity.is_empty())
            .is_none()
    {
        return Err(invalid_output(
            "nominal callback lost original coroutine/handler/window binding",
        ));
    }

    let accepted = outcome.accepted_status(
        &telltale_machine::model::effects::EffectRequestBody::NominalCommand { request },
    );
    if exchange.get("accepted_status") != Some(&status_view(&accepted)) {
        return Err(invalid_output(
            "nominal typed acceptance was omitted or changed",
        ));
    }
    if exchange.get("effect_id").and_then(Value::as_u64) != Some(id)
        || exchange
            .pointer("/request/invocation")
            .and_then(Value::as_u64)
            != Some(id)
        || exchange.get("issued_at") != effect.get("issued_at")
    {
        return Err(invalid_output(
            "nominal exchange lost the original occurrence or tick",
        ));
    }
    compared["effect_id"] = json!(0);
    compared["request"]["invocation"] = json!(0);
    if exchange.pointer("/response/kind").and_then(Value::as_str) == Some("nominal_command") {
        let reply = exchange
            .pointer("/response/invocation")
            .and_then(Value::as_u64)
            .ok_or_else(|| invalid_output("missing actual returned nominal ID"))?;
        if reply != id && id.checked_add(1) != Some(reply) {
            return Err(invalid_output("unsupported foreign nominal reply relation"));
        }
        compared["response"]["invocation"] = json!(if reply == id { 0 } else { 1 });
    }
    Ok(())
}

fn require_nominal_publication(
    output: &Value,
    effect: &Value,
    exchanges: &[Value],
) -> Result<(), ProtocolMachineRunnerError> {
    for key in ["coroutines", "invoked"] {
        if !output.get(key).is_some_and(Value::is_array) {
            return Err(invalid_output(
                "missing executable continuation/event evidence",
            ));
        }
    }
    let invoked = output["invoked"]
        .as_array()
        .ok_or_else(|| invalid_output("missing actual nominal events"))?;
    let last_failed = exchanges
        .last()
        .and_then(|exchange| exchange.pointer("/accepted_status/status"))
        .and_then(Value::as_str)
        == Some("failure");
    if last_failed && effect["status"].as_str() != Some("failed") {
        return Err(invalid_output(
            "original host failure cannot publish a successful/live nominal effect",
        ));
    }
    let succeeded = effect["status"].as_str() == Some("succeeded");
    if invoked.len() != usize::from(succeeded) {
        return Err(invalid_output(
            "nominal success publication does not match actual lifecycle",
        ));
    }
    Ok(())
}

fn source_operation_identity(
    source: &Value,
    coroutines: &[Value],
) -> Result<
    (
        String,
        telltale_machine::operation_lifecycle::OperationDeclaration,
    ),
    ProtocolMachineRunnerError,
> {
    let declaration: telltale_machine::operation_lifecycle::OperationDeclaration =
        serde_json::from_value(source["declaration"].clone())?;
    let owner: telltale_machine::OwnershipCapability =
        serde_json::from_value(source["owner"].clone())?;
    let issued = source["issued_at"]
        .as_u64()
        .ok_or_else(|| invalid_output("missing parent original tick"))?;
    let pc = source["original_pc"]
        .as_u64()
        .ok_or_else(|| invalid_output("missing parent original PC"))?;
    let entry = source["entry_pc"]
        .as_u64()
        .ok_or_else(|| invalid_output("missing actual parent role entry"))?;
    let runtime_pc = source["runtime_original_pc"]
        .as_u64()
        .ok_or_else(|| invalid_output("missing installed parent PC"))?;
    let cid = source["coro_id"]
        .as_u64()
        .ok_or_else(|| invalid_output("missing parent coroutine"))?;
    let sid = source["session"]
        .as_u64()
        .ok_or_else(|| invalid_output("missing parent session"))?;
    let session = canonical_session_id(sid)?;
    let expected = format!("operation:{sid}:{cid}:{runtime_pc}:{issued}");
    if source["operation_id"] != json!(expected)
        || pc.checked_add(entry) != Some(runtime_pc)
        || owner.session_id != session
        || owner.owner_id.is_empty()
        || !declaration.supported()
        || source["role"] != json!(declaration.role)
        || !matches!(owner.scope, telltale_machine::OwnershipScope::Session)
        || coroutines
            .iter()
            .filter(|coro| coro["coro_id"] == json!(cid) && coro["role"] == source["role"])
            .count()
            != 1
        || issued.checked_add(declaration.budget_ticks.get()).is_none()
    {
        return Err(invalid_output(
            "source operation lost original role/owner/PC/window identity",
        ));
    }
    Ok((expected, declaration))
}

fn require_source_operation_records(
    source: &Value,
    operation_id: &str,
    declaration: &telltale_machine::operation_lifecycle::OperationDeclaration,
    id: u64,
) -> Result<(), ProtocolMachineRunnerError> {
    use telltale_machine::semantic_objects::{OperationInstance, ProgressContract};
    let record: OperationInstance = serde_json::from_value(source["record"].clone())?;
    let progress: ProgressContract = serde_json::from_value(source["progress"].clone())?;
    let owner: telltale_machine::OwnershipCapability =
        serde_json::from_value(source["owner"].clone())?;
    if record.operation_id != operation_id
        || progress.operation_id != operation_id
        || record.session != Some(owner.session_id)
        || progress.session != record.session
        || record.owner_id.as_ref() != Some(&owner.owner_id)
        || record.kind != declaration.name
        || record.agreement_profile.as_ref() != Some(&declaration.agreement_profile)
        || record.budget_ticks != Some(declaration.budget_ticks.get())
        || progress.budget_ticks != record.budget_ticks
        || !record.requires_proof
        || !progress.bounded
        || record.terminal_publication.is_some()
        || record.handler_identity.is_some()
        || record.effect_ids != [id]
        || record.dependent_operation_ids != [format!("effect:{id}")]
        || progress.last_ordering_key != source["issued_at"].as_u64()
    {
        return Err(invalid_output(
            "source operation original canonical policy/children/progress changed",
        ));
    }
    let resolved = source["resolved"]
        .as_bool()
        .ok_or_else(|| invalid_output("missing original resolution state"))?;
    let invalidated = source["invalidated"]
        .as_bool()
        .ok_or_else(|| invalid_output("missing original revocation state"))?;
    if resolved && (invalidated || source["outcome"].is_null()) {
        return Err(invalid_output(
            "source operation resolution was erased or conflated with revocation",
        ));
    }
    if resolved {
        let phase = match source["outcome"]["kind"].as_str() {
            Some("success") => "succeeded",
            Some("failure") => "failed",
            Some("cancelled") => "cancelled",
            _ => return Err(invalid_output("unsupported source resolution")),
        };
        let endpoint = source["issued_at"]
            .as_u64()
            .and_then(|issued| issued.checked_add(declaration.budget_ticks.get()));
        if source["record"]["phase"] != phase
            || source["progress"]["state"] != phase
            || progress
                .last_progress_tick
                .zip(endpoint)
                .map_or(true, |(tick, end)| {
                    tick > end || Some(tick) < source["issued_at"].as_u64()
                })
        {
            return Err(invalid_output(
                "source resolution bypassed original lifecycle/window",
            ));
        }
    }
    Ok(())
}

fn normalize_source_children(
    source: &Value,
    compared: &mut Value,
    declaration: &telltale_machine::operation_lifecycle::OperationDeclaration,
    exchanges: &[Value],
    id: u64,
) -> Result<(), ProtocolMachineRunnerError> {
    let [slot] = declaration.required_children.as_slice() else {
        return Err(invalid_output(
            "comparison requires exact original single-child source manifest",
        ));
    };
    if source["children"] != json!([id])
        || source["admitted_slots"] != json!([slot.pc])
        || slot.call.enclosing_operation != declaration.name
        || slot.call.role != declaration.role
        || slot.call.agreement_profile != declaration.agreement_profile
        || slot.call.budget_ticks != declaration.budget_ticks
        || slot.call.progress_contract != declaration.progress_contract
        || slot.call.progress_window != declaration.progress_window
    {
        return Err(invalid_output(
            "source child manifest/actual admission changed",
        ));
    }
    let completed = source["completed_children"]
        .as_array()
        .ok_or_else(|| invalid_output("missing actual retained child outcomes"))?;
    let last = exchanges
        .last()
        .ok_or_else(|| invalid_output("source child has no original callback"))?;
    let terminal = last["status"]["status"] != "blocked";
    if completed.len() != usize::from(terminal)
        || completed.first().is_some_and(|actual| {
            actual["effect_id"] != json!(id)
                || actual["status"] != last["status"]
                || actual["response"] != last["response"]
        })
    {
        return Err(invalid_output(
            "original source child outcome was omitted or replaced",
        ));
    }
    compared["children"] = json!([0]);
    compared["record"]["effect_ids"] = json!([0]);
    compared["record"]["dependent_operation_ids"] = json!(["effect:0"]);
    if !completed.is_empty() {
        compared["completed_children"][0]["effect_id"] = json!(0);
        if completed[0]["response"]["kind"] == "nominal_command" {
            let reply = completed[0]["response"]["invocation"]
                .as_u64()
                .ok_or_else(|| invalid_output("missing original child reply ID"))?;
            if reply != id && id.checked_add(1) != Some(reply) {
                return Err(invalid_output(
                    "unsupported foreign source child reply relation",
                ));
            }
            compared["completed_children"][0]["response"]["invocation"] =
                json!(if reply == id { 0 } else { 1 });
        }
    }
    Ok(())
}

fn normalize_source_operations(
    output: &Value,
    compared: &mut Value,
    id: u64,
) -> Result<(), ProtocolMachineRunnerError> {
    let source = output["source_operations"]
        .as_array()
        .ok_or_else(|| invalid_output("missing source operation continuation observations"))?;
    if source.len() > 1 {
        return Err(invalid_output("ambiguous original source operation"));
    }
    let coroutines = output["coroutines"]
        .as_array()
        .ok_or_else(|| invalid_output("missing original coroutines"))?;
    let exchanges = output["exchanges"]
        .as_array()
        .ok_or_else(|| invalid_output("missing original exchanges"))?;
    for (index, original) in source.iter().enumerate() {
        let (operation_id, declaration) = source_operation_identity(original, coroutines)?;
        require_source_operation_records(original, &operation_id, &declaration, id)?;
        let target = &mut compared["source_operations"][index];
        normalize_source_children(original, target, &declaration, exchanges, id)?;
        target["operation_id"] = json!("source_operation:0");
        target["record"]["operation_id"] = json!("source_operation:0");
        target["progress"]["operation_id"] = json!("source_operation:0");
        target["entry_pc"] = json!(0);
        target["runtime_original_pc"] = original["original_pc"].clone();
    }
    Ok(())
}

fn nominal_comparison_view(output: &Value) -> Result<Value, ProtocolMachineRunnerError> {
    let (id, issued_at) = nominal_original_context(output)?;
    require_nominal_coroutines(output, id, issued_at)?;
    validate_readiness_execution(output)?;
    let effects = output["effects"]
        .as_array()
        .ok_or_else(|| invalid_output("missing effects"))?;
    let coroutines = output["coroutines"]
        .as_array()
        .ok_or_else(|| invalid_output("missing coroutines"))?;
    let exchanges = output["exchanges"]
        .as_array()
        .ok_or_else(|| invalid_output("missing exchanges"))?;
    let mut compared = output.clone();
    compared["effects"][0]["effect_id"] = json!(0);
    compared["operations"][0]["effect_ids"] = json!([0]);
    for (index, coro) in coroutines.iter().enumerate() {
        if !coro["continuation"].is_null() {
            compared["coroutines"][index]["continuation"]["invocation"] = json!(0);
        }
    }
    for (index, exchange) in exchanges.iter().enumerate() {
        normalize_nominal_exchange(
            exchange,
            &mut compared["exchanges"][index],
            coroutines,
            id,
            issued_at,
            &effects[0],
        )?;
    }
    require_nominal_publication(output, &effects[0], exchanges)?;
    normalize_source_operations(output, &mut compared, id)?;
    Ok(compared)
}

/// Compare typed nominal execution, never communication-only traces. Each side
/// must retain one actual occurrence, its typed exchanges and original window.
/// IDs are related only after the explicit reference checks above; raw outputs
/// remain unchanged. No ticks, results, lifecycle states or continuations are
/// normalized.
///
/// # Errors
/// Refuses missing/erased nominal evidence or inconsistent original references.
pub fn nominal_executions_equivalent(
    left: &Value,
    right: &Value,
) -> Result<bool, ProtocolMachineRunnerError> {
    Ok(nominal_comparison_view(left)? == nominal_comparison_view(right)?)
}

fn nominal_response_view(
    response: Option<&EffectResponse>,
) -> Result<Value, ProtocolMachineRunnerError> {
    match response {
        Some(EffectResponse::NominalCommand { reply }) => Ok(json!({
            "kind":"nominal_command","invocation":reply.invocation,"result":reply.result})),
        Some(EffectResponse::Release) => Ok(json!({"kind":"release"})),
        None => Ok(Value::Null),
        Some(_) => Err(invalid_output(
            "unsupported actual typed nominal response cannot be erased",
        )),
    }
}

#[cfg(test)]
mod response_capture_tests {
    use super::*;

    #[test]
    fn original_issue_tick_comes_from_first_matching_typed_request_envelope() {
        use telltale_machine::{
            EffectExchangeRecord, EffectInterfaceMetadata, EffectRequest, EffectRequestBody,
        };
        let nominal = NominalCommandRequest {
            invocation: 9,
            session: 2,
            coroutine: 0,
            declaration: telltale_machine::nominal_command::NominalCommandDeclaration {
                interface: "Host".into(),
                operation: "ready".into(),
                may_block: true,
                readiness_predicate: None,
            },
            role: "A".into(),
        };
        let original = EffectExchangeRecord {
            effect_id: 9,
            handler_identity: "original".into(),
            ordering_key: 17,
            request: EffectRequest {
                effect_id: Some(9),
                tick: 3,
                session: Some(2),
                operation_id: Some("effect:9".into()),
                metadata: EffectInterfaceMetadata::for_effect_kind("invoke_step"),
                body: EffectRequestBody::NominalCommand {
                    request: nominal.clone(),
                },
            },
            outcome: EffectOutcome::blocked(),
        };
        let mut retried = original.clone();
        retried.ordering_key = 82;
        let exchanges = [(&original, &nominal), (&retried, &nominal)];
        assert_eq!(original_nominal_issued_at(&exchanges, 9), Some(3));
        assert_eq!(original_nominal_issued_at(&exchanges, 99), None);
    }

    #[test]
    fn raw_outcome_decoding_retains_concrete_failure_and_typed_application_reply() {
        use telltale_machine::nominal_command::{NominalCommandReply, NominalCommandValue};
        use telltale_machine::EffectOutcomeStatus;
        let original = EffectOutcome {
            status: EffectOutcomeStatus::Failure {
                failure: EffectFailure::denied("original semantic failure"),
            },
            response: Some(EffectResponse::NominalCommand {
                reply: NominalCommandReply {
                    invocation: 9,
                    result: Ok(NominalCommandValue::Bool(true)),
                },
            }),
        };
        let view = json!({"status":status_view(&original.status),
            "response":nominal_response_view(original.response.as_ref()).expect("typed response")});
        assert_eq!(
            outcome_from_view(&view).expect("concrete original types"),
            original
        );
        let mut malformed = view;
        malformed["response"]["result"] = json!({"Ok":true});
        assert!(outcome_from_view(&malformed).is_err());
    }

    #[test]
    fn parent_session_conversion_preserves_the_actual_canonical_integer_range() {
        let maximum =
            u64::try_from(telltale_machine::SessionId::MAX).expect("canonical native/wasm width");
        assert_eq!(
            canonical_session_id(maximum).expect("largest canonical ID"),
            telltale_machine::SessionId::MAX
        );
        if let Some(foreign) = maximum.checked_add(1) {
            assert!(canonical_session_id(foreign).is_err());
        }
    }

    #[test]
    fn original_ordering_and_actual_completion_observations_cannot_be_erased() {
        let blocked = json!({"ordering_key":3,"completed_at_tick":null,"status":"blocked"});
        require_nominal_lifecycle(&blocked, 3).expect("live original has no completion");
        let settled = json!({"ordering_key":3,"completed_at_tick":7,"status":"succeeded"});
        require_nominal_lifecycle(&settled, 3).expect("actual later completion remains visible");
        for mutated in [
            json!({"ordering_key":7,"completed_at_tick":7,"status":"succeeded"}),
            json!({"ordering_key":3,"status":"succeeded"}),
            json!({"ordering_key":3,"completed_at_tick":null,"status":"succeeded"}),
            json!({"ordering_key":3,"completed_at_tick":2,"status":"succeeded"}),
            json!({"ordering_key":3,"completed_at_tick":7,"status":"blocked"}),
        ] {
            assert!(require_nominal_lifecycle(&mutated, 3).is_err());
        }
    }

    #[test]
    fn readiness_provider_input_cannot_transport_issued_authority() {
        let forged_outcome = json!({"status":"readiness", "reply_offset":0,
            "witness":{"witness_id":1,"session_id":0,"owner_id":"original","generation":0,"scope":"Session","predicate_ref":"Host.ready"}});
        assert!(serde_json::from_value::<NominalHostOutcome>(forged_outcome).is_err());
        let forged_owner = json!({"owner_id":"original", "issue_after_blocked":true,
            "generation":0,"session_id":0,"scope":"Session"});
        assert!(serde_json::from_value::<NominalReadinessAdmission>(forged_owner).is_err());
        let intent: NominalReadinessAdmission =
            serde_json::from_value(json!({"owner_id":"original","issue_after_blocked":true}))
                .expect("setup intent only");
        assert!(intent.issue_after_blocked);
        assert_eq!(intent.owner_id, "original");
    }

    #[test]
    fn unsupported_actual_response_is_not_captured_as_absence_even_on_failure() {
        let outcome = EffectOutcome {
            status: telltale_machine::model::effects::EffectOutcomeStatus::Failure {
                failure: EffectFailure::denied("original semantic failure"),
            },
            response: Some(EffectResponse::Choose {
                label: "original typed payload".into(),
            }),
        };
        assert!(nominal_response_view(outcome.response.as_ref()).is_err());
        assert_eq!(
            nominal_response_view(None).expect("actual absence"),
            Value::Null
        );
        assert_eq!(
            nominal_response_view(Some(&EffectResponse::Release)).expect("supported wrong kind"),
            json!({"kind":"release"})
        );
    }
}
