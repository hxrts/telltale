//! VM-backed simulation runner.
//!
//! Wraps `telltale-vm` to execute choreographies through the bytecode VM,
//! producing the same `Trace` format as the lightweight scheduler.

use std::collections::{BTreeMap, HashMap};

use telltale_types::{GlobalType, LocalTypeR};
use telltale_vm::coroutine::Value;
use telltale_vm::loader::CodeImage;
use telltale_vm::vm::{ObsEvent, StepResult, VMConfig, VM};

use crate::scheduler::EffectHandler as SimEffectHandler;
use crate::trace::{StepRecord, Trace};

/// (coroutine_id, role_name) pair.
type CoroInfo = Vec<(usize, String)>;

/// Adapter: wraps a simulator `EffectHandler` (f64-based) for the VM (Value-based).
pub struct VmEffectAdapter<'a> {
    inner: &'a dyn SimEffectHandler,
}

impl<'a> VmEffectAdapter<'a> {
    /// Create a new adapter wrapping a simulator effect handler.
    #[must_use]
    pub fn new(handler: &'a dyn SimEffectHandler) -> Self {
        Self { inner: handler }
    }
}

impl<'a> telltale_vm::effect::EffectHandler for VmEffectAdapter<'a> {
    fn handle_send(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &[Value],
    ) -> Result<Value, String> {
        let f64_state = values_to_f64s(state);
        let payload = self.inner.handle_send(role, partner, label, &f64_state)?;
        Ok(Value::Json(payload))
    }

    fn handle_recv(
        &self,
        role: &str,
        partner: &str,
        label: &str,
        state: &mut Vec<Value>,
        payload: &Value,
    ) -> Result<(), String> {
        let mut f64_state = values_to_f64s(state);
        let json_payload = match payload {
            Value::Json(v) => v.clone(),
            _ => serde_json::Value::Null,
        };
        self.inner
            .handle_recv(role, partner, label, &mut f64_state, &json_payload)?;
        for (i, &v) in f64_state.iter().enumerate() {
            if i + 2 < state.len() {
                state[i + 2] = Value::Real(v);
            }
        }
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
            .ok_or_else(|| "no labels available".into())
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> Result<(), String> {
        let mut f64_state = values_to_f64s(state);
        self.inner.step(role, &mut f64_state)?;
        for (i, &v) in f64_state.iter().enumerate() {
            if i + 2 < state.len() {
                state[i + 2] = Value::Real(v);
            }
        }
        Ok(())
    }
}

/// Convert Value registers to f64 state vector.
fn values_to_f64s(values: &[Value]) -> Vec<f64> {
    values
        .iter()
        .filter_map(|v| match v {
            Value::Real(r) => Some(*r),
            #[allow(clippy::as_conversions)]
            Value::Int(i) => Some(*i as f64),
            _ => None,
        })
        .collect()
}

/// Convert f64 state vector to Value registers.
fn f64s_to_values(state: &[f64]) -> Vec<Value> {
    state.iter().map(|&v| Value::Real(v)).collect()
}

/// Count active (Send/Recv) nodes per role in one Mu body traversal.
fn active_per_role(lt: &LocalTypeR) -> usize {
    match lt {
        LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
            1 + branches
                .first()
                .map(|(_, _, cont)| active_per_role(cont))
                .unwrap_or(0)
        }
        LocalTypeR::Mu { body, .. } => active_per_role(body),
        LocalTypeR::Var(_) | LocalTypeR::End => 0,
    }
}

/// Record state for all roles in a coroutine set.
fn record_all_roles(vm: &VM, coro_info: &CoroInfo, step: usize, trace: &mut Trace) {
    for (coro_id, role) in coro_info {
        if let Some(coro) = vm.coroutine(*coro_id) {
            trace.record(StepRecord {
                step,
                role: role.clone(),
                state: values_to_f64s(&coro.regs[2..]),
            });
        }
    }
}

/// Initialize coroutine registers from f64 state vectors.
fn init_coro_regs(vm: &mut VM, coro_info: &CoroInfo, initial_states: &HashMap<String, Vec<f64>>) {
    for (coro_id, role) in coro_info {
        if let Some(init) = initial_states.get(role) {
            if let Some(coro) = vm.coroutine_mut(*coro_id) {
                let vals = f64s_to_values(init);
                for (i, v) in vals.into_iter().enumerate() {
                    if i + 2 < coro.regs.len() {
                        coro.regs[i + 2] = v;
                    }
                }
            }
        }
    }
}

/// A choreography specification for concurrent execution.
pub struct ChoreographySpec {
    /// Local types per role.
    pub local_types: BTreeMap<String, LocalTypeR>,
    /// Global type.
    pub global_type: GlobalType,
    /// Initial state vectors per role.
    pub initial_states: HashMap<String, Vec<f64>>,
}

/// Run multiple choreographies concurrently on a single VM instance.
///
/// Each choreography gets its own session namespace. Returns one trace per
/// choreography, indexed in the same order as the input specs.
///
/// # Errors
///
/// Returns an error string if loading or execution fails.
#[allow(clippy::cognitive_complexity)]
pub fn run_vm_concurrent(
    specs: &[ChoreographySpec],
    steps: usize,
    handler: &dyn SimEffectHandler,
) -> Result<Vec<Trace>, String> {
    let mut vm = VM::new(VMConfig::default());
    let adapter = VmEffectAdapter { inner: handler };

    let mut session_infos: Vec<(usize, CoroInfo, usize)> = Vec::new();

    for spec in specs {
        let image = CodeImage::from_local_types(&spec.local_types, &spec.global_type);
        let sid = vm
            .load_choreography(&image)
            .map_err(|e| format!("load error: {e}"))?;

        let coros = vm.session_coroutines(sid);
        let coro_info: CoroInfo = coros.iter().map(|c| (c.id, c.role.clone())).collect();
        let num_roles = coro_info.len();

        init_coro_regs(&mut vm, &coro_info, &spec.initial_states);
        session_infos.push((sid, coro_info, num_roles));
    }

    // Coroutine ID → session index.
    let mut coro_to_session: HashMap<usize, usize> = HashMap::new();
    for (session_idx, (_sid, coro_info, _)) in session_infos.iter().enumerate() {
        for (coro_id, _) in coro_info {
            coro_to_session.insert(*coro_id, session_idx);
        }
    }

    let per_session_apr: Vec<usize> = specs
        .iter()
        .map(|s| {
            s.local_types
                .values()
                .next()
                .map(active_per_role)
                .unwrap_or(0)
        })
        .collect();

    let total_roles: usize = session_infos.iter().map(|(_, _, n)| *n).sum();
    let max_vm_steps = steps * total_roles * 10;
    let mut prev_trace_len = 0;
    let mut per_session_invokes: Vec<usize> = vec![0; specs.len()];
    let mut per_session_active: Vec<usize> = vec![0; specs.len()];
    let mut per_session_step: Vec<usize> = vec![0; specs.len()];
    let mut traces: Vec<Trace> = (0..specs.len()).map(|_| Trace::new()).collect();

    // Record initial state (step 0 = Mu step).
    for (si, (_sid, coro_info, _)) in session_infos.iter().enumerate() {
        if steps > 0 {
            record_all_roles(&vm, coro_info, 0, &mut traces[si]);
            per_session_step[si] = 1;
        }
    }

    for _ in 0..max_vm_steps {
        if per_session_step.iter().all(|&s| s >= steps) {
            break;
        }

        match vm.step(&adapter) {
            Ok(StepResult::AllDone | StepResult::Stuck) => break,
            Ok(StepResult::Continue) => {}
            Err(e) => return Err(format!("vm error: {e}")),
        }

        let invoked_sessions: Vec<usize> = {
            let current_trace = vm.trace();
            let result: Vec<usize> = current_trace[prev_trace_len..]
                .iter()
                .filter_map(|event| match event {
                    ObsEvent::Invoked { coro_id, .. } => {
                        coro_to_session.get(coro_id).copied()
                    }
                    _ => None,
                })
                .collect();
            prev_trace_len = current_trace.len();
            result
        };

        for si in invoked_sessions {
            per_session_invokes[si] += 1;
            let (_sid, coro_info, num_roles) = &session_infos[si];

            while per_session_invokes[si] >= *num_roles && per_session_step[si] < steps {
                per_session_invokes[si] -= *num_roles;
                record_all_roles(&vm, coro_info, per_session_step[si], &mut traces[si]);
                per_session_step[si] += 1;
                per_session_active[si] += 1;

                if per_session_active[si] >= per_session_apr[si]
                    && per_session_step[si] < steps
                {
                    per_session_active[si] = 0;
                    record_all_roles(&vm, coro_info, per_session_step[si], &mut traces[si]);
                    per_session_step[si] += 1;
                }
            }
        }
    }

    // Fall back to final state if no intermediate records.
    for (i, (_sid, coro_info, _)) in session_infos.iter().enumerate() {
        if traces[i].records.is_empty() {
            record_all_roles(&vm, coro_info, steps.saturating_sub(1), &mut traces[i]);
        }
    }

    Ok(traces)
}

/// Run a choreography through the VM and return a simulator-compatible trace.
///
/// The compiler emits `Invoke` after every Send/Recv. The scheduler has N
/// active steps + 1 Mu step per round. Every `num_roles` Invoked events
/// = 1 active scheduler step. After N active steps, record 1 Mu step.
///
/// # Errors
///
/// Returns an error string if the VM execution fails.
pub fn run_vm(
    local_types: &BTreeMap<String, LocalTypeR>,
    global_type: &GlobalType,
    initial_states: &HashMap<String, Vec<f64>>,
    steps: usize,
    handler: &dyn SimEffectHandler,
) -> Result<Trace, String> {
    let image = CodeImage::from_local_types(local_types, global_type);

    let mut vm = VM::new(VMConfig::default());
    let sid = vm
        .load_choreography(&image)
        .map_err(|e| format!("load error: {e}"))?;

    let coros = vm.session_coroutines(sid);
    let coro_info: CoroInfo = coros.iter().map(|c| (c.id, c.role.clone())).collect();
    let num_roles = coro_info.len();

    init_coro_regs(&mut vm, &coro_info, initial_states);

    let adapter = VmEffectAdapter { inner: handler };
    let mut trace = Trace::new();

    let apr = coro_info
        .first()
        .map(|(_, role)| {
            local_types
                .get(role)
                .map(active_per_role)
                .unwrap_or(0)
        })
        .unwrap_or(0);

    let max_vm_steps = steps * num_roles * 10;
    let mut prev_trace_len = 0;
    let mut invoke_count: usize = 0;
    let mut active_count: usize = 0;
    let mut step_idx: usize = 0;

    // Record initial state (step 0 = Mu step).
    if steps > 0 {
        record_all_roles(&vm, &coro_info, 0, &mut trace);
        step_idx = 1;
    }

    for _ in 0..max_vm_steps {
        if step_idx >= steps {
            break;
        }

        match vm.step(&adapter) {
            Ok(StepResult::AllDone | StepResult::Stuck) => break,
            Ok(StepResult::Continue) => {}
            Err(e) => return Err(format!("vm error: {e}")),
        }

        let current_trace = vm.trace();
        let new_invokes = current_trace[prev_trace_len..]
            .iter()
            .filter(|e| matches!(e, ObsEvent::Invoked { .. }))
            .count();
        prev_trace_len = current_trace.len();

        invoke_count += new_invokes;

        while invoke_count >= num_roles && step_idx < steps {
            invoke_count -= num_roles;
            record_all_roles(&vm, &coro_info, step_idx, &mut trace);
            step_idx += 1;
            active_count += 1;

            if active_count >= apr && step_idx < steps {
                active_count = 0;
                record_all_roles(&vm, &coro_info, step_idx, &mut trace);
                step_idx += 1;
            }
        }
    }

    if trace.records.is_empty() {
        record_all_roles(&vm, &coro_info, steps.saturating_sub(1), &mut trace);
    }

    Ok(trace)
}
