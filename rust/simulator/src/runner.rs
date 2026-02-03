//! VM-backed simulation runner.
//!
//! Wraps `telltale-vm` to execute choreographies through the bytecode VM,
//! producing the same `Trace` format as the lightweight scheduler.

use std::collections::{BTreeMap, HashMap};

use telltale_types::{GlobalType, LocalTypeR};
use telltale_vm::effect::EffectHandler;
use telltale_vm::loader::CodeImage;
use telltale_vm::vm::{ObsEvent, StepResult, VMConfig, VM};

use crate::checkpoint::CheckpointStore;
use crate::fault::FaultInjector;
use crate::network::NetworkModel;
use crate::property::{PropertyContext, PropertyMonitor, PropertyViolation};
use crate::rng::SimRng;
use crate::scenario::Scenario;
use crate::trace::{StepRecord, Trace};
use crate::value_conv::{f64s_to_values, registers_to_f64s};

/// (coroutine_id, role_name) pair.
type CoroInfo = Vec<(usize, String)>;

// (adapter removed; simulator handlers implement VM EffectHandler directly)

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
                state: registers_to_f64s(&coro.regs),
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
pub fn run_concurrent(
    specs: &[ChoreographySpec],
    steps: usize,
    handler: &dyn EffectHandler,
) -> Result<Vec<Trace>, String> {
    let mut vm = VM::new(VMConfig::default());

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

        match vm.step(handler) {
            Ok(StepResult::AllDone | StepResult::Stuck) => break,
            Ok(StepResult::Continue) => {}
            Err(e) => return Err(format!("vm error: {e}")),
        }

        let invoked_sessions: Vec<usize> = {
            let current_trace = vm.trace();
            let result: Vec<usize> = current_trace[prev_trace_len..]
                .iter()
                .filter_map(|event| match event {
                    ObsEvent::Invoked { coro_id, .. } => coro_to_session.get(coro_id).copied(),
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

                if per_session_active[si] >= per_session_apr[si] && per_session_step[si] < steps {
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
pub fn run(
    local_types: &BTreeMap<String, LocalTypeR>,
    global_type: &GlobalType,
    initial_states: &HashMap<String, Vec<f64>>,
    steps: usize,
    handler: &dyn EffectHandler,
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

    let mut trace = Trace::new();

    let apr = coro_info
        .first()
        .map(|(_, role)| local_types.get(role).map(active_per_role).unwrap_or(0))
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

        match vm.step(handler) {
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

/// Result of a scenario-backed run.
pub struct ScenarioResult {
    /// Execution trace with step records.
    pub trace: Trace,
    /// Property violations detected during execution.
    pub violations: Vec<PropertyViolation>,
}

/// Run a choreography with scenario-defined middleware (faults/network/properties).
///
/// # Errors
///
/// Returns an error string if the VM execution fails.
#[allow(clippy::too_many_lines)]
pub fn run_with_scenario(
    local_types: &BTreeMap<String, LocalTypeR>,
    global_type: &GlobalType,
    initial_states: &HashMap<String, Vec<f64>>,
    scenario: &Scenario,
    handler: &dyn EffectHandler,
) -> Result<ScenarioResult, String> {
    let image = CodeImage::from_local_types(local_types, global_type);
    let mut vm = VM::new(VMConfig::default());
    let sid = vm
        .load_choreography(&image)
        .map_err(|e| format!("load error: {e}"))?;

    let coros = vm.session_coroutines(sid);
    let coro_info: CoroInfo = coros.iter().map(|c| (c.id, c.role.clone())).collect();
    let num_roles = coro_info.len();

    init_coro_regs(&mut vm, &coro_info, initial_states);

    let mut trace = Trace::new();
    let apr = coro_info
        .first()
        .map(|(_, role)| local_types.get(role).map(active_per_role).unwrap_or(0))
        .unwrap_or(0);

    let max_vm_rounds = scenario.steps * num_roles * 10;
    let mut prev_trace_len = 0;
    let mut invoke_count: usize = 0;
    let mut active_count: usize = 0;
    let mut step_idx: usize = 0;

    if scenario.steps > 0 {
        record_all_roles(&vm, &coro_info, 0, &mut trace);
        step_idx = 1;
    }

    let mut rng = SimRng::new(scenario.seed);
    let mut monitor = scenario
        .property_monitor()
        .map_err(|e| format!("properties: {e}"))?
        .unwrap_or_else(|| PropertyMonitor::new(Vec::new()));

    let mut checkpoints = scenario.checkpoint_interval.map(|interval| {
        let dir = std::path::PathBuf::from("artifacts").join(&scenario.name);
        CheckpointStore::with_dir(interval, dir)
    });

    let schedule = scenario
        .fault_schedule()
        .map_err(|e| format!("fault schedule: {e}"))?;
    let fault = FaultInjector::new(handler, schedule, rng.fork());

    let mut fault_only = None;
    let mut network = None;
    if let Some(cfg) = scenario.network_config() {
        network = Some(NetworkModel::new(
            fault,
            cfg,
            rng.fork(),
            vm.clock().tick_duration,
        ));
    } else {
        fault_only = Some(fault);
    }

    for _ in 0..max_vm_rounds {
        if step_idx >= scenario.steps {
            break;
        }

        let next_tick = vm.clock().tick + 1;

        if let Some(net) = &network {
            net.inner().tick(next_tick, vm.trace());
            net.inner().deliver(next_tick, |sid, from, to, val| {
                vm.inject_message(sid, from, to, val)
                    .map_err(|e| e.to_string())
            });
            net.set_tick(next_tick);
            net.deliver(next_tick, |sid, from, to, val| {
                vm.inject_message(sid, from, to, val)
                    .map_err(|e| e.to_string())
            });
            vm.set_paused_roles(&net.inner().crashed_roles());
            match vm.step_round(net, scenario.concurrency) {
                Ok(StepResult::AllDone | StepResult::Stuck) => break,
                Ok(StepResult::Continue) => {}
                Err(e) => return Err(format!("vm error: {e}")),
            }
        } else {
            let fault = fault_only.as_ref().expect("fault injector");
            fault.tick(next_tick, vm.trace());
            fault.deliver(next_tick, |sid, from, to, val| {
                vm.inject_message(sid, from, to, val)
                    .map_err(|e| e.to_string())
            });
            vm.set_paused_roles(&fault.crashed_roles());
            match vm.step_round(fault, scenario.concurrency) {
                Ok(StepResult::AllDone | StepResult::Stuck) => break,
                Ok(StepResult::Continue) => {}
                Err(e) => return Err(format!("vm error: {e}")),
            }
        }

        let current_trace = vm.trace();
        let new_invokes = current_trace[prev_trace_len..]
            .iter()
            .filter(|e| matches!(e, ObsEvent::Invoked { .. }))
            .count();
        prev_trace_len = current_trace.len();

        invoke_count += new_invokes;

        while invoke_count >= num_roles && step_idx < scenario.steps {
            invoke_count -= num_roles;
            record_all_roles(&vm, &coro_info, step_idx, &mut trace);
            step_idx += 1;
            active_count += 1;

            if active_count >= apr && step_idx < scenario.steps {
                active_count = 0;
                record_all_roles(&vm, &coro_info, step_idx, &mut trace);
                step_idx += 1;
            }
        }

        let ctx = PropertyContext {
            tick: vm.clock().tick,
            trace: vm.trace(),
            sessions: vm.sessions(),
            coroutines: vm.coroutines(),
        };
        monitor.check(&ctx);
        if let Some(store) = &mut checkpoints {
            store.maybe_checkpoint(vm.clock().tick, &vm);
        }
    }

    if trace.records.is_empty() {
        record_all_roles(
            &vm,
            &coro_info,
            scenario.steps.saturating_sub(1),
            &mut trace,
        );
    }

    Ok(ScenarioResult {
        trace,
        violations: monitor.violations().to_vec(),
    })
}
