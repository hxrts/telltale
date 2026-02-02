//! VM-backed simulation runner.
//!
//! Wraps `telltale-vm` to execute choreographies through the bytecode VM,
//! producing the same `Trace` format as the lightweight scheduler.

use std::collections::{BTreeMap, HashMap};

use telltale_types::{GlobalType, LocalTypeR};
use telltale_vm::coroutine::Value;
use telltale_vm::loader::CodeImage;
use telltale_vm::vm::{VMConfig, VM};

use crate::scheduler::EffectHandler as SimEffectHandler;
use crate::trace::{StepRecord, Trace};

/// Adapter: wraps a simulator `EffectHandler` (f64-based) for the VM (Value-based).
struct VmEffectAdapter<'a> {
    inner: &'a dyn SimEffectHandler,
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
        // Write back f64 values into existing registers (starting at reg 2).
        for (i, &v) in f64_state.iter().enumerate() {
            if i + 2 < state.len() {
                state[i + 2] = Value::Real(v);
            }
        }
        Ok(())
    }

    fn step(&self, role: &str, state: &mut Vec<Value>) -> Result<(), String> {
        let mut f64_state = values_to_f64s(state);
        self.inner.step(role, &mut f64_state)?;
        // Write back f64 values into existing registers (starting at reg 2).
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

/// Run a choreography through the VM and return a simulator-compatible trace.
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

    // Initialize coroutine registers from initial_states.
    let coros = vm.session_coroutines(sid);
    let coro_info: Vec<(usize, String)> = coros.iter().map(|c| (c.id, c.role.clone())).collect();

    for (coro_id, role) in &coro_info {
        if let Some(init) = initial_states.get(role) {
            if let Some(coro) = vm.coroutine_mut(*coro_id) {
                let vals = f64s_to_values(init);
                // Put state values starting at register 2 (0=chan, 1=msg scratch).
                for (i, v) in vals.into_iter().enumerate() {
                    if i + 2 < coro.regs.len() {
                        coro.regs[i + 2] = v;
                    }
                }
            }
        }
    }

    let adapter = VmEffectAdapter { inner: handler };

    // Run the VM for enough steps (each VM step = one instruction, not one protocol tick).
    // A protocol tick involves ~2 instructions per role (send+recv or similar),
    // so we need more VM steps than protocol steps.
    let max_vm_steps = steps * local_types.len() * 10;
    vm.run(&adapter, max_vm_steps)
        .map_err(|e| format!("vm error: {e}"))?;

    // Collect trace: extract final states from coroutine registers.
    let mut trace = Trace::new();
    for (coro_id, role) in &coro_info {
        if let Some(coro) = vm.coroutine(*coro_id) {
            let f64_state = values_to_f64s(&coro.regs[2..]);
            trace.record(StepRecord {
                step: steps.saturating_sub(1),
                role: role.clone(),
                state: f64_state,
            });
        }
    }

    Ok(trace)
}
