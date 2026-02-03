//! Online property monitoring for simulation runs.

use std::collections::{BTreeMap, VecDeque};

use telltale_types::LocalTypeR;
use telltale_vm::coroutine::{CoroStatus, Coroutine};
use telltale_vm::instr::Endpoint;
use telltale_vm::session::{SessionId, SessionStore};
use telltale_vm::vm::ObsEvent;

use crate::value_conv::registers_to_f64s;

const TOLERANCE: f64 = 1e-8;

/// Property check context (read-only).
pub struct PropertyContext<'a> {
    /// Current simulation tick.
    pub tick: u64,
    /// Observable event trace from the VM.
    pub trace: &'a [ObsEvent],
    /// Session store for buffer and type state inspection.
    pub sessions: &'a SessionStore,
    /// Coroutine list for register inspection.
    pub coroutines: &'a [Coroutine],
}

/// Built-in properties supported by the monitor.
#[derive(Debug, Clone)]
pub enum Property {
    /// No coroutines have faulted.
    NoFaults,
    /// All coroutine states remain on the probability simplex.
    Simplex,
    /// Every send is received within a bounded number of ticks.
    SendRecvLiveness {
        /// Session to monitor.
        sid: SessionId,
        /// Maximum ticks between send and receive.
        bound: usize,
    },
    /// Session type depth monotonically decreases.
    TypeMonotonicity {
        /// Session to monitor.
        sid: SessionId,
    },
    /// Buffer occupancy stays below a maximum.
    BufferBound {
        /// Session to monitor.
        sid: SessionId,
        /// Maximum buffer size.
        max: usize,
    },
    /// Custom liveness property with precondition and goal predicates.
    Liveness {
        /// Property name for reporting.
        name: String,
        /// Predicate that starts the liveness window.
        precondition: Predicate,
        /// Predicate that must become true within bound.
        goal: Predicate,
        /// Maximum steps to reach goal after precondition.
        bound: usize,
    },
}

impl Property {
    /// Returns the property name for reporting.
    #[must_use]
    pub fn name(&self) -> String {
        match self {
            Self::NoFaults => "no_faults".into(),
            Self::Simplex => "simplex".into(),
            Self::SendRecvLiveness { sid, .. } => format!("send_recv_liveness[{sid}]"),
            Self::TypeMonotonicity { sid } => format!("type_monotonicity[{sid}]"),
            Self::BufferBound { sid, max } => format!("buffer_bound[{sid},{max}]"),
            Self::Liveness { name, .. } => name.clone(),
        }
    }
}

/// Predicate for liveness properties.
#[derive(Debug, Clone)]
pub enum Predicate {
    /// A built-in predicate like no_faults or simplex.
    BuiltIn(BuiltInPredicate),
    /// Compare current tick against a threshold.
    TickCmp {
        /// Comparison operator.
        op: CmpOp,
        /// Right-hand side value.
        rhs: u64,
    },
    /// Compare distance to equilibrium against a threshold.
    DistanceToEquilibriumCmp {
        /// Comparison operator.
        op: CmpOp,
        /// Right-hand side value.
        rhs: f64,
    },
}

/// Built-in predicates for property evaluation.
#[derive(Debug, Clone)]
pub enum BuiltInPredicate {
    /// True when no coroutines have faulted.
    NoFaults,
    /// True when all states remain on the probability simplex.
    Simplex,
}

/// Comparison operators for predicate evaluation.
#[derive(Debug, Clone, Copy)]
pub enum CmpOp {
    /// Less than.
    Lt,
    /// Less than or equal.
    Lte,
    /// Greater than.
    Gt,
    /// Greater than or equal.
    Gte,
    /// Equal.
    Eq,
}

impl Predicate {
    /// Evaluates the predicate against the current context.
    #[must_use]
    pub fn eval(&self, ctx: &PropertyContext) -> bool {
        match self {
            Self::BuiltIn(b) => match b {
                BuiltInPredicate::NoFaults => check_no_faults(ctx),
                BuiltInPredicate::Simplex => check_simplex(ctx),
            },
            Self::TickCmp { op, rhs } => match op {
                CmpOp::Lt => ctx.tick < *rhs,
                CmpOp::Lte => ctx.tick <= *rhs,
                CmpOp::Gt => ctx.tick > *rhs,
                CmpOp::Gte => ctx.tick >= *rhs,
                CmpOp::Eq => ctx.tick == *rhs,
            },
            Self::DistanceToEquilibriumCmp { op, rhs } => {
                let Some(dist) = distance_to_equilibrium(ctx) else {
                    return false;
                };
                match op {
                    CmpOp::Lt => dist < *rhs,
                    CmpOp::Lte => dist <= *rhs,
                    CmpOp::Gt => dist > *rhs,
                    CmpOp::Gte => dist >= *rhs,
                    CmpOp::Eq => (dist - *rhs).abs() < TOLERANCE,
                }
            }
        }
    }
}

/// Parse a simple predicate expression.
///
/// Supported forms:
/// - `no_faults`
/// - `simplex`
/// - `tick < N`, `tick <= N`, `tick > N`, `tick >= N`, `tick == N`
/// - `distance_to_equilibrium < X` (compared against uniform equilibrium)
pub fn parse_predicate(s: &str) -> Result<Predicate, String> {
    let expr = s.trim();
    match expr {
        "no_faults" => return Ok(Predicate::BuiltIn(BuiltInPredicate::NoFaults)),
        "simplex" => return Ok(Predicate::BuiltIn(BuiltInPredicate::Simplex)),
        _ => {}
    }

    let ops = [">=", "<=", "==", ">", "<"];
    for op in ops {
        if let Some((lhs, rhs)) = expr.split_once(op) {
            let lhs = lhs.trim();
            let rhs = rhs.trim();
            let op = match op {
                ">" => CmpOp::Gt,
                ">=" => CmpOp::Gte,
                "<" => CmpOp::Lt,
                "<=" => CmpOp::Lte,
                "==" => CmpOp::Eq,
                _ => return Err(format!("unsupported operator: {op}")),
            };
            if lhs == "tick" {
                let rhs = rhs
                    .parse::<u64>()
                    .map_err(|_| format!("invalid numeric literal: {rhs}"))?;
                return Ok(Predicate::TickCmp { op, rhs });
            }
            if lhs == "distance_to_equilibrium" {
                let rhs = rhs
                    .parse::<f64>()
                    .map_err(|_| format!("invalid numeric literal: {rhs}"))?;
                return Ok(Predicate::DistanceToEquilibriumCmp { op, rhs });
            }
            return Err(format!("unsupported predicate lhs: {lhs}"));
        }
    }

    Err(format!("unsupported predicate: {expr}"))
}

/// Property violation record.
#[derive(Debug, Clone)]
pub struct PropertyViolation {
    /// Name of the violated property.
    pub property_name: String,
    /// Simulation tick when the violation occurred.
    pub tick: u64,
    /// Human-readable violation description.
    pub details: String,
}

struct LivenessTracking {
    precondition_tick: Option<u64>,
    steps_since_precondition: usize,
}

struct SendRecvTracking {
    pending_sends: VecDeque<u64>,
}

struct TypeMonotonicityTracking {
    last_depths: BTreeMap<Endpoint, usize>,
}

enum PropertyState {
    Invariant {
        violated: bool,
    },
    Liveness {
        violated: bool,
        tracking: LivenessTracking,
    },
    SendRecv {
        violated: bool,
        tracking: SendRecvTracking,
    },
    TypeMonotonicity {
        violated: bool,
        tracking: TypeMonotonicityTracking,
    },
}

/// Online property monitor. Hooks into the VM step loop.
pub struct PropertyMonitor {
    properties: Vec<Property>,
    states: Vec<PropertyState>,
    violations: Vec<PropertyViolation>,
    last_trace_len: usize,
}

impl PropertyMonitor {
    /// Create a new monitor for a set of properties.
    #[must_use]
    pub fn new(properties: Vec<Property>) -> Self {
        let states = properties
            .iter()
            .map(|p| match p {
                Property::SendRecvLiveness { .. } => PropertyState::SendRecv {
                    violated: false,
                    tracking: SendRecvTracking {
                        pending_sends: VecDeque::new(),
                    },
                },
                Property::TypeMonotonicity { .. } => PropertyState::TypeMonotonicity {
                    violated: false,
                    tracking: TypeMonotonicityTracking {
                        last_depths: BTreeMap::new(),
                    },
                },
                Property::Liveness { .. } => PropertyState::Liveness {
                    violated: false,
                    tracking: LivenessTracking {
                        precondition_tick: None,
                        steps_since_precondition: 0,
                    },
                },
                _ => PropertyState::Invariant { violated: false },
            })
            .collect();

        Self {
            properties,
            states,
            violations: Vec::new(),
            last_trace_len: 0,
        }
    }

    /// Access recorded violations.
    #[must_use]
    pub fn violations(&self) -> &[PropertyViolation] {
        &self.violations
    }

    /// Check all properties against the current VM context.
    pub fn check(&mut self, ctx: &PropertyContext<'_>) {
        let new_events = ctx.trace.get(self.last_trace_len..).unwrap_or(&[]);

        for (idx, prop) in self.properties.iter().enumerate() {
            match (&prop, &mut self.states[idx]) {
                (Property::NoFaults, PropertyState::Invariant { violated }) => {
                    if !*violated && !check_no_faults(ctx) {
                        *violated = true;
                        self.violations.push(PropertyViolation {
                            property_name: prop.name(),
                            tick: ctx.tick,
                            details: "faulted coroutine detected".into(),
                        });
                    }
                }
                (Property::Simplex, PropertyState::Invariant { violated }) => {
                    if !*violated && !check_simplex(ctx) {
                        *violated = true;
                        self.violations.push(PropertyViolation {
                            property_name: prop.name(),
                            tick: ctx.tick,
                            details: "state left simplex".into(),
                        });
                    }
                }
                (Property::BufferBound { sid, max }, PropertyState::Invariant { violated }) => {
                    if *violated {
                        continue;
                    }
                    if let Some(session) = ctx.sessions.get(*sid) {
                        let too_large = session.buffers.values().any(|buf| buf.len() > *max);
                        if too_large {
                            *violated = true;
                            self.violations.push(PropertyViolation {
                                property_name: prop.name(),
                                tick: ctx.tick,
                                details: format!("buffer size exceeded {max}"),
                            });
                        }
                    }
                }
                (
                    Property::SendRecvLiveness { sid, bound },
                    PropertyState::SendRecv { violated, tracking },
                ) => {
                    if *violated {
                        continue;
                    }
                    for event in new_events {
                        match event {
                            ObsEvent::Sent { session, tick, .. } if session == sid => {
                                tracking.pending_sends.push_back(*tick);
                            }
                            ObsEvent::Received { session, .. } if session == sid => {
                                tracking.pending_sends.pop_front();
                            }
                            _ => {}
                        }
                    }
                    if let Some(&send_tick) = tracking.pending_sends.front() {
                        if ctx.tick.saturating_sub(send_tick) > *bound as u64 {
                            *violated = true;
                            self.violations.push(PropertyViolation {
                                property_name: prop.name(),
                                tick: ctx.tick,
                                details: format!(
                                    "send at tick {send_tick} not received within {bound} ticks"
                                ),
                            });
                        }
                    }
                }
                (
                    Property::TypeMonotonicity { sid },
                    PropertyState::TypeMonotonicity { violated, tracking },
                ) => {
                    if *violated {
                        continue;
                    }
                    if let Some(session) = ctx.sessions.get(*sid) {
                        for (ep, entry) in &session.local_types {
                            if contains_recursion(&entry.original) {
                                continue;
                            }
                            let depth = type_depth(&entry.current);
                            if let Some(prev) = tracking.last_depths.get(ep) {
                                if depth > *prev {
                                    *violated = true;
                                    self.violations.push(PropertyViolation {
                                        property_name: prop.name(),
                                        tick: ctx.tick,
                                        details: format!(
                                            "type depth increased for {}:{} ({prev} -> {depth})",
                                            ep.sid, ep.role
                                        ),
                                    });
                                    break;
                                }
                            }
                            tracking.last_depths.insert(ep.clone(), depth);
                        }
                    }
                }
                (
                    Property::Liveness {
                        precondition,
                        goal,
                        bound,
                        ..
                    },
                    PropertyState::Liveness { violated, tracking },
                ) => {
                    if *violated {
                        continue;
                    }
                    let precond = precondition.eval(ctx);
                    if tracking.precondition_tick.is_none() && precond {
                        tracking.precondition_tick = Some(ctx.tick);
                        tracking.steps_since_precondition = 0;
                    }
                    if let Some(_) = tracking.precondition_tick {
                        if goal.eval(ctx) {
                            tracking.precondition_tick = None;
                            tracking.steps_since_precondition = 0;
                        } else {
                            tracking.steps_since_precondition += 1;
                            if tracking.steps_since_precondition > *bound {
                                *violated = true;
                                self.violations.push(PropertyViolation {
                                    property_name: prop.name(),
                                    tick: ctx.tick,
                                    details: format!(
                                        "goal not reached within {bound} steps after precondition"
                                    ),
                                });
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        self.last_trace_len = ctx.trace.len();
    }
}

/// Every send is eventually received (within the session).
#[must_use]
pub fn send_recv_liveness(sid: SessionId, bound: usize) -> Property {
    Property::SendRecvLiveness { sid, bound }
}

/// Type state never regresses (monotonic advancement).
#[must_use]
pub fn type_monotonicity(sid: SessionId) -> Property {
    Property::TypeMonotonicity { sid }
}

/// No session faults.
#[must_use]
pub fn no_faults() -> Property {
    Property::NoFaults
}

/// Buffer occupancy bounded.
#[must_use]
pub fn buffer_bound(sid: SessionId, max: usize) -> Property {
    Property::BufferBound { sid, max }
}

fn check_no_faults(ctx: &PropertyContext<'_>) -> bool {
    ctx.coroutines
        .iter()
        .all(|c| !matches!(c.status, CoroStatus::Faulted(_)))
}

fn check_simplex(ctx: &PropertyContext<'_>) -> bool {
    for coro in ctx.coroutines {
        let vals = registers_to_f64s(&coro.regs);
        if vals.is_empty() {
            continue;
        }
        let sum: f64 = vals.iter().sum();
        if (sum - 1.0).abs() > TOLERANCE {
            return false;
        }
        if vals.iter().any(|v| *v < -TOLERANCE) {
            return false;
        }
    }
    true
}

fn distance_to_equilibrium(ctx: &PropertyContext<'_>) -> Option<f64> {
    let mut max_dist: Option<f64> = None;
    for coro in ctx.coroutines {
        let vals = registers_to_f64s(&coro.regs);
        if vals.is_empty() {
            continue;
        }
        let n = vals.len() as f64;
        let target = 1.0 / n;
        let dist = vals
            .iter()
            .map(|v| (v - target).powi(2))
            .sum::<f64>()
            .sqrt();
        max_dist = Some(max_dist.map_or(dist, |m| m.max(dist)));
    }
    max_dist
}

fn contains_recursion(lt: &LocalTypeR) -> bool {
    match lt {
        LocalTypeR::Mu { body, .. } => contains_recursion(body),
        LocalTypeR::Var(_) => true,
        LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
            branches.iter().any(|(_, _, cont)| contains_recursion(cont))
        }
        LocalTypeR::End => false,
    }
}

fn type_depth(lt: &LocalTypeR) -> usize {
    match lt {
        LocalTypeR::End | LocalTypeR::Var(_) => 0,
        LocalTypeR::Mu { body, .. } => type_depth(body),
        LocalTypeR::Send { branches, .. } | LocalTypeR::Recv { branches, .. } => {
            let max_branch = branches
                .iter()
                .map(|(_, _, cont)| type_depth(cont))
                .max()
                .unwrap_or(0);
            1 + max_branch
        }
    }
}
