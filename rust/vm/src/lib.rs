//! Bytecode VM for choreographic session type protocols.
//!
//! This crate provides a standalone, embeddable virtual machine that executes
//! choreographic protocols projected to local session types. The VM validates
//! every instruction against its session type monitor, ensuring protocol
//! conformance at runtime.
//!
//! # Architecture
//!
//! The VM follows the Lean specification in `lean/Runtime/VM/`:
//! - **Instructions** ([`instr::Instr`]): bytecode ops for send/recv/choice/session lifecycle
//! - **Coroutines** ([`coroutine::Coroutine`]): lightweight execution units, one per role
//! - **Sessions** ([`session::SessionStore`]): manage session lifecycle and namespaces
//! - **Buffers** ([`buffer::BoundedBuffer`]): bounded message channels with backpressure
//! - **Scheduler** ([`scheduler::Scheduler`]): policy-based coroutine scheduling
//! - **Loader** ([`loader`]): dynamic choreography loading with validation
//! - **Compiler** ([`compiler`]): compile `LocalTypeR` to bytecode
//!
//! The VM is the **single execution engine** for simulation and runtime
//! orchestration. Higher-level systems (e.g. `telltale-simulator`) wrap the
//! VM with deterministic middleware for network latency, faults, property
//! monitoring, and checkpointing.
//!
//! **Nested simulation** is supported via [`nested::NestedVMHandler`], which
//! allows a VM coroutine to host an inner VM for distributed or hierarchical
//! simulations.
//!
//! # Effect Handler Contract
//!
//! The VM's [`effect::EffectHandler`] is synchronous, deterministic, and
//! **session-local**. It must not depend on global time or shared mutable
//! state across sessions. This is distinct from the async, typed
//! `telltale_choreography::ChoreoHandler` used by generated choreography code.
//!
//! # Usage
//!
//! ```ignore
//! use telltale_vm::{VM, VMConfig, compiler, loader::CodeImage};
//!
//! let config = VMConfig::default();
//! let mut vm = VM::new(config);
//! let image = CodeImage::from_local_types(&local_types, &global_type);
//! let sid = vm.load_choreography(image, &handler)?;
//! while vm.step(&handler)? {}
//! ```

pub mod architecture;
pub mod backend;
pub mod bridge;
pub mod buffer;
pub mod clock;
pub mod compiler;
pub mod composition;
pub mod coroutine;
pub mod determinism;
pub mod driver;
pub mod effect;
pub mod envelope_diff;
pub mod exec;
pub mod exec_api;
pub mod faults;
pub mod guard;
pub mod identity;
pub mod instr;
pub mod instruction_semantics;
pub mod intern;
pub mod kernel;
pub mod loader;
pub mod nested;
pub mod output_condition;
pub mod persistence;
pub mod runtime_contracts;
pub mod scheduler;
pub mod serialization;
pub mod session;
#[cfg(feature = "multi-thread")]
pub mod threaded;
pub mod trace;
pub mod transfer_semantics;
pub mod verification;
pub mod vm;
#[cfg(target_arch = "wasm32")]
pub mod wasm;

pub use architecture::{
    EngineOwnership, EngineRole, CANONICAL_ENGINE, CROSS_TARGET_CONTRACT, ENGINE_OWNERSHIP,
    EQUIVALENCE_SURFACES,
};
pub use backend::VMBackend;
pub use bridge::{
    EffectGuardBridge, IdentityGuardBridge, IdentityPersistenceBridge, IdentityVerificationBridge,
    PersistenceEffectBridge,
};
pub use clock::SimClock;
pub use composition::{
    ComposedRuntime, CompositionCertificate, CompositionError, DeterminismCapability, MemoryBudget,
    MemoryUsage, ProtocolBundle, SchedulerCapability, TheoremPackCapabilities,
};
pub use coroutine::{CoroStatus, Coroutine, CoroutineState, KnowledgeSet, Value};
pub use determinism::{DeterminismMode, EffectDeterminismTier};
pub use driver::NativeSingleThreadDriver;
#[cfg(feature = "multi-thread")]
pub use driver::NativeThreadedDriver;
pub use effect::{
    CorruptionType, EffectTraceEntry, EffectTraceTape, RecordingEffectHandler, ReplayEffectHandler,
    TopologyPerturbation,
};
pub use envelope_diff::{
    EffectOrderingClass, EnvelopeDiff, EnvelopeDiffArtifactV1, FailureVisibleDiffClass,
    SchedulerPermutationClass, WaveWidthBound,
};
pub use exec_api::{ExecResult, ExecStatus, StepEvent, StepPack};
pub use faults::{classify_fault, fault_code, fault_code_of, FaultClass};
pub use guard::{GuardLayer, InMemoryGuardLayer, LayerId};
pub use identity::{IdentityModel, ParticipantId, SiteId as IdentitySiteId, StaticIdentityModel};
pub use instr::Instr;
pub use intern::{StringId, SymbolTable};
pub use kernel::VMKernel;
pub use nested::NestedVMHandler;
pub use output_condition::{
    verify_output_condition, OutputConditionCheck, OutputConditionHint, OutputConditionMeta,
    OutputConditionPolicy,
};
pub use persistence::{NoopPersistence, PersistenceModel};
pub use runtime_contracts::{
    admit_vm_runtime, determinism_profile_supported, enforce_vm_runtime_gates,
    request_determinism_profile, requires_vm_runtime_contracts, runtime_capability_snapshot,
    DeterminismArtifacts, RuntimeAdmissionResult, RuntimeContracts, RuntimeGateResult,
};
pub use scheduler::{
    CrossLaneHandoff, LaneId as SchedulerLaneId, PriorityPolicy, SchedPolicy, SchedState,
    Scheduler, StepUpdate,
};
pub use serialization::{
    canonical_effect_trace, canonical_replay_fragment_v1, canonical_trace_v1,
    CanonicalReplayFragmentV1, CanonicalTraceV1,
};
pub use session::{decode_edge_json, Edge, HandlerId, SessionId, SessionStore};
#[cfg(feature = "multi-thread")]
pub use threaded::{
    ContentionMetrics, LaneHandoff, LaneId, LaneSchedulerState, LaneSelection, ThreadedVM,
};
pub use trace::{
    normalize_trace, normalize_trace_v1, obs_session, strict_trace, with_tick, NormalizedTraceV1,
    TRACE_NORMALIZATION_SCHEMA_VERSION,
};
pub use transfer_semantics::{decode_transfer_request, move_endpoint_bundle, TransferRequest};
pub use verification::{
    signValue, sign_value, verifySignedValue, verify_signed_value, AuthProof, AuthTree, Commitment,
    DefaultVerificationModel, Hash, HashTag, Nullifier, Signature, SigningKey, VerificationModel,
    VerifyingKey,
};
pub use vm::{
    MonitorMode, Program, RuntimeTuningProfile, SchedStepDebug, ThreadedRoundSemantics, VMConfig,
    VMState, VM,
};
#[cfg(target_arch = "wasm32")]
pub use wasm::WasmVM;
